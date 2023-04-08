use std::fmt;
use std::rc::Rc;
use crate::common::error::Res;
use crate::common::row::Row;
use crate::core::trees::TreeNode;
use crate::core::types::{Field, Type};
use crate::exec::attr::{Attribute, reference, from_fields};
use crate::exec::catalog;
use crate::storage::btree::BTreeIter;
use crate::storage::txn::{TransactionRef, next_object_id};

pub fn insert(info: Rc<catalog::TableInfo>, project: Rc<Vec<usize>>, query: Plan) -> Res<Plan> {
  Ok(
    Plan::Insert {
      output: Rc::new(
        vec![reference(&Field::new("NUM_INSERTED", Type::BIGINT, false)?, 0)?]
      ),
      info: info,
      project: project,
      query: vec![query],
    }
  )
}

pub fn project(output: Rc<Vec<Attribute>>, child: Plan) -> Res<Plan> {
  Ok(Plan::Project { output, child: vec![child] })
}

pub fn table_scan(info: Rc<catalog::TableInfo>) -> Res<Plan> {
  Ok(
    Plan::TableScan {
      output: Rc::new(from_fields(info.table_fields())?),
      info: info,
    }
  )
}

// Physical plan.
#[derive(Clone, Debug, PartialEq)]
pub enum Plan {
  // TODO: Add assertion on the length of the project vector
  // project.len() == 0 || fields.len() == project.len()
  // TODO: Add assertion on the query having non-zero attributes.
  Insert {
    output: Rc<Vec<Attribute>>, // attributes for insert, not the query
    info: Rc<catalog::TableInfo>,
    // Projection map: vector that contains field positions to insert into.
    // If the vector is empty, then no projection is provided.
    project: Rc<Vec<usize>>,
    query: Vec<Plan>
  },
  Limit {
    limit: usize,
    child: Vec<Plan>,
  },
  Project {
    output: Rc<Vec<Attribute>>,
    child: Vec<Plan>,
  },
  TableScan {
    output: Rc<Vec<Attribute>>, // derived from the table info
    info: Rc<catalog::TableInfo>
  },
}

impl Plan {
  #[inline]
  pub fn output(&self) -> &[Attribute] {
    match self {
      Plan::Insert { output, .. } => output,
      Plan::Limit { child, .. } => child[0].output(),
      Plan::Project { output, .. } => output,
      Plan::TableScan { output, .. } => output,
    }
  }

  #[inline]
  pub fn execute(&self, txn: &TransactionRef) -> Res<PlanIter> {
    match self {
      Plan::Insert { info, project, query, .. } => {
        let child = &query[0];
        let output = child.output();
        let fields = info.table_fields().get();

        // TODO: Revisit the error messages and convert them.

        // Validation.
        if project.len() == 0 {
          // Projection vector is empty, we need to check all of the fields in the table.
          if output.len() > fields.len() {
            return Err(internal_err!("Insert has more expressions than target columns"))
          } else {
            // For the output fields, check if data type matches.
            for i in 0..output.len() {
              if &output[i].data_type() != &fields[i].data_type() {
                return Err(internal_err!("Data type mismatch"));
              }
            }
            // For the remaining fields, check if we can insert nulls.
            for i in output.len()..fields.len() {
              if !fields[i].nullable() {
                return Err(internal_err!("Non-null constraint violation"));
              }
            }
          }
        } else {
          // Projection vector exists, we only need to check projection fields.
          if output.len() > project.len() {
            return Err(internal_err!("Insert has more expressions than target columns"))
          } else if output.len() < project.len() {
            return Err(internal_err!("Insert has more target columns than expressions"))
          } else {
            let mut null_check_vector = vec![false; fields.len()];
            for i in 0..output.len() {
              let ord = project[i];
              null_check_vector[ord] = true;
              if &output[i].data_type() != &fields[ord].data_type() {
                return Err(internal_err!("Data type mismatch"));
              }
            }
            // Verify that the remaining columns are nullable.
            for i in 0..fields.len() {
              if !null_check_vector[i] && !fields[i].nullable() {
                return Err(internal_err!("Non-null constraint violation"));
              }
            }
          }
        }

        // Whether or not we can directly write a row without allocating a new one.
        let zero_copy =
          // Output must match the schema.
          project.len() == 0 && output.len() == fields.len() ||
          // Output must match the projection and projection must insert in the order of schema.
          project.len() == output.len() && project.iter().enumerate().filter(|(i, p)| i != *p).count() == 0;

        // At this point, the input data is valid and matches the table schema.
        let mut set = match catalog::get_table_data(&txn, info) {
          Some(set) => set,
          None => catalog::create_table_data(&txn, info)?,
        };

        let mut num_rows = 0;
        let mut iter = child.execute(&txn)?;

        if zero_copy {
          while let Some(row) = iter.next() {
            // TODO: Improve nullability check.
            for i in 0..fields.len() {
              if row.is_null(i) && !fields[i].nullable() {
                return Err(internal_err!("Non-null constraint violation"));
              }
            }
            let row_id = next_object_id(&txn);
            set.put(&u64_u8!(row_id), &row.to_vec());
            num_rows += 1;
          }
        } else if project.len() == 0 {
          // TODO: Check if we can combine the last two if branches (with project and without).
          while let Some(row) = iter.next() {
            let mut out_row = Row::new(fields.len());
            for i in 0..output.len() {
              let attr = &output[i];
              attr.eval(&row, &mut out_row, i, fields[i].nullable())?;
            }
            let row_id = next_object_id(&txn);
            set.put(&u64_u8!(row_id), &out_row.to_vec());
            num_rows += 1;
          }
        } else {
          while let Some(row) = iter.next() {
            let mut out_row = Row::new(fields.len());
            for i in 0..output.len() {
              let ord = project[i];
              let attr = &output[i];
              attr.eval(&row, &mut out_row, ord, fields[ord].nullable())?;
            }
            let row_id = next_object_id(&txn);
            set.put(&u64_u8!(row_id), &out_row.to_vec());
            num_rows += 1;
          }
        }

        // Construct the output of the command.
        let mut row = Row::new(1);
        row.set_i64(0, num_rows as i64);
        Ok(PlanIter::from_vec(vec![row]))
      },
      Plan::Limit { limit, child } => {
        Ok(PlanIter::limit(*limit, child[0].execute(&txn)?))
      },
      Plan::Project { .. } => {
        // select a, b, c from (select a, b from table)
        // Check if the outputs can be extracted from the child's output.
        unimplemented!()
      },
      Plan::TableScan { ref info, .. } => {
        match catalog::get_table_data(&txn, info) {
          Some(mut set) => {
            let num_fields = info.table_fields().len();
            let iter = set.list(None, None);
            Ok(PlanIter::TableScanIter { num_fields, iter })
          },
          None => Ok(PlanIter::empty()),
        }
      },
    }
  }
}

impl TreeNode<Plan> for Plan {
  #[inline]
  fn display(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Plan::Insert { .. } => write!(f, "Insert"),
      Plan::Limit { .. } => write!(f, "Limit"),
      Plan::Project { .. } => write!(f, "Project"),
      Plan::TableScan { .. } => write!(f, "TableScan"),
    }
  }

  #[inline]
  fn as_ref(&self) -> &Plan {
    self
  }

  #[inline]
  fn children(&self) -> &[Plan] {
    match self {
      Plan::Insert { query, .. } => query,
      Plan::Limit { child, .. } => child,
      Plan::Project { child, .. } => child,
      Plan::TableScan { .. } => &[],
    }
  }

  #[inline]
  fn copy(&self, children: Vec<Plan>) -> Plan {
    match self {
      Plan::Insert { output, info, project, .. } => {
        // TODO: improve assertion message.
        assert_eq!(children.len(), 1, "Insert: {:?}", children);
        Plan::Insert {
          output: output.clone(),
          info: info.clone(),
          project: project.clone(),
          query: children
        }
      },
      Plan::Limit { limit, .. } => {
        assert_eq!(children.len(), 1, "Limit: {:?}", children);
        Plan::Limit { limit: *limit, child: children }
      },
      Plan::Project { output, .. } => {
        // TODO: improve assertion message.
        assert_eq!(children.len(), 1, "Project: {:?}", children);
        Plan::Project {
          output: output.clone(),
          child: children
        }
      },
      Plan::TableScan { output, info } => {
        Plan::TableScan {
          output: output.clone(),
          info: info.clone()
        }
      },
    }
  }
}

pub enum PlanIter {
  EmptyIter,
  FromVecIter { rows: Vec<Row> },
  LimitIter { limit: usize, parent: Box<PlanIter> },
  TableScanIter { num_fields: usize, iter: BTreeIter },
}

impl PlanIter {
  // Returns an empty iterator.
  #[inline]
  fn empty() -> Self {
    Self::EmptyIter
  }

  // Returns an iterator from the vector of rows.
  #[inline]
  fn from_vec(mut rows: Vec<Row>) -> Self {
    rows.reverse();
    Self::FromVecIter { rows: rows }
  }

  // Returns an iterator that is limited to `limit` rows from the `parent`.
  #[inline]
  fn limit(limit: usize, plan: PlanIter) -> Self {
    Self::LimitIter { limit: limit, parent: Box::new(plan) }
  }
}

impl Iterator for PlanIter {
  type Item = Row;

  fn next(&mut self) -> Option<Self::Item> {
    match self {
      PlanIter::EmptyIter => None,
      PlanIter::FromVecIter { rows } => rows.pop(),
      PlanIter::LimitIter { ref mut limit, parent } => {
        if *limit > 0 {
          *limit -= 1;
          parent.next()
        } else {
          None
        }
      },
      PlanIter::TableScanIter { num_fields, iter } => {
        match iter.next() {
          Some((_key, data)) => Some(Row::from_buf(*num_fields, data)),
          None => None,
        }
      },
    }
  }
}

#[cfg(test)]
pub mod tests {
  use super::*;

  #[test]
  fn test_plan_iter_empty() {
    let mut iter = PlanIter::empty();
    assert!(iter.next().is_none());
  }

  #[test]
  fn test_plan_iter_from_vec() {
    let mut iter = PlanIter::from_vec(vec![Row::new(1)]);
    assert_eq!(iter.next().unwrap().num_fields(), 1);

    let mut iter = PlanIter::from_vec(
      vec![
        Row::new(1),
        Row::new(2),
        Row::new(3),
      ]
    );
    assert_eq!(iter.next().unwrap().num_fields(), 1);
    assert_eq!(iter.next().unwrap().num_fields(), 2);
    assert_eq!(iter.next().unwrap().num_fields(), 3);
  }

  #[test]
  fn test_plan_iter_limit() {
    // Limit is greater than the length of the iterator.
    let iter = PlanIter::from_vec(
      vec![
        Row::new(1),
        Row::new(1),
        Row::new(1),
      ]
    );
    let mut limit_iter = PlanIter::limit(1, iter);
    assert!(limit_iter.next().is_some());
    assert!(limit_iter.next().is_none());

    // Limit is smaller than the length of the iterator.
    let iter = PlanIter::from_vec(vec![Row::new(1)]);
    let mut limit_iter = PlanIter::limit(10, iter);
    assert!(limit_iter.next().is_some());
    for _ in 0..10 {
      assert!(limit_iter.next().is_none());
    }

    // Limit on an empty iterator.
    let iter = PlanIter::from_vec(Vec::new());
    let mut limit_iter = PlanIter::limit(5, iter);
    for _ in 0..5 {
      assert!(limit_iter.next().is_none());
    }
  }
}
