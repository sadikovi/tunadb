//! Parser to convert a SQL string into list of plans.

use std::rc::Rc;
use crate::common::error::{Error, Res};
use crate::core::types::{Field, Fields, Type};
use crate::exec::plan::{Expression, Plan, TableIdentifier};
use crate::exec::scanner::{Scanner, Token, TokenType};

// Parser for the SQL queries.
pub struct Parser<'a> {
  sql: &'a str,
  scanner: Scanner<'a>,
  current: Token,
}

impl<'a> Parser<'a> {
  // Returns true if there are no more tokens left.
  #[inline]
  fn done(&self) -> bool {
    self.current.token_type() == TokenType::EOF
  }

  // Returns true if the current token has the provided type.
  #[inline]
  fn check(&self, tpe: TokenType) -> bool {
    self.current.token_type() == tpe
  }

  // Advances the parser to the next token.
  // Only returns an error if an error token was encountered.
  #[inline]
  fn advance(&mut self) -> Res<()> {
    self.current = self.scanner.next_token();
    // Check if we could not parse the token. In this case, we always return an error regardless
    // of where we are in the parsing.
    if self.current.token_type() == TokenType::ERROR {
      Err(self.error_at(&self.current, self.current.error_message().unwrap_or("Internal error")))
    } else {
      Ok(())
    }
  }

  // If the token matches, advances by consuming the token and returns true.
  // If the token does not match, false is returned.
  #[inline]
  fn matches(&mut self, tpe: TokenType) -> Res<bool> {
    if self.check(tpe) {
      self.advance()?;
      Ok(true)
    } else {
      Ok(false)
    }
  }

  // Consumes the current token and returns it if it matches the provided token type.
  // If there is no match, an error is returned.
  #[inline]
  fn consume(&mut self, tpe: TokenType, msg: &str) -> Res<Token> {
    if self.check(tpe) {
      let res = self.current;
      self.advance()?;
      Ok(res)
    } else {
      Err(self.error_at(&self.current, msg))
    }
  }

  // Returns parse error with a custom message and context.
  #[inline]
  fn error_at(&self, token: &Token, msg: &str) -> Error {
    // If the token spans multiple lines, we need to truncate up to new line.
    let context_prefix = format!("Line {}: ", token.line_num() + 1);
    let context = &self.sql[token.line_pos()..token.pos() + token.len()];
    let context_len = context.find('\n').unwrap_or(context.len());

    let full_msg = format!(
      concat!(
        "Syntax error at or near the position {} (line {}):",
        "\n",
        "  {}", // user-provided message
        "\n",
        "\n",
        "{}{}",
        "\n",
        "{5:->6$}", // cursor offset
        "{7:^>8$}", // cursor label
      ),
      // Relative position to the beginning of the token, 1-based.
      token.pos() - token.line_pos() + 1,
      // Line number of the beginning of the token, 1-based.
      token.line_num() + 1,
      // User-provided message.
      msg,
      // Context.
      context_prefix,
      &context[..context_len],
      "-",
      context_prefix.len() + token.pos() - token.line_pos(),
      "^",
      3,
    );
    Error::SQLParseError(full_msg)
  }

  //=============
  // Expressions
  //=============

  #[inline]
  fn primary(&mut self) -> Res<Expression> {
    // Global star.
    if self.matches(TokenType::STAR)? {
      return Ok(Expression::Star(Rc::new(Vec::new())));
    }

    // Identifier.
    if self.check(TokenType::IDENTIFIER) {
      let mut parts = Vec::new();
      loop {
        let token = self.consume(TokenType::IDENTIFIER, "Expected identifier")?;

        let mut part = String::new();
        let mut last_char = '"'; // removes the first double quote.
        for c in token.value(&self.sql).chars() {
          if c == '"' && last_char == c {
            // Reset to avoid removal of the next, non-paired, double quote.
            last_char = '\0';
          } else {
            part.push(c);
            last_char = c;
          }
        }
        if last_char == '"' {
          part.pop(); // removes the last double quote.
        }
        parts.push(part);

        if !self.matches(TokenType::DOT)? {
          return Ok(Expression::Identifier(Rc::new(parts)));
        }

        // For the cases "identifer.*".
        if self.matches(TokenType::STAR)? {
          return Ok(Expression::Star(Rc::new(parts)));
        }
      }
    }

    // Literals.
    if self.check(TokenType::NUMBER) {
      let value = self.current.value(&self.sql).to_string();

      if let Ok(int_value) = value.parse::<i64>() {
        self.advance()?;
        if int_value >= i32::MIN.into() && int_value <= i32::MAX.into() {
          return Ok(Expression::LiteralInt(int_value as i32));
        } else {
          return Ok(Expression::LiteralBigInt(int_value));
        }
      }

      if let Ok(double_value) = value.parse::<f64>() {
        self.advance()?;
        if double_value >= f32::MIN.into() && double_value <= f32::MAX.into() {
          return Ok(Expression::LiteralFloat(double_value as f32));
        } else {
          return Ok(Expression::LiteralDouble(double_value));
        }
      }

      return Err(self.error_at(&self.current, &format!("Invalid number '{}'", value)));
    } else if self.check(TokenType::STRING) {
      let mut literal = String::new();
      let mut last_char = '\''; // removes the first single quote.
      for c in self.current.value(&self.sql).chars() {
        if c == '\'' && last_char == c {
          // Reset to avoid removal of the next, non-paired, single quote.
          last_char = '\0';
        } else {
          literal.push(c);
          last_char = c;
        }
      }
      if last_char == '\'' {
        literal.pop(); // removes the last single quote.
      }
      self.advance()?;
      return Ok(Expression::LiteralString(Rc::new(literal)));
    } else if self.check(TokenType::NULL) {
      self.advance()?;
      return Ok(Expression::Null);
    }

    if self.matches(TokenType::PAREN_LEFT)? {
      let expr = self.expression()?;
      self.consume(TokenType::PAREN_RIGHT, "Expected ')'")?;
      return Ok(expr);
    }

    Err(
      self.error_at(
        &self.current,
        &format!(
          "Expected expression but found '{}'",
          &self.current.value(&self.sql)
        )
      )
    )
  }

  #[inline]
  fn unary(&mut self) -> Res<Expression> {
    if self.matches(TokenType::MINUS)? {
      Ok(Expression::UnaryMinus(Rc::new(self.primary()?)))
    } else if self.matches(TokenType::PLUS)? {
      Ok(Expression::UnaryPlus(Rc::new(self.primary()?)))
    } else {
      self.primary()
    }
  }

  #[inline]
  fn multiplication(&mut self) -> Res<Expression> {
    let mut expr = self.unary()?;

    loop {
      if self.matches(TokenType::STAR)? {
        let right = self.unary()?;
        expr = Expression::Multiply(Rc::new(expr), Rc::new(right));
      } else if self.matches(TokenType::SLASH)? {
        let right = self.unary()?;
        expr = Expression::Divide(Rc::new(expr), Rc::new(right));
      } else {
        break;
      }
    }

    Ok(expr)
  }

  #[inline]
  fn addition(&mut self) -> Res<Expression> {
    let mut expr = self.multiplication()?;

    loop {
      if self.matches(TokenType::PLUS)? {
        let right = self.multiplication()?;
        expr = Expression::Add(Rc::new(expr), Rc::new(right));
      } else if self.matches(TokenType::MINUS)? {
        let right = self.multiplication()?;
        expr = Expression::Subtract(Rc::new(expr), Rc::new(right));
      } else {
        break;
      }
    }

    Ok(expr)
  }

  #[inline]
  fn comparison(&mut self) -> Res<Expression> {
    let left = self.addition()?;

    // Parse the right-hand side of the expression.
    if self.matches(TokenType::EQUALS)? {
      let right = self.addition()?;
      Ok(Expression::Equals(Rc::new(left), Rc::new(right)))
    } else if self.matches(TokenType::GREATER_THAN)? {
      let right = self.addition()?;
      Ok(Expression::GreaterThan(Rc::new(left), Rc::new(right)))
    } else if self.matches(TokenType::GREATER_THAN_EQUALS)? {
      let right = self.addition()?;
      Ok(Expression::GreaterThanEquals(Rc::new(left), Rc::new(right)))
    } else if self.matches(TokenType::LESS_THAN)? {
      let right = self.addition()?;
      Ok(Expression::LessThan(Rc::new(left), Rc::new(right)))
    } else if self.matches(TokenType::LESS_THAN_EQUALS)? {
      let right = self.addition()?;
      Ok(Expression::LessThanEquals(Rc::new(left), Rc::new(right)))
    } else {
      // Technically, a single left-hand side can be a boolean expression already, e.g. boolean
      // literal or a column evaluated to a boolean, so absence of the comparison operator does
      // not necessarily mean an error.
      Ok(left)
    }
  }

  #[inline]
  fn logical_and(&mut self) -> Res<Expression> {
    let mut expr = self.comparison()?;

    while self.matches(TokenType::AND)? {
      let right = self.comparison()?;
      expr = Expression::And(Rc::new(expr), Rc::new(right));
    }

    Ok(expr)
  }

  #[inline]
  fn logical_or(&mut self) -> Res<Expression> {
    let mut expr = self.logical_and()?;

    while self.matches(TokenType::OR)? {
      let right = self.logical_and()?;
      expr = Expression::Or(Rc::new(expr), Rc::new(right));
    }

    Ok(expr)
  }

  #[inline]
  fn expression(&mut self) -> Res<Expression> {
    self.logical_or()
  }

  //============
  // Statements
  //============

  #[inline]
  fn column_type(&mut self) -> Res<Type> {
    let token = self.consume(TokenType::IDENTIFIER, "Expected column type")?;
    let type_str = token.value(&self.sql);

    if type_str.eq_ignore_ascii_case("INT") {
      Ok(Type::INT)
    } else if type_str.eq_ignore_ascii_case("BIGINT") {
      Ok(Type::BIGINT)
    } else if type_str.eq_ignore_ascii_case("TEXT") {
      Ok(Type::TEXT)
    } else {
      Err(self.error_at(&self.current, &format!("Unknown column type '{}'", type_str)))
    }
  }

  // Parses an optional alias.
  // The position is only advanced if the alias exists.
  #[inline]
  fn optional_alias(&mut self) -> Res<Option<Rc<String>>> {
    if self.check(TokenType::IDENTIFIER) {
      let value = self.current.value(&self.sql).to_string();
      self.advance()?;
      Ok(Some(Rc::new(value)))
    } else if self.matches(TokenType::AS)? {
      let token = self.consume(TokenType::IDENTIFIER, "Expected an identifier after AS")?;
      let value = token.value(&self.sql).to_string();
      Ok(Some(Rc::new(value)))
    } else {
      // There is no alias.
      Ok(None)
    }
  }

  #[inline]
  fn expression_list(&mut self) -> Res<Vec<Expression>> {
    let mut expressions = Vec::new();

    loop {
      let mut expr = self.expression()?;

      // Parse optional alias:
      //   Expression [alias]
      //   Expression [AS alias]
      if let Some(alias) = self.optional_alias()? {
        expr = Expression::Alias(Rc::new(expr), alias);
      }

      expressions.push(expr);

      if self.check(TokenType::COMMA) {
        self.advance()?;
      } else {
        break;
      }
    }

    Ok(expressions)
  }

  #[inline]
  fn table_identifier(&mut self) -> Res<TableIdentifier> {
    // We expect:
    //   [schema].[table]
    //   [table] (implies the currently selected schema)
    let part1_token = self.consume(
      TokenType::IDENTIFIER,
      "Expected a table name or schema.table qualifier"
    )?;

    if self.matches(TokenType::DOT)? {
      let part2_token = self.consume(
        TokenType::IDENTIFIER,
        "Expected a table name after the schema"
      )?;

      Ok(
        TableIdentifier::new(
          Some(part1_token.value(&self.sql).to_string()),
          part2_token.value(&self.sql).to_string()
        )
      )
    } else {
      // We have [table] with the current schema.
      Ok(
        TableIdentifier::new(
          None,
          part1_token.value(&self.sql).to_string()
        )
      )
    }
  }

  #[inline]
  fn from_statement(&mut self) -> Res<Plan> {
    let table_ident = self.table_identifier()?;
    // Parse optional alias:
    //   FROM table [alias]
    //   FROM table [AS alias]
    let table_alias = self.optional_alias()?;
    Ok(Plan::UnresolvedTableScan(Rc::new(table_ident), table_alias))
  }

  #[inline]
  fn where_statement(&mut self, plan: Plan) -> Res<Plan> {
    let expression = self.expression()?;
    Ok(Plan::Filter(Rc::new(expression), Rc::new(plan)))
  }

  #[inline]
  fn limit_statement(&mut self, plan: Plan) -> Res<Plan> {
    // LIMIT <number>.
    let token = self.consume(TokenType::NUMBER, "Expected LIMIT value")?;
    match token.value(&self.sql).parse() {
      Ok(value) => Ok(Plan::Limit(value, Rc::new(plan))),
      // We failed to parse the value for the limit node.
      Err(_) => Err(self.error_at(&token, "Invalid LIMIT number")),
    }
  }

  #[inline]
  fn select_statement(&mut self) -> Res<Plan> {
    let mut plan = Plan::Empty;

    // Parse the list of columns for projection.
    let expressions = self.expression_list()?;

    if self.matches(TokenType::FROM)? {
      plan = self.from_statement()?;
    }

    plan = Plan::Project(Rc::new(expressions), Rc::new(plan));

    if self.matches(TokenType::WHERE)? {
      plan = self.where_statement(plan)?;
    }

    if self.matches(TokenType::LIMIT)? {
      plan = self.limit_statement(plan)?;
    }

    Ok(plan)
  }

  #[inline]
  fn insert_statement(&mut self) -> Res<Plan> {
    self.consume(TokenType::INTO, "Expected INTO keyword")?;
    // Extract the table name.
    let table_ident = self.table_identifier()?;

    // Parse the target columns.
    let mut columns = Vec::new();
    if self.matches(TokenType::PAREN_LEFT)? {
      loop {
        let col_name = self.consume(TokenType::IDENTIFIER, "Expected column name")?;
        columns.push(col_name.value(&self.sql).to_string());

        if self.matches(TokenType::COMMA)? {
          // Continue parsing identifiers.
        } else {
          break;
        }
      }

      self.consume(TokenType::PAREN_RIGHT, "Expected ')'")?;
    }

    // Parse values or the query.
    let query = if self.matches(TokenType::VALUES)? {
      let mut rows = Vec::new();
      // The initial number of expressions must equal to the number of columns.
      // If columns are empty, then no columns were provided.
      let mut expected_expr_len: usize = columns.len();
      loop {
        self.consume(TokenType::PAREN_LEFT, "Expected '('")?;
        // Parse expression list.
        let mut expr = Vec::new();
        loop {
          expr.push(self.expression()?);
          if !self.matches(TokenType::COMMA)? {
            break;
          }
        }

        if expected_expr_len == 0 {
          expected_expr_len = expr.len();
        }

        if expr.len() != expected_expr_len {
          return Err(
            self.error_at(
              &self.current,
              &format!(
                "Mismatch in the number of expressions: expected {} but found {}",
                expected_expr_len,
                expr.len(),
              )
            )
          );
        }

        rows.push(expr);

        self.consume(TokenType::PAREN_RIGHT, "Expected ')'")?;

        // Check if we need to continue parsing expressions.
        if !self.matches(TokenType::COMMA)? {
          break;
        }
      }
      Plan::LocalRelation(Rc::new(rows))
    } else if self.matches(TokenType::SELECT)? {
      self.select_statement()?
    } else {
      return Err(
        self.error_at(
          &self.current,
          "Expected SELECT query or VALUES list"
        )
      );
    };

    Ok(Plan::InsertInto(Rc::new(table_ident), Rc::new(columns), Rc::new(query)))
  }

  #[inline]
  fn create_schema_statement(&mut self) -> Res<Plan> {
    let token = self.consume(TokenType::IDENTIFIER, "Expected schema identifier")?;
    Ok(Plan::CreateSchema(Rc::new(token.value(&self.sql).to_string())))
  }

  #[inline]
  fn create_table_statement(&mut self) -> Res<Plan> {
    let ident = self.table_identifier()?;
    let mut fields = Vec::new();

    self.consume(TokenType::PAREN_LEFT, "Expected '('")?;

    loop {
      let col_name = self.consume(TokenType::IDENTIFIER, "Expected column name")?;
      let col_type = self.column_type()?;
      let mut col_nullable = true; // column is nullable by default.
      // Parse optional constraints.
      if self.matches(TokenType::NULL)? {
        // The field is null.
        col_nullable = true;
      } else if self.matches(TokenType::NOT)? {
        self.consume(TokenType::NULL, "Expected NOT NULL constraint")?;
        col_nullable = false;
      }

      match Field::new(col_name.value(&self.sql), col_type, col_nullable) {
        Ok(field) => {
          fields.push(field);
        },
        Err(err) => {
          return Err(
            self.error_at(
              &self.current,
              &format!("Error while creating a field: {:?}", err)
            )
          );
        },
      }

      if self.matches(TokenType::COMMA)? {
        // Continue parsing fields.
      } else {
        break;
      }
    }

    self.consume(TokenType::PAREN_RIGHT, "Expected ')'")?;

    let schema = match Fields::new(fields) {
      Ok(fields) => fields,
      Err(err) => {
        return Err(
          self.error_at(
            &self.current,
            &format!("Error in table schema: {:?}", err)
          )
        );
      },
    };

    Ok(Plan::CreateTable(Rc::new(ident), Rc::new(schema)))
  }

  #[inline]
  fn drop_schema_statement(&mut self) -> Res<Plan> {
    let token = self.consume(TokenType::IDENTIFIER, "Expected schema identifier")?;
    let is_cascade = self.matches(TokenType::CASCADE)?;
    Ok(Plan::DropSchema(Rc::new(token.value(&self.sql).to_string()), is_cascade))
  }

  #[inline]
  fn drop_table_statement(&mut self) -> Res<Plan> {
    let ident = self.table_identifier()?;
    Ok(Plan::DropTable(Rc::new(ident)))
  }

  #[inline]
  fn statement(&mut self) -> Res<Plan> {
    // Each statement can have an optional `;` at the end.
    // We need to capture errors when there are extra tokens at the end of the statement.
    let mut stmt: Option<Plan> = None;

    if self.matches(TokenType::CREATE)? {
      if self.matches(TokenType::SCHEMA)? {
        stmt = Some(self.create_schema_statement()?);
      } else if self.matches(TokenType::TABLE)? {
        stmt = Some(self.create_table_statement()?);
      }
    } else if self.matches(TokenType::DROP)? {
      if self.matches(TokenType::SCHEMA)? {
        stmt = Some(self.drop_schema_statement()?);
      } else if self.matches(TokenType::TABLE)? {
        stmt = Some(self.drop_table_statement()?);
      }
    } else if self.matches(TokenType::INSERT)? {
      stmt = Some(self.insert_statement()?);
    } else if self.matches(TokenType::SELECT)? {
      stmt = Some(self.select_statement()?);
    }

    match stmt {
      Some(stmt) => {
        if !self.matches(TokenType::SEMICOLON)? && !self.done() {
          Err(
            self.error_at(
              &self.current,
              &format!("Unexpected token '{}'", self.current.value(&self.sql))
            )
          )
        } else {
          Ok(stmt)
        }
      },
      None => {
        Err(
          self.error_at(
            &self.current,
            &format!("Unsupported token '{}'", self.current.value(&self.sql))
          )
        )
      },
    }
  }
}

// Returns a sequence of Plans corresponding to the input SQL string.
// SQL string can contain one or more statements, each plan represents a statement/query.
pub fn parse(sql: &str) -> Res<Vec<Plan>> {
  let mut scanner = Scanner::new(sql.as_bytes());
  let token = scanner.next_token();

  let mut parser = Parser {
    sql: sql,
    scanner: scanner,
    current: token,
  };

  let mut plans = Vec::new();

  while !parser.done() {
    plans.push(parser.statement()?);
  }

  Ok(plans)
}

#[cfg(test)]
pub mod tests {
  use super::*;
  use crate::exec::plan::dsl::*;

  // Helper method to check the query plan.
  fn assert_plans(query: &str, plans: Vec<Plan>) {
    match parse(query) {
      Ok(v) => {
        assert_eq!(v.len(), plans.len());
        for i in 0..plans.len() {
          assert_eq!(v[i], plans[i]);
        }
      },
      Err(Error::SQLParseError(ref msg)) => {
        panic!("SQLParseError: Failed to parse the query: \n{}", msg);
      },
      Err(err) => {
        panic!("Unexpected error during query parsing: \n{:?}", err);
      },
    }
  }

  fn assert_plan(query: &str, plan: Plan) {
    assert_plans(query, vec![plan]);
  }

  #[test]
  fn test_parser_empty_query() {
    assert_plans("", vec![]);
  }

  #[test]
  #[should_panic(expected = "Unsupported token ';'")]
  fn test_parser_empty_query_semicolon() {
    assert_plan(";", empty());
  }

  #[test]
  fn test_parser_comment() {
    assert_plans("-- comment", vec![]);
  }

  #[test]
  fn test_parser_literals() {
    assert_plan(
      "select 1, 1.2, -3.4, +5.6, '7.8', (9), null;",
      project(
        vec![
          int(1),
          float(1.2),
          _minus(float(3.4)),
          _plus(float(5.6)),
          string("7.8"),
          int(9),
          null(),
        ],
        empty()
      )
    );
  }

  #[test]
  fn test_parser_literals_strings() {
    assert_plan(
      "select 'a', 'a b', 'a''b''c''d', 'a\"''b', '\"aa''s bb\"', 'quotes: ''\"''';",
      project(
        vec![
          string("a"),
          string("a b"),
          string("a'b'c'd"),
          string("a\"'b"),
          string("\"aa's bb\""),
          string("quotes: '\"'"),
        ],
        empty()
      )
    );

    assert_plan(
      "select '', ' ', '''', '\"'",
      project(
        vec![
          string(""),
          string(" "),
          string("'"),
          string("\""),
        ],
        empty()
      )
    );
  }

  #[test]
  fn test_parser_expressions() {
    assert_plan(
      "select *, 1 * 2",
      project(
        vec![
          star(),
          multiply(int(1), int(2)),
        ],
        empty()
      )
    );

    assert_plan(
      "select 1 + 2, (2 - 1) / 3 * 5, (2 - 1) / (3 * 5), 100000000000, 1e50;",
      project(
        vec![
          add(int(1), int(2)),
          multiply(
            divide(
              subtract(
                int(2),
                int(1)
              ),
              int(3)
            ),
            int(5)
          ),
          divide(
            subtract(
              int(2),
              int(1)
            ),
            multiply(
              int(3),
              int(5)
            )
          ),
          bigint(100000000000),
          double(1e50),
        ],
        empty()
      )
    );
  }

  #[test]
  fn test_parser_expressions_identifier() {
    assert_plan(
      "select \"a b\", \"a \"\" b\", \"ab\"\"\"",
      project(
        vec![
          identifier("a b"),
          identifier("a \" b"),
          identifier("ab\""),
        ],
        empty()
      ),
    );
  }

  #[test]
  fn test_parser_expressions_chain() {
    assert_plan(
      "select a.b.c, 'a.b.c', \"a.b.c\", \"a\".\"b\".\"c\", \"a.b\".c",
      project(
        vec![
          qualified_identifier(vec!["a", "b", "c"]),
          string("a.b.c"),
          identifier("a.b.c"),
          qualified_identifier(vec!["a", "b", "c"]),
          qualified_identifier(vec!["a.b", "c"]),
        ],
        empty()
      ),
    );

    assert_plan(
      "select 1.2",
      project(vec![float(1.2)], empty()),
    );
  }

  #[test]
  fn test_parser_expressions_star() {
    assert_plan(
      "select *",
      project(vec![star()], empty()),
    );

    assert_plan(
      "select *, *",
      project(vec![star(), star()], empty()),
    );

    assert_plan(
      "select t.* from test t",
      project(vec![qualified_star(vec!["t"])], from(None, "test", Some("t"))),
    );

    assert_plan(
      "select s.t.*",
      project(vec![qualified_star(vec!["s", "t"])], empty()),
    );
  }

  #[test]
  #[should_panic(expected = "Unexpected token '.'")]
  fn test_parser_expressions_star_invalid_0() {
    assert_plan(
      "select *.a",
      empty(),
    );
  }

  #[test]
  #[should_panic(expected = "Unexpected token '.'")]
  fn test_parser_expressions_star_invalid_1() {
    assert_plan(
      "select *.*",
      empty(),
    );
  }

  #[test]
  #[should_panic(expected = "Unexpected token '.'")]
  fn test_parser_expressions_star_invalid_2() {
    assert_plan(
      "select t.*.*",
      empty(),
    );
  }

  #[test]
  #[should_panic(expected = "Unexpected token '2'")]
  fn test_parser_expressions_star_invalid_3() {
    assert_plan(
      "select * 2",
      empty(),
    );
  }

  #[test]
  #[should_panic(expected = "Expected identifier")]
  fn test_parser_expressions_chain_fail_extra_dot() {
    assert_plan(
      "select a.b.",
      empty(),
    );
  }

  #[test]
  #[should_panic(expected = "Expected identifier")]
  fn test_parser_expressions_chain_fail_missing_identifier() {
    assert_plan(
      "select a.1",
      empty(),
    );
  }

  #[test]
  fn test_parser_alias() {
    assert_plan(
      "select a as col1, b col2, c as col3, d col4;",
      project(
        vec![
          alias(identifier("a"), "col1"),
          alias(identifier("b"), "col2"),
          alias(identifier("c"), "col3"),
          alias(identifier("d"), "col4"),
        ],
        empty()
      )
    );
  }

  #[test]
  #[should_panic(expected = "Expected an identifier after AS")]
  fn test_parser_alias_fail_as() {
    // The test verifies that an identifier follows AS.
    assert_plan(
      "select a col1, b as, c as col3;",
      empty()
    );
  }

  #[test]
  fn test_parser_from() {
    assert_plan(
      "select * from test_table",
      project(
        vec![
          star(),
        ],
        from(None, "test_table", None)
      )
    );

    assert_plan(
      "select * from test_schema.test_table",
      project(
        vec![
          star(),
        ],
        from(Some("test_schema"), "test_table", None)
      )
    );
  }

  #[test]
  fn test_parser_from_alias() {
    assert_plan(
      "select col1 as a from test as t",
      project(
        vec![
          alias(identifier("col1"), "a"),
        ],
        from(None, "test", Some("t"))
      ),
    );

    assert_plan(
      "select col1 a from test t",
      project(
        vec![
          alias(identifier("col1"), "a"),
        ],
        from(None, "test", Some("t"))
      ),
    );
  }

  #[test]
  #[should_panic(expected = "Expected an identifier after AS")]
  fn test_parser_from_alias_fail_as() {
    assert_plan(
      "select a from test as",
      empty(),
    );
  }

  #[test]
  fn test_parser_where() {
    assert_plan(
      "select * from test where a",
      filter(
        identifier("a"), // boolean column
        project(vec![star()], from(None, "test", None))
      )
    );

    assert_plan(
      "select * from test where 1 = 2 and a > b or c < d",
      filter(
        or(
          and(
            equals(
              int(1),
              int(2)
            ),
            greater_than(
              identifier("a"),
              identifier("b")
            )
          ),
          less_than(
            identifier("c"),
            identifier("d")
          )
        ),
        project(vec![star()], from(None, "test", None))
      )
    );

    assert_plan(
      "select * from test where 1 = 2 and (a > b or c < d)",
      filter(
        and(
          equals(
            int(1),
            int(2)
          ),
          or(
            greater_than(
              identifier("a"),
              identifier("b")
            ),
            less_than(
              identifier("c"),
              identifier("d")
            )
          )
        ),
        project(vec![star()], from(None, "test", None))
      )
    );

    assert_plan(
      "select * from test where ((b) = ('def') or (a > 1)) and b = 'abc'",
      filter(
        and(
          or(
            equals(
              identifier("b"),
              string("def")
            ),
            greater_than(
              identifier("a"),
              int(1)
            )
          ),
          equals(
            identifier("b"),
            string("abc")
          )
        ),
        project(vec![star()], from(None, "test", None))
      )
    );
  }

  #[test]
  fn test_parser_limit() {
    assert_plan(
      "select * from test limit 123",
      limit(
        123,
        project(vec![star()], from(None, "test", None))
      )
    );
  }

  #[test]
  #[should_panic(expected = "Expected SELECT query or VALUES list")]
  fn test_parser_insert_into_error() {
    assert_plan(
      "insert into test_table",
      empty()
    );
  }

  #[test]
  #[should_panic(expected = "Expected expression but found ')'")]
  fn test_parser_insert_into_values_unclosed_list() {
    assert_plan(
      "insert into test_table values (1, 'a', )",
      empty()
    );
  }

  #[test]
  #[should_panic(expected = "Expected '('")]
  fn test_parser_insert_into_values_unclosed_sequence() {
    assert_plan(
      "insert into test_table values (1, 'a'),",
      empty()
    );
  }

  #[test]
  #[should_panic(expected = "Mismatch in the number of expressions: expected 2 but found 3")]
  fn test_parser_insert_into_values_expr_mismatch() {
    assert_plan(
      "insert into test_table values (1, 'a'), (2, 'b', 'c')",
      empty()
    )
  }

  #[test]
  #[should_panic(expected = "Mismatch in the number of expressions: expected 3 but found 2")]
  fn test_parser_insert_into_values_cols_mismatch() {
    assert_plan(
      "insert into test_table (a, b, c) values (1, 'a'), (2, 'b')",
      empty()
    )
  }

  #[test]
  #[should_panic(expected = "Expected expression but found ')'")]
  fn test_parser_insert_into_values_empty_list() {
    assert_plan(
      "insert into test_table (a, b, c) values (), (2, 'b')",
      empty()
    )
  }

  #[test]
  fn test_parser_insert_into_values_star() {
    assert_plan(
      "insert into test_table (a, b, c) values (*, 1, 2 + 3)",
      insert_into_values(
        None,
        "test_table",
        vec!["a".to_string(), "b".to_string(), "c".to_string()],
        vec![
          vec![
            star(),
            int(1),
            add(int(2), int(3))
          ],
        ]
      )
    )
  }

  #[test]
  fn test_parser_insert_into_values() {
    assert_plan(
      "insert into test_table values (1, 'a'), (2, 'b')",
      insert_into_values(
        None,
        "test_table",
        vec![],
        vec![
          vec![int(1), string("a")],
          vec![int(2), string("b")],
        ]
      )
    );

    assert_plan(
      "insert into test_schema.test_table values (1, 'a'), (2, 'b')",
      insert_into_values(
        Some("test_schema"),
        "test_table",
        vec![],
        vec![
          vec![int(1), string("a")],
          vec![int(2), string("b")],
        ]
      )
    );

    assert_plan(
      "insert into test_schema.test_table (a, b) values (1, 'a'), (1 + 2, 'b')",
      insert_into_values(
        Some("test_schema"),
        "test_table",
        vec!["a".to_string(), "b".to_string()],
        vec![
          vec![int(1), string("a")],
          vec![add(int(1), int(2)), string("b")],
        ]
      )
    );
  }

  #[test]
  fn test_parser_insert_into_select() {
    assert_plan(
      "insert into test_schema.test_table select 1 as a, 2 as b",
      insert_into_select(
        Some("test_schema"),
        "test_table",
        vec![],
        project(
          vec![
            alias(int(1), "a"),
            alias(int(2), "b"),
          ],
          empty()
        )
      )
    );

    assert_plan(
      "insert into test_schema.test_table (a, b) select 1 as a, 2 as b",
      insert_into_select(
        Some("test_schema"),
        "test_table",
        vec!["a".to_string(), "b".to_string()],
        project(
          vec![
            alias(int(1), "a"),
            alias(int(2), "b"),
          ],
          empty()
        )
      )
    );
  }

  #[test]
  fn test_parser_create_schema() {
    assert_plan(
      "create schema test;",
      create_schema("test")
    );
  }

  #[test]
  #[should_panic(expected = "Expected schema identifier")]
  fn test_parser_create_schema_error() {
    assert_plan(
      "create schema 123;",
      empty()
    );
  }

  #[test]
  #[should_panic(expected = "Expected '('")]
  fn test_parser_create_table_error_no_columns() {
    assert_plan(
      "create table test_schema.test_table;",
      empty()
    );
  }

  #[test]
  #[should_panic(expected = "Expected column name")]
  fn test_parser_create_table_error_no_column_name() {
    assert_plan(
      "create table test_schema.test_table ();",
      empty()
    );
  }

  #[test]
  #[should_panic(expected = "Expected column type")]
  fn test_parser_create_table_error_no_column_type() {
    assert_plan(
      "create table test_schema.test_table (c1);",
      empty()
    );
  }

  #[test]
  #[should_panic(expected = "Expected NOT NULL constraint")]
  fn test_parser_create_table_error_column_non_null() {
    assert_plan(
      "create table test_schema.test_table (c1 int not);",
      empty()
    );
  }

  #[test]
  #[should_panic(expected = "Unknown column type 'int2'")]
  fn test_parser_create_table_error_unknown_column_type() {
    assert_plan(
      "create table test_schema.test_table (c1 int2);",
      empty()
    );
  }

  #[test]
  fn test_parser_create_table() {
    assert_plan(
      "create table test_schema.test_table (c1 int not null, c2 text null, c3 bigint);",
      create_table(
        Some("test_schema"),
        "test_table",
        Fields::new(
          vec![
            Field::new("c1", Type::INT, false).unwrap(),
            Field::new("c2", Type::TEXT, true).unwrap(),
            Field::new("c3", Type::BIGINT, true).unwrap(),
          ]
        ).unwrap()
      )
    );
  }

  #[test]
  fn test_parser_drop_schema() {
    assert_plan(
      "drop schema test_schema;",
      drop_schema("test_schema", false)
    );

    assert_plan(
      "drop schema test_schema cascade;",
      drop_schema("test_schema", true)
    );
  }

  #[test]
  fn test_parser_drop_table() {
    assert_plan(
      "drop table test_table;",
      drop_table(None, "test_table")
    );

    assert_plan(
      "drop table test_schema.test_table;",
      drop_table(Some("test_schema"), "test_table")
    );
  }

  #[test]
  fn test_parser_multiple_statements() {
    assert_plans(
      "select 1; select 2; select 3",
      vec![
        project(vec![int(1)], empty()),
        project(vec![int(2)], empty()),
        project(vec![int(3)], empty()),
      ],
    );
  }
}
