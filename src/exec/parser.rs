use std::rc::Rc;
use crate::common::error::{Error, Res};
use crate::exec::plan::{Expression, Plan};
use crate::exec::scanner::{Scanner, Token, TokenType};

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

  // Returns the value of the current token.
  // It is typically used after `check()` method, knowing that the token is valid.
  // Panics if the current token is None.
  #[inline]
  fn token_value(&self) -> &str {
    self.current.value(self.sql)
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

  #[inline]
  fn consume(&mut self, tpe: TokenType, msg: &str) -> Res<()> {
    if self.check(tpe) {
      self.advance()
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

  //============
  // Expresions
  //============

  #[inline]
  fn primary(&mut self) -> Res<Expression> {
    // Identifier.
    if self.check(TokenType::IDENTIFIER) {
      let value = self.token_value().to_string();
      self.advance()?;
      return Ok(Expression::Identifier(Rc::new(value)));
    }

    // Literals.
    if self.check(TokenType::NUMBER) {
      let value = self.token_value().to_string();
      self.advance()?;
      return Ok(Expression::LiteralNumber(Rc::new(value)));
    } else if self.check(TokenType::STRING) {
      let value = self.token_value().to_string();
      self.advance()?;
      return Ok(Expression::LiteralString(Rc::new(value)));
    } else if self.check(TokenType::NULL) {
      self.advance()?;
      return Ok(Expression::Null);
    }

    if self.matches(TokenType::PAREN_LEFT)? {
      let expr = self.expression()?;
      self.consume(TokenType::PAREN_RIGHT, "Expected closing `)`")?;
      return Ok(expr);
    }

    Err(
      self.error_at(
        &self.current,
        &format!(
          "Expected expression but found '{}'",
          &self.token_value()
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
  fn expression_list(&mut self) -> Res<Vec<Expression>> {
    let mut expressions = Vec::new();

    loop {
      if self.check(TokenType::STAR) {
        self.advance()?;
        expressions.push(Expression::Star);
      } else {
        let mut expr = self.expression()?;

        // Parse optional alias:
        //   Expression [alias]
        //   Expression [AS alias]
        if self.check(TokenType::AS) {
          self.advance()?;
        }
        if self.check(TokenType::IDENTIFIER) {
          let value = self.token_value().to_string();
          self.advance()?;
          expr = Expression::Alias(Rc::new(expr), Rc::new(value));
        }

        expressions.push(expr);
      }

      if self.check(TokenType::COMMA) {
        self.advance()?;
      } else {
        break;
      }
    }

    Ok(expressions)
  }

  #[inline]
  fn from_statement(&mut self) -> Res<Plan> {
    // We expect:
    //   [schema].[table]
    //   [table] (implies the currently selected schema)
    if self.check(TokenType::IDENTIFIER) {
      let identifier1 = self.token_value().to_string();
      self.advance()?;

      if self.check(TokenType::DOT) {
        // We have [schema].[table].
        let context_token = self.current.clone();
        self.advance()?;
        // We expect table name after ".".
        if self.check(TokenType::IDENTIFIER) {
          let identifier2 = self.token_value().to_string();
          self.advance()?;
          Ok(Plan::TableScan(Some(Rc::new(identifier1)), Rc::new(identifier2)))
        } else {
          Err(self.error_at(&context_token, "Expected a table name after the schema name"))
        }
      } else {
        // We have [table] with the current schema.
        Ok(Plan::TableScan(None, Rc::new(identifier1.to_string())))
      }
    } else {
      Err(
        self.error_at(
          &self.current,
          &format!(
            "Expected a table name or `schema`.`table` qualifier after FROM but found '{}'",
            self.token_value()
          )
        )
      )
    }
  }

  #[inline]
  fn where_statement(&mut self, plan: Plan) -> Res<Plan> {
    let expression = self.expression()?;
    Ok(Plan::Filter(Rc::new(expression), Rc::new(plan)))
  }

  #[inline]
  fn limit_statement(&mut self, plan: Plan) -> Res<Plan> {
    // LIMIT <number>.
    if self.check(TokenType::NUMBER) {
      match self.token_value().parse() {
        Ok(value) => {
          // Advance and return the limit plan.
          self.advance()?;
          Ok(Plan::Limit(value, Rc::new(plan)))
        },
        Err(_) => {
          // We failed to parse the value into a limit.
          Err(
            self.error_at(
              &self.current,
              &format!(
                "Expected LIMIT value to be a valid number but found '{}'",
                self.token_value()
              )
            )
          )
        }
      }
    } else {
      Err(self.error_at(&self.current, "Expected limit value"))
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
  fn statement(&mut self) -> Res<Plan> {
    // Each statement can have an optional `;` at the end.
    // We need to capture any errors when the statement is followed by some other token.
    if self.matches(TokenType::SELECT)? {
      let stmt = self.select_statement()?;
      if !self.matches(TokenType::SEMICOLON)? && !self.done() {
        Err(self.error_at(&self.current, &format!("Unexpected token '{}'", self.token_value())))
      } else {
        Ok(stmt)
      }
    } else {
      Err(
        self.error_at(
          &self.current,
          &format!("Unsupported token {}", self.token_value())
        )
      )
    }
  }
}

// Returns Plan instance from the sql string.
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
  fn assert_plan(query: &str, plan: Plan) {
    match parse(query) {
      Ok(mut v) => {
        assert_eq!(v.pop().unwrap(), plan);
      },
      Err(Error::SQLParseError(ref msg)) => {
        panic!("SQLParseError: Failed to parse the query: \n{}", msg);
      },
      Err(err) => {
        panic!("Unexpected error during query parsing: \n{:?}", err);
      },
    }
  }

  #[test]
  fn test_parser_literals() {
    assert_plan(
      "select 1, 1.2, -3.4, +5.6, '7.8', (9), null;",
      project(
        vec![
          number("1"),
          number("1.2"),
          _minus(number("3.4")),
          _plus(number("5.6")),
          string("7.8"),
          number("9"),
          null(),
        ],
        empty()
      )
    );
  }

  #[test]
  fn test_parser_expressions() {
    assert_plan(
      "select 1 + 2, (2 - 1) / 3 * 5, (2 - 1) / (3 * 5);",
      project(
        vec![
          add(number("1"), number("2")),
          multiply(
            divide(
              subtract(
                number("2"),
                number("1")
              ),
              number("3")
            ),
            number("5")
          ),
          divide(
            subtract(
              number("2"),
              number("1")
            ),
            multiply(
              number("3"),
              number("5")
            )
          ),
        ],
        empty()
      )
    );
  }

  #[test]
  fn test_parser_alias() {
    assert_plan(
      "select a as col1, b col2, c as col3;",
      project(
        vec![
          alias(identifier("a"), "col1"),
          alias(identifier("b"), "col2"),
          alias(identifier("c"), "col3"),
        ],
        empty()
      )
    );
  }

  #[test]
  fn test_parser_from() {
    assert_plan(
      "select * from test",
      project(
        vec![
          star(),
        ],
        from(None, "test")
      )
    );

    assert_plan(
      "select * from schema.test",
      project(
        vec![
          star(),
        ],
        from(Some("schema"), "test")
      )
    );
  }

  #[test]
  fn test_parser_where() {
    assert_plan(
      "select * from test where a",
      filter(
        identifier("a"), // boolean column
        project(vec![star()], from(None, "test"))
      )
    );

    assert_plan(
      "select * from test where 1 = 2 and a > b or c < d",
      filter(
        or(
          and(
            equals(
              number("1"),
              number("2")
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
        project(vec![star()], from(None, "test"))
      )
    );

    assert_plan(
      "select * from test where 1 = 2 and (a > b or c < d)",
      filter(
        and(
          equals(
            number("1"),
            number("2")
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
        project(vec![star()], from(None, "test"))
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
              number("1")
            )
          ),
          equals(
            identifier("b"),
            string("abc")
          )
        ),
        project(vec![star()], from(None, "test"))
      )
    );
  }

  #[test]
  fn test_parser_limit() {
    assert_plan(
      "select * from test limit 123",
      limit(
        123,
        project(vec![star()], from(None, "test"))
      )
    );
  }
}
