use crate::common::error::{Error, Res};
use crate::exec::scanner::{Scanner, Token, TokenType};

#[derive(Debug)]
pub enum ParsedPlan {
  Filter(Expression /* filter expression */, Box<ParsedPlan> /* child */),
  Limit(usize /* limit */, Box<ParsedPlan> /* child */),
  Project(Vec<String> /* expressions */, Box<ParsedPlan>),
  TableScan(Option<String> /* schema */, String /* table name */),
  Empty, // indicates an empty relation, e.g. "select 1;"
}

#[derive(Debug)]
pub enum Expression {
  And(Box<Expression>, Box<Expression>),
  Or(Box<Expression>, Box<Expression>),
  Equals(Box<Expression>, Box<Expression>),
  GreaterThan(Box<Expression>, Box<Expression>),
  GreaterThanEquals(Box<Expression>, Box<Expression>),
  LessThan(Box<Expression>, Box<Expression>),
  LessThanEquals(Box<Expression>, Box<Expression>),
  Multiply(Box<Expression>, Box<Expression>),
  Divide(Box<Expression>, Box<Expression>),
  Add(Box<Expression>, Box<Expression>),
  Subtract(Box<Expression>, Box<Expression>),
  UnaryPlus(Box<Expression>),
  UnaryMinus(Box<Expression>),
  Identifier(String /* identifier value */),
  LiteralNumber(String /* numeric value */),
  LiteralString(String /* string value */),
}

pub struct Parser<'a> {
  sql: &'a str,
  scanner: Scanner<'a>,
  current: Token,
  plans: Vec<ParsedPlan>,
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
  fn current_value(&self) -> &str {
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
      let value = self.current_value().to_string();
      self.advance()?;
      return Ok(Expression::Identifier(value));
    }

    // Literals.
    if self.check(TokenType::NUMBER) {
      let value = self.current_value().to_string();
      self.advance()?;
      return Ok(Expression::LiteralNumber(value));
    } else if self.check(TokenType::STRING) {
      let value = self.current_value().to_string();
      self.advance()?;
      return Ok(Expression::LiteralString(value));
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
          &self.current_value()
        )
      )
    )
  }

  #[inline]
  fn unary(&mut self) -> Res<Expression> {
    if self.matches(TokenType::MINUS)? {
      Ok(Expression::UnaryMinus(Box::new(self.primary()?)))
    } else if self.matches(TokenType::PLUS)? {
      Ok(Expression::UnaryPlus(Box::new(self.primary()?)))
    } else {
      self.primary()
    }
  }

  #[inline]
  fn multiplication(&mut self) -> Res<Expression> {
    let mut expr = self.unary()?;

    loop {
      if self.matches(TokenType::SLASH)? {
        let right = self.unary()?;
        expr = Expression::Multiply(Box::new(expr), Box::new(right));
      } else if self.matches(TokenType::STAR)? {
        let right = self.unary()?;
        expr = Expression::Divide(Box::new(expr), Box::new(right));
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
        expr = Expression::Add(Box::new(expr), Box::new(right));
      } else if self.matches(TokenType::MINUS)? {
        let right = self.multiplication()?;
        expr = Expression::Subtract(Box::new(expr), Box::new(right));
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
      Ok(Expression::Equals(Box::new(left), Box::new(right)))
    } else if self.matches(TokenType::GREATER_THAN)? {
      let right = self.addition()?;
      Ok(Expression::GreaterThan(Box::new(left), Box::new(right)))
    } else if self.matches(TokenType::GREATER_THAN_EQUALS)? {
      let right = self.addition()?;
      Ok(Expression::GreaterThanEquals(Box::new(left), Box::new(right)))
    } else if self.matches(TokenType::LESS_THAN)? {
      let right = self.addition()?;
      Ok(Expression::LessThan(Box::new(left), Box::new(right)))
    } else if self.matches(TokenType::LESS_THAN_EQUALS)? {
      let right = self.addition()?;
      Ok(Expression::LessThanEquals(Box::new(left), Box::new(right)))
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
      expr = Expression::And(Box::new(expr), Box::new(right));
    }

    Ok(expr)
  }

  #[inline]
  fn logical_or(&mut self) -> Res<Expression> {
    let mut expr = self.logical_and()?;

    while self.matches(TokenType::OR)? {
      let right = self.logical_and()?;
      expr = Expression::Or(Box::new(expr), Box::new(right));
    }

    Ok(expr)
  }

  #[inline]
  fn expression(&mut self) -> Res<Expression> {
    self.logical_or()
  }

  #[inline]
  fn expression_list(&mut self) -> Res<Vec<String>> {
    // Expression can be "*" or "identifier".
    // a
    // a, b
    // a, b, *
    let mut expressions = Vec::new();

    let mut is_first_expression = true;
    let mut context_token = self.current.clone();

    loop {
      if self.check(TokenType::IDENTIFIER) {
        expressions.push(self.current_value().to_string());
      } else if self.check(TokenType::STAR) {
        expressions.push(self.current_value().to_string());
      } else if is_first_expression {
        // We could not find any valid expressions to start the list.
        return Err(
          self.error_at(
            &self.current,
            &format!(
              "Expected an expression list but found '{}'",
              self.current_value()
            )
          )
        );
      } else {
        // We have already parsed "," which must be followed by a valid expression.
        return Err(
          self.error_at(
            &context_token,
            &format!(
              "Expected a valid expression after `,` but found '{}'",
              self.current_value()
            )
          )
        )
      }

      self.advance()?;

      is_first_expression = false;
      context_token = self.current.clone();

      // If the following token is ",", then try to infer the token after, otherwise finish
      // the expression list and exit the loop.
      if !self.matches(TokenType::COMMA)? {
        break;
      }
    }

    Ok(expressions)
  }

  #[inline]
  fn from_statement(&mut self) -> Res<ParsedPlan> {
    // We expect:
    //   [schema].[table]
    //   [table] (implies the currently selected schema)
    if self.check(TokenType::IDENTIFIER) {
      let identifier1 = self.current_value().to_string();
      self.advance()?;

      if self.check(TokenType::DOT) {
        // We have [schema].[table].
        let context_token = self.current.clone();
        self.advance()?;
        // We expect table name after ".".
        if self.check(TokenType::IDENTIFIER) {
          let identifier2 = self.current_value().to_string();
          Ok(ParsedPlan::TableScan(Some(identifier1), identifier2))
        } else {
          Err(
            self.error_at(
              &context_token,
              "Expected a table name after the schema name but no table name was provided"
            )
          )
        }
      } else {
        // We have [table] with the current schema.
        Ok(ParsedPlan::TableScan(None, identifier1.to_string()))
      }
    } else {
      Err(
        self.error_at(
          &self.current,
          &format!(
            "Expected a table name or schema.table qualifier after FROM but found '{}'",
            self.current_value()
          )
        )
      )
    }
  }

  #[inline]
  fn where_statement(&mut self, plan: ParsedPlan) -> Res<ParsedPlan> {
    let expression = self.expression()?;
    Ok(ParsedPlan::Filter(expression, Box::new(plan)))
  }

  #[inline]
  fn limit_statement(&mut self, plan: ParsedPlan) -> Res<ParsedPlan> {
    // LIMIT <number>.
    if self.check(TokenType::NUMBER) {
      match self.current_value().parse() {
        Ok(value) => {
          // Advance and return the limit plan.
          self.advance()?;
          Ok(ParsedPlan::Limit(value, Box::new(plan)))
        },
        Err(_) => {
          // We failed to parse the value into a limit.
          return Err(
            self.error_at(
              &self.current,
              &format!(
                "Expected LIMIT value to be a valid number but found '{}'",
                self.current_value()
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
  fn select_statement(&mut self) -> Res<()> {
    let mut plan = ParsedPlan::Empty;

    // Parse the list of columns for projection.
    let expressions = self.expression_list()?;

    if self.matches(TokenType::FROM)? {
      plan = self.from_statement()?;
    }

    plan = ParsedPlan::Project(expressions, Box::new(plan));

    if self.matches(TokenType::WHERE)? {
      plan = self.where_statement(plan)?;
    }

    if self.matches(TokenType::LIMIT)? {
      plan = self.limit_statement(plan)?;
    }

    println!("Plan: {:?}", plan);

    Ok(())
  }

  #[inline]
  fn statement(&mut self) -> Res<()> {
    if self.matches(TokenType::SELECT)? {
      self.select_statement()
    } else {
      Err(
        self.error_at(
          &self.current,
          &format!("Unsupported token {}", self.current_value())
        )
      )
    }
  }
}

// Returns ParsedPlan instance from the sql string.
pub fn parse(sql: &str) -> Res<Vec<ParsedPlan>> {
  let mut scanner = Scanner::new(sql.as_bytes());
  let token = scanner.next_token();

  let mut parser = Parser {
    sql: sql,
    scanner: scanner,
    current: token,
    plans: Vec::new()
  };

  while !parser.done() {
    parser.statement()?;
  }

  Ok(parser.plans)
}

#[cfg(test)]
pub mod tests {
  use super::*;

  #[test]
  fn test_parser_debug() {
    // let query = "select a, b, c, *
    //   from table
    //   where a > 1 and b = 'abc' or b = 'def'
    //   limit 123";

    // let query = "select a, b, c, *
    //   from table
    //   where b = 'def' or a > 1 and b = 'abc'
    //   limit 123";

    // let query = "select a, b, c, *
    //   from table
    //   where ((b) = ('def') or (a > 1)) and b = 'abc'
    //   limit 123";

    let query = "select a, b, c, *
      from table
      where - -2
      limit 123";

    // let query = "select a, b, c,";

    // let query = "select";

    println!("Query: {}", query);

    let res = match parse(query) {
      Ok(v) => v,
      Err(Error::SQLParseError(ref msg)) => {
        println!("{}", msg);
        panic!();
      },
      err => err.unwrap(),
    };

    println!("Result: {:?}", res);
    assert!(false, "OK");
  }
}