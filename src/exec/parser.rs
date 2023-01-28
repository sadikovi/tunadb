#[allow(non_camel_case_types)]
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum TokenType {
  // 1 character tokens.
  COMMA, DOT, EQUALS, GREATER_THAN, LESS_THAN, MINUS, PAREN_LEFT, PAREN_RIGHT, PLUS, SEMICOLON,
  SLASH, STAR, VERTICAL_SINGLE,

  // 2+ character tokens.
  GREATER_THAN_EQUALS, LESS_THAN_EQUALS, VERTICAL_DOUBLE,

  // Literals.
  IDENTIFIER, NUMBER, STRING,

  // Keywords.
  AND, AS, BETWEEN, BY, CASE, DISTINCT, ELSE, END, FROM, GROUP, IN, IS, LIKE, LIMIT, NULL, OR,
  ORDER, SELECT, THEN, WHEN, WHERE, WITH,

  // Others.
  ERROR,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Token {
  tpe: TokenType,
  pos: usize,
  len: usize,
  line: usize,
  err_msg: Option<String>, // available for TokenType::ERROR
}

impl Token {
  pub fn token_type(&self) -> TokenType {
    self.tpe
  }

  pub fn value<'a, 'b>(&'a self, input: &'b str) -> &'b str {
    &input[self.pos..self.pos + self.len]
  }
}

#[inline]
fn is_alpha(c: u8) -> bool {
  c >= b'A' && c <= b'Z' || c >= b'a' && c <= b'z'
}

#[inline]
fn is_digit(c: u8) -> bool {
  c >= b'0' && c <= b'9'
}

pub struct Scanner<'a> {
  input: &'a [u8],
  start: usize,
  end: usize,
  line: usize,
}

impl<'a> Scanner<'a> {
  pub fn new(input: &'a [u8]) -> Self {
    Self { input, start: 0, end: 0, line: 0 }
  }

  #[inline]
  fn advance(&mut self) -> u8 {
    let c = self.input[self.end];
    self.end += 1;
    c
  }

  #[inline]
  fn peek(&self) -> u8 {
    self.input[self.end]
  }

  #[inline]
  fn peek_next(&self) -> Option<u8> {
    if self.end < self.input.len() - 1 {
      Some(self.input[self.end + 1])
    } else {
      None
    }
  }

  #[inline]
  fn consume(&mut self, c: u8) -> bool {
    if self.done() || self.peek() != c {
      false
    } else {
      self.advance();
      true
    }
  }

  #[inline]
  fn done(&self) -> bool {
    self.end >= self.input.len()
  }

  #[inline]
  fn skip_whitespace(&mut self) {
    while !self.done() {
      match self.peek() {
        // Skip whitespaces.
        b' ' | b'\r' | b'\t' => {
          self.advance();
        },
        // Skip new lines.
        b'\n' => {
          self.line += 1;
          self.advance();
        },
        // Skip single line comments.
        b'-' => {
          if let Some(b'-') = self.peek_next() {
            while !self.done() && self.peek() != b'\n' {
              self.advance();
            }
          } else {
            return;
          }
        },
        _ => {
          return;
        },
      }
    }
  }

  #[inline]
  fn _new_token(&self, tpe: TokenType, msg: Option<String>) -> Token {
    Token { tpe, pos: self.start, len: self.end - self.start, line: self.line, err_msg: msg }
  }

  #[inline]
  fn make_token(&self, tpe: TokenType) -> Token {
    self._new_token(tpe, None)
  }

  #[inline]
  fn error_token(&self, msg: &str) -> Token {
    self._new_token(TokenType::ERROR, Some(msg.to_string()))
  }

  #[inline]
  fn match_keyword(&self, expected: &[u8]) -> bool {
    expected.eq_ignore_ascii_case(&self.input[self.start..self.end])
  }

  #[inline]
  fn identifier_type(&self) -> TokenType {
    // We have already consumed the identifier, we just need to match the string.
    if self.match_keyword(b"AND") {
      TokenType::AND
    } else if self.match_keyword(b"AS") {
      TokenType::AS
    } else if self.match_keyword(b"BETWEEN") {
      TokenType::BETWEEN
    } else if self.match_keyword(b"BY") {
      TokenType::BY
    } else if self.match_keyword(b"CASE") {
      TokenType::CASE
    } else if self.match_keyword(b"DISTINCT") {
      TokenType::DISTINCT
    } else if self.match_keyword(b"ELSE") {
      TokenType::ELSE
    } else if self.match_keyword(b"END") {
      TokenType::END
    } else if self.match_keyword(b"FROM") {
      TokenType::FROM
    } else if self.match_keyword(b"GROUP") {
      TokenType::GROUP
    } else if self.match_keyword(b"IN") {
      TokenType::IN
    } else if self.match_keyword(b"IS") {
      TokenType::IS
    } else if self.match_keyword(b"LIKE") {
      TokenType::LIKE
    } else if self.match_keyword(b"LIMIT") {
      TokenType::LIMIT
    } else if self.match_keyword(b"NULL") {
      TokenType::NULL
    } else if self.match_keyword(b"OR") {
      TokenType::OR
    } else if self.match_keyword(b"ORDER") {
      TokenType::ORDER
    } else if self.match_keyword(b"SELECT") {
      TokenType::SELECT
    } else if self.match_keyword(b"THEN") {
      TokenType::THEN
    } else if self.match_keyword(b"WHEN") {
      TokenType::WHEN
    } else if self.match_keyword(b"WHERE") {
      TokenType::WHERE
    } else if self.match_keyword(b"WITH") {
      TokenType::WITH
    } else {
      TokenType::IDENTIFIER
    }
  }

  #[inline]
  fn identifier(&mut self) -> Token {
    while !self.done() && (is_alpha(self.peek()) || is_digit(self.peek()) || self.peek() == b'_') {
      self.advance();
    }
    self.make_token(self.identifier_type())
  }

  #[inline]
  fn escaped_identifier(&mut self) -> Token {
    // Escaped identifier is wrapped with backticks (`) and can contain any characters other than
    // backticks.
    while !self.done() {
      match self.peek() {
        b'\n' => {
          // Increment the scanner line if the identifier spans multiple lines.
          self.line += 1;
          self.advance();
        },
        b'\\' => {
          // This is an escaped backtick, consume both.
          self.advance();
          self.consume(b'`');
        },
        b'`' => {
          break;
        },
        _ => {
          self.advance();
        },
      }
    }

    if self.done() {
      self.error_token("Unterminated identifier")
    } else {
      // Move over the closing backtick.
      self.advance();
      self.make_token(TokenType::IDENTIFIER)
    }
  }

  #[inline]
  fn number(&mut self) -> Token {
    while !self.done() && is_digit(self.peek()) {
      self.advance();
    }

    // Check the fractional part.
    if !self.done() && self.consume(b'.') {
      // If "." exists, then the fractional part must follow.
      if self.done() || !is_digit(self.peek()) {
        return self.error_token("Ambiguous trailing of the numeric literal");
      }
      while !self.done() && is_digit(self.peek()) {
        self.advance();
      }
    }

    // Check exponent.
    if !self.done() && (self.consume(b'e') || self.consume(b'E')) {
      // If "e" exists, then the exponent must follow.
      if self.consume(b'-') {
        if self.done() || !is_digit(self.peek()) {
          return self.error_token("Ambiguous trailing of the numeric literal");
        }
      } else if self.consume(b'+') {
        if self.done() || !is_digit(self.peek()) {
          return self.error_token("Ambiguous trailing of the numeric literal");
        }
      } else {
        if self.done() || !is_digit(self.peek()) {
          return self.error_token("Ambiguous trailing of the numeric literal");
        }
      }
      while !self.done() && is_digit(self.peek()) {
        self.advance();
      }
    }

    self.make_token(TokenType::NUMBER)
  }

  #[inline]
  fn string(&mut self) -> Token {
    while !self.done() {
      match self.peek() {
        b'\n' => {
          // Increment the scanner line if the string spans multiple lines.
          self.line += 1;
          self.advance();
        },
        b'\\' => {
          // This is an escaped single quote, consume both the quote and the backslash.
          self.advance();
          self.consume(b'\'');
        },
        b'\'' => {
          break;
        },
        _ => {
          self.advance();
        },
      }
    }

    if self.done() {
      self.error_token("Unterminated string")
    } else {
      // Move over the closing quote.
      self.advance();
      self.make_token(TokenType::STRING)
    }
  }
}

impl<'a> Iterator for Scanner<'a> {
  type Item = Token;

  fn next(&mut self) -> Option<Self::Item> {
    loop {
      self.skip_whitespace();

      self.start = self.end;

      if self.done() {
        return None;
      }

      match self.advance() {
        c if is_alpha(c) => return Some(self.identifier()),
        c if is_digit(c) => return Some(self.number()),
        b'`' => return Some(self.escaped_identifier()),
        b'.' => return Some(self.make_token(TokenType::DOT)),
        b',' => return Some(self.make_token(TokenType::COMMA)),
        b';' => return Some(self.make_token(TokenType::SEMICOLON)),
        b'(' => return Some(self.make_token(TokenType::PAREN_LEFT)),
        b')' => return Some(self.make_token(TokenType::PAREN_RIGHT)),
        b'=' => return Some(self.make_token(TokenType::EQUALS)),
        b'*' => return Some(self.make_token(TokenType::STAR)),
        b'+' => return Some(self.make_token(TokenType::PLUS)),
        b'-' => return Some(self.make_token(TokenType::MINUS)),
        b'/' => return Some(self.make_token(TokenType::SLASH)),
        b'>' => match self.consume(b'=') {
          true => return Some(self.make_token(TokenType::GREATER_THAN_EQUALS)),
          false => return Some(self.make_token(TokenType::GREATER_THAN)),
        },
        b'<' => match self.consume(b'=') {
          true => return Some(self.make_token(TokenType::LESS_THAN_EQUALS)),
          false => return Some(self.make_token(TokenType::LESS_THAN)),
        },
        b'|' => match self.consume(b'|') {
          true => return Some(self.make_token(TokenType::VERTICAL_DOUBLE)),
          false => return Some(self.make_token(TokenType::VERTICAL_SINGLE)),
        },
        b'\'' => return Some(self.string()),
        _ => return Some(self.error_token("Illegal character")),
      }
    }
  }
}

#[cfg(test)]
pub mod tests {
  use super::*;
  use std::fs::File;
  use std::io::Read;

  // Loads a query from the provided file path.
  fn load_query(path: &str) -> String {
    let mut file = File::open(path).unwrap();
    let mut input = String::new();
    file.read_to_string(&mut input).unwrap();
    input
  }

  fn collect_tokens(input: &str) -> Vec<Token> {
    let mut tokens = Vec::new();
    let mut scanner = Scanner::new(&input.as_bytes());
    while let Some(token) = scanner.next() {
      tokens.push(token);
    }
    tokens
  }

  fn assert_sql(input: &str, expected: Vec<(TokenType, &str)>) {
    let tokens = collect_tokens(input);
    let mut res = Vec::new();
    for token in tokens {
      println!("Line {}, {:?}: {}", token.line, token.token_type(), token.value(&input));
      res.push((token.tpe, token.value(&input)));
    }
    assert_eq!(res, expected);
  }

  // #[test]
  // fn test_parser_tpcds() {
  //   for i in 1..100 {
  //     println!("\nQuery {}\n", i);
  //     let input = load_query(&format!("/Users/ivansadikov/developer/tpcds/query{}.sql", i));
  //     let tokens = collect_tokens(&input);
  //     for token in tokens {
  //       if token.tpe == TokenType::IDENTIFIER {
  //         println!("Line {}, {:?}: {}", token.line, token.token_type(), token.value(&input));
  //       }
  //     }
  //   }
  //   //
  //   // for i in &[12, 20, 44, 47, 53, 57, 63, 89, 98] {
  //   //   println!("\nQuery {}\n", i);
  //   //   let input = load_query(&format!("/Users/ivansadikov/developer/tpcds/modified/query{}.sql", i));
  //   //   check(&input);
  //   // }
  //
  //   assert!(false, "OK");
  // }

  #[test]
  fn test_parser_comments() {
    assert_sql(
      "--comment 1 + 2",
      vec![]
    );
    assert_sql(
      "-- 1 + 2",
      vec![]
    );
    assert_sql(
      "1 -- 2",
      vec![(TokenType::NUMBER, "1")]
    );
  }

  #[test]
  fn test_parser_strings() {
    // Positive cases.
    assert_sql(r"''", vec![(TokenType::STRING, r"''")]);
    assert_sql(r"'abc'", vec![(TokenType::STRING, r"'abc'")]);
    assert_sql(r"'abc\'abc'", vec![(TokenType::STRING, r"'abc\'abc'")]);
    assert_sql(r"'abc\'abc\n\''", vec![(TokenType::STRING, r"'abc\'abc\n\''")]);

    // Negative cases.
    assert_sql(r"'abc", vec![(TokenType::ERROR, r"'abc")]);
  }

  #[test]
  fn test_parser_numbers() {
    assert_sql("123", vec![(TokenType::NUMBER, "123")]);
    assert_sql("1.23", vec![(TokenType::NUMBER, "1.23")]);
    assert_sql("-123", vec![(TokenType::MINUS, "-"), (TokenType::NUMBER, "123")]);
    assert_sql("-1.23", vec![(TokenType::MINUS, r"-"), (TokenType::NUMBER, "1.23")]);
    assert_sql("+123", vec![(TokenType::PLUS, "+"), (TokenType::NUMBER, "123")]);
    assert_sql("+1.23", vec![(TokenType::PLUS, "+"), (TokenType::NUMBER, "1.23")]);
    assert_sql("-988e3", vec![(TokenType::MINUS, "-"), (TokenType::NUMBER, "988e3")]);
    assert_sql("+988E3", vec![(TokenType::PLUS, "+"), (TokenType::NUMBER, "988E3")]);
    assert_sql("-1.23e3", vec![(TokenType::MINUS, "-"), (TokenType::NUMBER, "1.23e3")]);
    assert_sql("-1.23E3", vec![(TokenType::MINUS, "-"), (TokenType::NUMBER, "1.23E3")]);
    assert_sql("-0.99e-12", vec![(TokenType::MINUS, "-"), (TokenType::NUMBER, "0.99e-12")]);
    assert_sql("-0.99E-12", vec![(TokenType::MINUS, "-"), (TokenType::NUMBER, "0.99E-12")]);
    assert_sql("+2.785e+12", vec![(TokenType::PLUS, "+"), (TokenType::NUMBER, "2.785e+12")]);
    assert_sql("+2.785E+12", vec![(TokenType::PLUS, "+"), (TokenType::NUMBER, "2.785E+12")]);

    assert_sql(
      "3 - 2",
      vec![
        (TokenType::NUMBER, "3"),
        (TokenType::MINUS, "-"),
        (TokenType::NUMBER, "2")
      ]
    );
    assert_sql(
      "3-2",
      vec![
        (TokenType::NUMBER, "3"),
        (TokenType::MINUS, "-"),
        (TokenType::NUMBER, "2")
      ]
    );

    assert_sql(
      "-1.23e12.3",
      vec![
        (TokenType::MINUS, "-"),
        (TokenType::NUMBER, "1.23e12"),
        (TokenType::DOT, "."),
        (TokenType::NUMBER, "3")
      ]
    );
    assert_sql(
      "-1.23e12-3",
      vec![
        (TokenType::MINUS, "-"),
        (TokenType::NUMBER, "1.23e12"),
        (TokenType::MINUS, "-"),
        (TokenType::NUMBER, "3")
      ]
    );

    assert_sql("-12.", vec![(TokenType::MINUS, "-"), (TokenType::ERROR, "12.")]);
    assert_sql("-12e", vec![(TokenType::MINUS, "-"), (TokenType::ERROR, "12e")]);
    assert_sql(
      "-12.e",
      vec![
        (TokenType::MINUS, "-"),
        (TokenType::ERROR, "12."),
        (TokenType::IDENTIFIER, "e")
      ]
    );
  }

  #[test]
  fn test_parser_special_chars() {
    assert_sql(">", vec![(TokenType::GREATER_THAN, ">")]);
    assert_sql("<", vec![(TokenType::LESS_THAN, "<")]);
    assert_sql(">=", vec![(TokenType::GREATER_THAN_EQUALS, ">=")]);
    assert_sql("<=", vec![(TokenType::LESS_THAN_EQUALS, "<=")]);
    assert_sql("> =", vec![(TokenType::GREATER_THAN, ">"), (TokenType::EQUALS, "=")]);
    assert_sql("< =", vec![(TokenType::LESS_THAN, "<"), (TokenType::EQUALS, "=")]);
    assert_sql("()", vec![(TokenType::PAREN_LEFT, "("), (TokenType::PAREN_RIGHT, ")")]);
    assert_sql("/", vec![(TokenType::SLASH, "/")]);
    assert_sql("|", vec![(TokenType::VERTICAL_SINGLE, "|")]);
    assert_sql("||", vec![(TokenType::VERTICAL_DOUBLE, "||")]);
    assert_sql("| |", vec![(TokenType::VERTICAL_SINGLE, "|"), (TokenType::VERTICAL_SINGLE, "|")]);
  }

  #[test]
  fn test_parser_sql1() {
    assert_sql(
      r"
        -- comment
        select a where a >
      ",
      vec![
        (TokenType::SELECT, "select"),
        (TokenType::IDENTIFIER, "a"),
        (TokenType::WHERE, "where"),
        (TokenType::IDENTIFIER, "a"),
        (TokenType::GREATER_THAN, ">"),
      ]
    );
  }


  #[test]
  fn test_parser_sql2() {
    assert_sql(
      r"select a as `a b c\` d e` from table",
      vec![
        (TokenType::SELECT, "select"),
        (TokenType::IDENTIFIER, "a"),
        (TokenType::AS, "as"),
        (TokenType::IDENTIFIER, r"`a b c\` d e`"),
        (TokenType::FROM, "from"),
        (TokenType::IDENTIFIER, "table"),
      ]
    );
  }

  #[test]
  fn test_parser_sql3() {
    assert_sql(
      r"select 3.3e3, -1.2;",
      vec![
        (TokenType::SELECT, "select"),
        (TokenType::NUMBER, "3.3e3"),
        (TokenType::COMMA, ","),
        (TokenType::MINUS, "-"),
        (TokenType::NUMBER, "1.2"),
        (TokenType::SEMICOLON, ";"),
      ]
    );
  }

  #[test]
  fn test_parser_sql4() {
    assert_sql(
      r"

        -- multiline strings
        select 1 from table where t = 'line1
          line2
        line3\'
            line4\
        line5
        line6
        line7\'line8
        '
      ",
      vec![
        (TokenType::SELECT, "select"),
        (TokenType::NUMBER, "1"),
        (TokenType::FROM, "from"),
        (TokenType::IDENTIFIER, "table"),
        (TokenType::WHERE, "where"),
        (TokenType::IDENTIFIER, "t"),
        (TokenType::EQUALS, "="),
        (TokenType::STRING, r"'line1
          line2
        line3\'
            line4\
        line5
        line6
        line7\'line8
        '"),
      ]
    )
  }

  #[test]
  fn test_parser_sql5() {
    assert_sql(
      r"select a from table where a >= 1 and b <= 2;",
      vec![
        (TokenType::SELECT, "select"),
        (TokenType::IDENTIFIER, "a"),
        (TokenType::FROM, "from"),
        (TokenType::IDENTIFIER, "table"),
        (TokenType::WHERE, "where"),
        (TokenType::IDENTIFIER, "a"),
        (TokenType::GREATER_THAN_EQUALS, ">="),
        (TokenType::NUMBER, "1"),
        (TokenType::AND, "and"),
        (TokenType::IDENTIFIER, "b"),
        (TokenType::LESS_THAN_EQUALS, "<="),
        (TokenType::NUMBER, "2"),
        (TokenType::SEMICOLON, ";"),
      ]
    )
  }

  #[test]
  fn test_parser_sql6() {
    assert_sql(
      r"select * from table where a is null or b is null group by a order by a",
      vec![
        (TokenType::SELECT, "select"),
        (TokenType::STAR, "*"),
        (TokenType::FROM, "from"),
        (TokenType::IDENTIFIER, "table"),
        (TokenType::WHERE, "where"),
        (TokenType::IDENTIFIER, "a"),
        (TokenType::IS, "is"),
        (TokenType::NULL, "null"),
        (TokenType::OR, "or"),
        (TokenType::IDENTIFIER, "b"),
        (TokenType::IS, "is"),
        (TokenType::NULL, "null"),
        (TokenType::GROUP, "group"),
        (TokenType::BY, "by"),
        (TokenType::IDENTIFIER, "a"),
        (TokenType::ORDER, "order"),
        (TokenType::BY, "by"),
        (TokenType::IDENTIFIER, "a"),
      ]
    )
  }
}
