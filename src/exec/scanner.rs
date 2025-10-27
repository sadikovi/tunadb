//! Scanner to convert a sequence of characters/bytes into a sequence of tokens.
//! Used internally in parser.

#[allow(non_camel_case_types)]
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum TokenType {
  // 1 character tokens.
  COMMA,
  DOT,
  EQUALS,
  GREATER_THAN,
  LESS_THAN,
  MINUS,
  PAREN_LEFT,
  PAREN_RIGHT,
  PLUS,
  SEMICOLON,
  SLASH,
  STAR,
  VERTICAL_SINGLE,

  // 2+ character tokens.
  GREATER_THAN_EQUALS,
  LESS_THAN_EQUALS,
  VERTICAL_DOUBLE,

  // Literals.
  IDENTIFIER,
  NUMBER,
  STRING,

  // Keywords.
  ALL,
  AND,
  AS,
  BETWEEN,
  BY,
  CASCADE,
  CASE,
  CREATE,
  DISTINCT,
  DROP,
  ELSE,
  END,
  EXISTS,
  FROM,
  GROUP,
  IN,
  INSERT,
  INTO,
  IS,
  LIKE,
  LIMIT,
  NOT,
  NULL,
  OR,
  ORDER,
  SCHEMA,
  SELECT,
  TABLE,
  THEN,
  UNION,
  VALUES,
  WHEN,
  WHERE,
  WITH,

  // Others.
  ERROR,
  EOF
}

// Error messages.
const ERROR_AMBIGUOUS_TRAILING_NUM_LITERAL: &str = "Ambiguous trailing of the numeric literal";
const ERROR_ILLEGAL_CHARACTER: &str = "Illegal character";
const ERROR_UNTERMINATED_IDENTIFIER: &str = "Unterminated identifier";
const ERROR_UNTERMINATED_STRING: &str = "Unterminated string";

// Token that is produced by the scanner.
// It must implement Copy trait as we use it in parser to return tokens
// after advancing the cursor.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct Token {
  tpe: TokenType,
  pos: usize,
  len: usize,
  line_num: usize,
  line_pos: usize,
  err_msg: Option<&'static str>, // only available for TokenType::ERROR
}

impl Token {
  // Returns the token type.
  #[inline]
  pub fn token_type(&self) -> TokenType {
    self.tpe
  }

  // Returns the absolute token starting position from the beginning of the input, 0-based.
  // To calculate the relative position, use `line_pos()` method.
  #[inline]
  pub fn pos(&self) -> usize {
    self.pos
  }

  // Returns the length of the token value.
  #[inline]
  pub fn len(&self) -> usize {
    self.len
  }

  // Returns the line on which the token occurs, 0-based.
  #[inline]
  pub fn line_num(&self) -> usize {
    self.line_num
  }

  // Returns the absolute position at the beginning of the current line.
  #[inline]
  pub fn line_pos(&self) -> usize {
    self.line_pos
  }

  // Returns the string value of the token from the input.
  #[inline]
  pub fn value<'a, 'b>(&'a self, input: &'b str) -> &'b str {
    &input[self.pos..self.pos + self.len]
  }

  // Returns an optional error message.
  // This is only available for tokens with type ERROR.
  #[inline]
  pub fn error_message(&self) -> Option<&str> {
    self.err_msg.as_ref().map(|x| x.as_ref())
  }
}

// Returns true if the byte is an ASCII character from "A" to "Z" or from "a" to "z".
#[inline]
fn is_alpha(c: u8) -> bool {
  c >= b'A' && c <= b'Z' || c >= b'a' && c <= b'z'
}

// Returns true if the byte is a digit from 0 to 9.
#[inline]
fn is_digit(c: u8) -> bool {
  c >= b'0' && c <= b'9'
}

// Scanner to produce tokens from the input string. Implements the Iterator interface to iterate
// over tokens.
//
// Input string can contain more than one statement separated by a semicolon.
// The end of string is indicated by next_token() method returning an "EOF" token.
pub struct Scanner<'a> {
  input: &'a [u8],
  start: usize,
  end: usize,
  line_start: usize,
  line_end: usize,
  line_pos_start: usize, // position that needs to be reported to the user
  line_pos_end: usize, // position at the beginning of the current line
}

impl<'a> Scanner<'a> {
  // Creates a new scanner by wrapping the input string.
  pub fn new(input: &'a [u8]) -> Self {
    Self {
      input,
      start: 0,
      end: 0,
      line_start: 0,
      line_end: 0,
      line_pos_start: 0,
      line_pos_end: 0
    }
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
          self.line_end += 1;
          self.line_pos_end = self.end + 1; // skip the new line character
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
  fn _new_token(&self, tpe: TokenType, msg: Option<&'static str>) -> Token {
    Token {
      tpe,
      pos: self.start,
      len: self.end - self.start,
      line_num: self.line_start,
      line_pos: self.line_pos_start,
      err_msg: msg
    }
  }

  #[inline]
  fn make_token(&self, tpe: TokenType) -> Token {
    self._new_token(tpe, None)
  }

  #[inline]
  fn error_token(&self, msg: &'static str) -> Token {
    self._new_token(TokenType::ERROR, Some(msg))
  }

  #[inline]
  fn match_keyword(&self, expected: &[u8]) -> bool {
    expected.eq_ignore_ascii_case(&self.input[self.start..self.end])
  }

  #[inline]
  fn identifier_type(&self) -> TokenType {
    // We have already consumed the identifier, we just need to match the string.
    if self.match_keyword(b"ALL") {
      TokenType::ALL
    } else if self.match_keyword(b"AND") {
      TokenType::AND
    } else if self.match_keyword(b"AS") {
      TokenType::AS
    } else if self.match_keyword(b"BETWEEN") {
      TokenType::BETWEEN
    } else if self.match_keyword(b"BY") {
      TokenType::BY
    } else if self.match_keyword(b"CASCADE") {
      TokenType::CASCADE
    } else if self.match_keyword(b"CASE") {
      TokenType::CASE
    } else if self.match_keyword(b"CREATE") {
      TokenType::CREATE
    } else if self.match_keyword(b"DISTINCT") {
      TokenType::DISTINCT
    } else if self.match_keyword(b"DROP") {
      TokenType::DROP
    } else if self.match_keyword(b"ELSE") {
      TokenType::ELSE
    } else if self.match_keyword(b"END") {
      TokenType::END
    } else if self.match_keyword(b"EXISTS") {
      TokenType::EXISTS
    } else if self.match_keyword(b"FROM") {
      TokenType::FROM
    } else if self.match_keyword(b"GROUP") {
      TokenType::GROUP
    } else if self.match_keyword(b"IN") {
      TokenType::IN
    } else if self.match_keyword(b"INSERT") {
      TokenType::INSERT
    } else if self.match_keyword(b"INTO") {
      TokenType::INTO
    } else if self.match_keyword(b"IS") {
      TokenType::IS
    } else if self.match_keyword(b"LIKE") {
      TokenType::LIKE
    } else if self.match_keyword(b"LIMIT") {
      TokenType::LIMIT
    } else if self.match_keyword(b"NOT") {
      TokenType::NOT
    } else if self.match_keyword(b"NULL") {
      TokenType::NULL
    } else if self.match_keyword(b"OR") {
      TokenType::OR
    } else if self.match_keyword(b"ORDER") {
      TokenType::ORDER
    } else if self.match_keyword(b"SCHEMA") {
      TokenType::SCHEMA
    } else if self.match_keyword(b"SELECT") {
      TokenType::SELECT
    } else if self.match_keyword(b"TABLE") {
      TokenType::TABLE
    } else if self.match_keyword(b"THEN") {
      TokenType::THEN
    } else if self.match_keyword(b"UNION") {
      TokenType::UNION
    } else if self.match_keyword(b"VALUES") {
      TokenType::VALUES
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

  // Extracts the escaped identifier that is wrapped with double quotes (") and can contain any
  // characters.
  // A double quote can be escaped by placing another one in front of it, e.g. "".
  #[inline]
  fn escaped_identifier(&mut self) -> Token {
    while !self.done() {
      match self.peek() {
        b'\n' => {
          // Increment the scanner line if the identifier spans multiple lines.
          self.line_end += 1;
          self.line_pos_end = self.end + 1; // skip the new line character
          self.advance();
        },
        b'"' => {
          match self.peek_next() {
            Some(b'"') => {
              self.advance();
              self.consume(b'"');
            },
            _ => break,
          }
        },
        _ => {
          self.advance();
        },
      }
    }

    if self.done() {
      self.error_token(ERROR_UNTERMINATED_IDENTIFIER)
    } else {
      // Move over the closing double quote.
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
        return self.error_token(ERROR_AMBIGUOUS_TRAILING_NUM_LITERAL);
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
          return self.error_token(ERROR_AMBIGUOUS_TRAILING_NUM_LITERAL);
        }
      } else if self.consume(b'+') {
        if self.done() || !is_digit(self.peek()) {
          return self.error_token(ERROR_AMBIGUOUS_TRAILING_NUM_LITERAL);
        }
      } else {
        if self.done() || !is_digit(self.peek()) {
          return self.error_token(ERROR_AMBIGUOUS_TRAILING_NUM_LITERAL);
        }
      }
      while !self.done() && is_digit(self.peek()) {
        self.advance();
      }
    }

    self.make_token(TokenType::NUMBER)
  }

  // Extracts string is wrapped with single quotes (').
  // A single quote can be escaped by placing another one in front of it, e.g. ''.
  #[inline]
  fn string(&mut self) -> Token {
    while !self.done() {
      match self.peek() {
        b'\n' => {
          // Increment the scanner line if the string spans multiple lines.
          self.line_end += 1;
          self.line_pos_end = self.end + 1; // skip the new line character
          self.advance();
        },
        b'\'' => {
          match self.peek_next() {
            Some(b'\'') => {
              self.advance();
              self.consume(b'\'');
            },
            _ => break,
          }
        },
        _ => {
          self.advance();
        },
      }
    }

    if self.done() {
      self.error_token(ERROR_UNTERMINATED_STRING)
    } else {
      // Move over the closing quote.
      self.advance();
      self.make_token(TokenType::STRING)
    }
  }


  // Returns the next parsed token.
  //
  // The end of stream is indicated by EOF token.
  // Once EOF is reached, the same EOF token will be returned.
  pub fn next_token(&mut self) -> Token {
    loop {
      self.skip_whitespace();

      self.start = self.end;
      self.line_start = self.line_end;
      self.line_pos_start = self.line_pos_end;

      if self.done() {
        return self.make_token(TokenType::EOF);
      }

      match self.advance() {
        c if is_alpha(c) => return self.identifier(),
        c if is_digit(c) => return self.number(),
        b'.' => return self.make_token(TokenType::DOT),
        b',' => return self.make_token(TokenType::COMMA),
        b';' => return self.make_token(TokenType::SEMICOLON),
        b'(' => return self.make_token(TokenType::PAREN_LEFT),
        b')' => return self.make_token(TokenType::PAREN_RIGHT),
        b'=' => return self.make_token(TokenType::EQUALS),
        b'*' => return self.make_token(TokenType::STAR),
        b'+' => return self.make_token(TokenType::PLUS),
        b'-' => return self.make_token(TokenType::MINUS),
        b'/' => return self.make_token(TokenType::SLASH),
        b'>' => match self.consume(b'=') {
          true => return self.make_token(TokenType::GREATER_THAN_EQUALS),
          false => return self.make_token(TokenType::GREATER_THAN),
        },
        b'<' => match self.consume(b'=') {
          true => return self.make_token(TokenType::LESS_THAN_EQUALS),
          false => return self.make_token(TokenType::LESS_THAN),
        },
        b'|' => match self.consume(b'|') {
          true => return self.make_token(TokenType::VERTICAL_DOUBLE),
          false => return self.make_token(TokenType::VERTICAL_SINGLE),
        },
        b'\'' => return self.string(),
        b'"' => return self.escaped_identifier(),
        _ => return self.error_token(ERROR_ILLEGAL_CHARACTER),
      }
    }
  }
}

#[cfg(test)]
pub mod tests {
  use super::*;

  // Parses the input string and returns the list of tokens.
  fn collect_tokens(input: &str) -> Vec<Token> {
    let mut tokens = Vec::new();
    let mut scanner = Scanner::new(&input.as_bytes());
    loop {
      let token = scanner.next_token();
      if token.token_type() == TokenType::EOF {
        break;
      }
      tokens.push(token);
    }
    tokens
  }

  // Asserts that the list of tokens matches the expected output.
  fn assert_sql(input: &str, expected: Vec<(TokenType, &str)>) {
    let tokens = collect_tokens(input);
    let mut res = Vec::new();
    for token in tokens {
      res.push((token.tpe, token.value(&input)));
    }
    assert_eq!(res, expected);
  }

  #[test]
  fn test_scanner_multiline() {
    let query = "
select
       l_returnflag,
       l_linestatus,
       sum(l_quantity) as sum_qty,
       sum(l_extendedprice) as sum_base_price,


       sum(l_extendedprice * (1-l_discount)) as sum_disc_price,
       sum(l_extendedprice * (1-l_discount) * (1+l_tax)) as sum_charge,
       avg(l_quantity) as avg_qty,
       avg(l_extendedprice) as avg_price,
       avg(l_discount) as avg_disc,
       count(*) as count_order
-- comment with new lines \\n \n \n
from
       lineitem
  where
       l_shipdate <= dateadd(day, -90, to_date('1998-12-01'))
       and l_linestatus =
       'status1
        status2'
    group by
       l_returnflag,
       l_linestatus
    order by
       l_returnflag,
       l_linestatus;
    ";

    let tokens = collect_tokens(query);
    // Check that there are no errors during parsing.
    for token in &tokens {
      assert_ne!(token.tpe, TokenType::ERROR);
    }

    // SELECT token.
    let token = &tokens[0];
    assert_eq!(token.token_type(), TokenType::SELECT);
    assert_eq!(token.line_num(), 1);
    assert_eq!(token.line_pos(), 1);
    assert_eq!(&query[token.line_pos()..token.pos() + token.len], "select");

    // FROM token.
    let token = &tokens[78];
    assert_eq!(token.token_type(), TokenType::FROM);
    assert_eq!(token.line_num(), 17);
    assert_eq!(token.line_pos(), 447);
    assert_eq!(&query[token.line_pos()..token.pos() + token.len], "from");

    // WHERE token.
    let token = &tokens[80];
    assert_eq!(token.token_type(), TokenType::WHERE);
    assert_eq!(token.line_num(), 19);
    assert_eq!(token.line_pos(), 468);
    assert_eq!(&query[token.line_pos()..token.pos() + token.len], "  where");

    // Multiline string.
    let token = &tokens[98];
    assert_eq!(token.token_type(), TokenType::STRING);
    assert_eq!(token.line_num(), 22);
    assert_eq!(token.line_pos(), 564);
    assert_eq!(
      &query[token.line_pos()..token.pos() + token.len],
      "       'status1\n        status2'"
    );

    // GROUP token.
    let token = &tokens[99];
    assert_eq!(token.token_type(), TokenType::GROUP);
    assert_eq!(token.line_num(), 24);
    assert_eq!(token.line_pos(), 597);
    assert_eq!(&query[token.line_pos()..token.pos() + token.len], "    group");

    // BY token.
    let token = &tokens[100];
    assert_eq!(token.token_type(), TokenType::BY);
    assert_eq!(token.line_num(), 24);
    assert_eq!(token.line_pos(), 597);
    assert_eq!(&query[token.line_pos()..token.pos() + token.len], "    group by");

    // SEMICOLON token.
    let token = &tokens[109];
    assert_eq!(token.token_type(), TokenType::SEMICOLON);
    assert_eq!(token.line_num(), 29);
    assert_eq!(token.line_pos(), 685);
    assert_eq!(&query[token.line_pos()..token.pos() + token.len], "       l_linestatus;");
  }

  #[test]
  fn test_scanner_end_of_file() {
    let input = ";";
    let mut scanner = Scanner::new(&input.as_bytes());

    // Skip semicolon, we just assert the correct token type.
    let token = scanner.next_token();
    assert_eq!(token.token_type(), TokenType::SEMICOLON);

    let token = scanner.next_token();
    assert_eq!(token.token_type(), TokenType::EOF);
    assert_eq!(token.pos(), 1);
    assert_eq!(token.line_num(), 0);
    assert_eq!(token.value(input), "");

    // Once EOF has been reached, assert that we return the same token again.
    let token = scanner.next_token();
    assert_eq!(token.token_type(), TokenType::EOF);
    assert_eq!(token.pos(), 1);
    assert_eq!(token.line_num(), 0);
    assert_eq!(token.value(input), "");
  }

  #[test]
  fn test_scanner_comments() {
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
  fn test_scanner_strings() {
    // Positive cases.
    assert_sql(r"''", vec![(TokenType::STRING, r"''")]);
    assert_sql(r"'abc'", vec![(TokenType::STRING, r"'abc'")]);
    assert_sql(r"'abc''abc'", vec![(TokenType::STRING, r"'abc''abc'")]);
    assert_sql(r"'abc\'", vec![(TokenType::STRING, r"'abc\'")]);
    assert_sql(r"'abc\\\abc'", vec![(TokenType::STRING, r"'abc\\\abc'")]);
    assert_sql(r"'abc\abc\n\'", vec![(TokenType::STRING, r"'abc\abc\n\'")]);
    assert_sql(r"''''", vec![(TokenType::STRING, r"''''")]);
    assert_sql(r"' '' '' '", vec![(TokenType::STRING, r"' '' '' '")]);

    // Negative cases.
    assert_sql(r"'abc", vec![(TokenType::ERROR, r"'abc")]);
    assert_sql(r"'''", vec![(TokenType::ERROR, r"'''")]);
  }

  #[test]
  fn test_scanner_numbers() {
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
  fn test_scanner_special_chars() {
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
  fn test_scanner_identifiers() {
    assert_sql("abc", vec![(TokenType::IDENTIFIER, "abc")]);
    assert_sql("a123", vec![(TokenType::IDENTIFIER, "a123")]);
    assert_sql("a1_a2", vec![(TokenType::IDENTIFIER, "a1_a2")]);
    assert_sql("_a123", vec![(TokenType::ERROR, "_"), (TokenType::IDENTIFIER, "a123")]);
    assert_sql(
      "a-b",
      vec![
        (TokenType::IDENTIFIER, "a"),
        (TokenType::MINUS, "-"),
        (TokenType::IDENTIFIER, "b")
      ]
    );

    // Escaped identifiers
    assert_sql("\"abc\"", vec![(TokenType::IDENTIFIER, "\"abc\"")]);
    assert_sql("\"a b c\"", vec![(TokenType::IDENTIFIER, "\"a b c\"")]);
    assert_sql("\"a ' b\"", vec![(TokenType::IDENTIFIER, "\"a ' b\"")]);
    assert_sql("\"\"", vec![(TokenType::IDENTIFIER, "\"\"")]);
    assert_sql("\" \"\" \"", vec![(TokenType::IDENTIFIER, "\" \"\" \"")]);

    assert_sql("\"\"\"", vec![(TokenType::ERROR, "\"\"\"")]);
  }

  #[test]
  fn test_scanner_keywords() {
    // We parse "schema" name as SCHEMA token even if it comes after FROM.
    assert_sql(
      "select * from schema",
      vec![
        (TokenType::SELECT, "select"),
        (TokenType::STAR, "*"),
        (TokenType::FROM, "from"),
        (TokenType::SCHEMA, "schema"),
      ]
    );

    // We parse "table" name as TABLE token even if it comes after FROM.
    assert_sql(
      "select * from table",
      vec![
        (TokenType::SELECT, "select"),
        (TokenType::STAR, "*"),
        (TokenType::FROM, "from"),
        (TokenType::TABLE, "table"),
      ]
    );
  }

  #[test]
  fn test_scanner_sql1() {
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
  fn test_scanner_sql2() {
    assert_sql(
      "select a as \"a b c\"\" d e\" from table0",
      vec![
        (TokenType::SELECT, "select"),
        (TokenType::IDENTIFIER, "a"),
        (TokenType::AS, "as"),
        (TokenType::IDENTIFIER, "\"a b c\"\" d e\""),
        (TokenType::FROM, "from"),
        (TokenType::IDENTIFIER, "table0"),
      ]
    );
  }

  #[test]
  fn test_scanner_sql3() {
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
  fn test_scanner_sql4() {
    assert_sql(
      r"

        -- multiline strings
        select 1 from table0 where t = 'line1
          line2
        line3''
            line4\
        line5
        line6
        line7''line8
        '
      ",
      vec![
        (TokenType::SELECT, "select"),
        (TokenType::NUMBER, "1"),
        (TokenType::FROM, "from"),
        (TokenType::IDENTIFIER, "table0"),
        (TokenType::WHERE, "where"),
        (TokenType::IDENTIFIER, "t"),
        (TokenType::EQUALS, "="),
        (TokenType::STRING, r"'line1
          line2
        line3''
            line4\
        line5
        line6
        line7''line8
        '"),
      ]
    );
  }

  #[test]
  fn test_scanner_sql5() {
    assert_sql(
      r"select a from table0 where a >= 1 and b <= 2;",
      vec![
        (TokenType::SELECT, "select"),
        (TokenType::IDENTIFIER, "a"),
        (TokenType::FROM, "from"),
        (TokenType::IDENTIFIER, "table0"),
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
    );
  }

  #[test]
  fn test_scanner_sql6() {
    assert_sql(
      r"select * from table0 where a is null or b is null group by a order by a",
      vec![
        (TokenType::SELECT, "select"),
        (TokenType::STAR, "*"),
        (TokenType::FROM, "from"),
        (TokenType::IDENTIFIER, "table0"),
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
    );
  }

  #[test]
  fn test_scanner_create1() {
    assert_sql(
      "create schema test_schema;",
      vec![
        (TokenType::CREATE, "create"),
        (TokenType::SCHEMA, "schema"),
        (TokenType::IDENTIFIER, "test_schema"),
        (TokenType::SEMICOLON, ";"),
      ]
    );
  }

  #[test]
  fn test_scanner_create2() {
    assert_sql(
      "create table test_schema.test_table (c1 int null, c2 int not null, c3 int);",
      vec![
        (TokenType::CREATE, "create"),
        (TokenType::TABLE, "table"),
        (TokenType::IDENTIFIER, "test_schema"),
        (TokenType::DOT, "."),
        (TokenType::IDENTIFIER, "test_table"),
        (TokenType::PAREN_LEFT, "("),
        (TokenType::IDENTIFIER, "c1"),
        (TokenType::IDENTIFIER, "int"),
        (TokenType::NULL, "null"),
        (TokenType::COMMA, ","),
        (TokenType::IDENTIFIER, "c2"),
        (TokenType::IDENTIFIER, "int"),
        (TokenType::NOT, "not"),
        (TokenType::NULL, "null"),
        (TokenType::COMMA, ","),
        (TokenType::IDENTIFIER, "c3"),
        (TokenType::IDENTIFIER, "int"),
        (TokenType::PAREN_RIGHT, ")"),
        (TokenType::SEMICOLON, ";"),
      ]
    );
  }

  #[test]
  fn test_scanner_drop1() {
    assert_sql(
      "drop schema test_schema cascade;",
      vec![
        (TokenType::DROP, "drop"),
        (TokenType::SCHEMA, "schema"),
        (TokenType::IDENTIFIER, "test_schema"),
        (TokenType::CASCADE, "cascade"),
        (TokenType::SEMICOLON, ";"),
      ]
    );
  }

  #[test]
  fn test_scanner_drop2() {
    assert_sql(
      "drop table test_schema.test_table;",
      vec![
        (TokenType::DROP, "drop"),
        (TokenType::TABLE, "table"),
        (TokenType::IDENTIFIER, "test_schema"),
        (TokenType::DOT, "."),
        (TokenType::IDENTIFIER, "test_table"),
        (TokenType::SEMICOLON, ";"),
      ]
    );
  }

  #[test]
  fn test_scanner_insert1() {
    assert_sql(
      "insert into t1 (a, b, c) values (1, 2, 3), (4, 5, 6);",
      vec![
        (TokenType::INSERT, "insert"),
        (TokenType::INTO, "into"),
        (TokenType::IDENTIFIER, "t1"),
        (TokenType::PAREN_LEFT, "("),
        (TokenType::IDENTIFIER, "a"),
        (TokenType::COMMA, ","),
        (TokenType::IDENTIFIER, "b"),
        (TokenType::COMMA, ","),
        (TokenType::IDENTIFIER, "c"),
        (TokenType::PAREN_RIGHT, ")"),
        (TokenType::VALUES, "values"),
        (TokenType::PAREN_LEFT, "("),
        (TokenType::NUMBER, "1"),
        (TokenType::COMMA, ","),
        (TokenType::NUMBER, "2"),
        (TokenType::COMMA, ","),
        (TokenType::NUMBER, "3"),
        (TokenType::PAREN_RIGHT, ")"),
        (TokenType::COMMA, ","),
        (TokenType::PAREN_LEFT, "("),
        (TokenType::NUMBER, "4"),
        (TokenType::COMMA, ","),
        (TokenType::NUMBER, "5"),
        (TokenType::COMMA, ","),
        (TokenType::NUMBER, "6"),
        (TokenType::PAREN_RIGHT, ")"),
        (TokenType::SEMICOLON, ";"),
      ]
    );
  }

  #[test]
  fn test_scanner_insert2() {
    assert_sql(
      "insert into t1 select a, b, c from t2;",
      vec![
        (TokenType::INSERT, "insert"),
        (TokenType::INTO, "into"),
        (TokenType::IDENTIFIER, "t1"),
        (TokenType::SELECT, "select"),
        (TokenType::IDENTIFIER, "a"),
        (TokenType::COMMA, ","),
        (TokenType::IDENTIFIER, "b"),
        (TokenType::COMMA, ","),
        (TokenType::IDENTIFIER, "c"),
        (TokenType::FROM, "from"),
        (TokenType::IDENTIFIER, "t2"),
        (TokenType::SEMICOLON, ";"),
      ]
    );
  }
}
