pub mod catalog;
pub mod parser;
pub mod plan;
pub mod scanner;

const DEFAULT_EXPRESSION_NAME: &str = "?col?";
const DEFAULT_SUBQUERY_NAME: &str = "?subquery?";
