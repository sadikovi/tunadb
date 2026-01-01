pub mod catalog;
pub mod parser;
pub mod plan;
pub mod row;
pub mod scanner;
pub mod session;
pub mod trees;
pub mod types;

const DEFAULT_EXPRESSION_NAME: &str = "?col?";
const DEFAULT_SUBQUERY_NAME: &str = "?subquery?";
