//! Test database.
#![feature(map_first_last)]

#[macro_use]
pub mod util;
#[macro_use]
pub mod error;
pub mod storage;
pub mod cache;
pub mod page;
pub mod btree;
pub mod tree;
pub mod txn;
pub mod db;
