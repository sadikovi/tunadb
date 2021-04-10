// open a database or create a new one
// - if directory does not exist -> new database, try to create it
// - if directory exists but does not have a marker file -> not a database directory, cannot open
// - if directory exists, has a marker file and no lock file -> existing database, open it
// - if directory exists, has a marker file, and has a lock file -> existing database, cannot open

mod btree;
mod page;

#[cfg(test)]
mod tests {
  #[test]
  fn it_works() {
    assert_eq!(2 + 2, 4);
  }
}
