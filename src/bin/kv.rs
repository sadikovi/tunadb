use std::io;
use std::io::Write;
use tunadb::db;
use tunadb::txn::BTree;

#[derive(Clone, Debug)]
enum Cmd {
  Get(Vec<u8> /* key */),
  Set(Vec<u8> /* key */, Vec<u8> /* val */),
  Del(Vec<u8> /* key */),
  Exists(Vec<u8> /* key */),
  List, // lists all of the keys and values in the database
  Open(String), // opens a database
  Help,
  Unknown,
}

fn advance<'a>(iter: &mut dyn Iterator<Item = &'a str>) -> Result<&'a str, String> {
  match iter.next() {
    Some(token) => Ok(token),
    None => Err(format!("Expected the token but no more tokens are available")),
  }
}

fn finish<'a>(iter: &mut dyn Iterator<Item = &'a str>) -> Result<(), String> {
  match iter.next() {
    None => Ok(()),
    Some(token) => Err(format!("Expected the end, found '{}'", token)),
  }
}

fn parse_cmd(cmd: &str) -> Result<Cmd, String> {
  let mut iter = cmd.trim().split(' ').filter(|t| t.len() > 0);
  let cmd = match iter.next() {
    Some("GET") | Some("get") => {
      let key = advance(&mut iter)?;
      finish(&mut iter)?;
      Cmd::Get(key.as_bytes().to_owned())
    },
    Some("SET") | Some("set") => {
      let key = advance(&mut iter)?;
      let val = advance(&mut iter)?;
      finish(&mut iter)?;
      Cmd::Set(key.as_bytes().to_owned(), val.as_bytes().to_owned())
    },
    Some("DEL") | Some ("del") => {
      let key = advance(&mut iter)?;
      finish(&mut iter)?;
      Cmd::Del(key.as_bytes().to_owned())
    },
    Some("EXISTS") | Some("exists") => {
      let key = advance(&mut iter)?;
      finish(&mut iter)?;
      Cmd::Exists(key.as_bytes().to_owned())
    },
    Some("LIST") | Some("list") => {
      finish(&mut iter)?;
      Cmd::List
    },
    Some("OPEN") | Some("open") => {
      let key = advance(&mut iter)?;
      finish(&mut iter)?;
      Cmd::Open(key.to_owned())
    },
    Some("HELP") | Some("help") => {
      finish(&mut iter)?;
      Cmd::Help
    },
    _ => Cmd::Unknown,
  };
  Ok(cmd)
}

fn with_table<F, T>(db: &mut db::DB, func: F) -> T where F: Fn(&mut BTree) -> T, {
  db.with_txn(true, |txn| {
    let mut table = BTree::find("kv", txn.clone())
      .unwrap_or_else(|| BTree::new("kv".to_owned(), txn));
    func(&mut table)
  })
}

fn main() {
  println!("=============================");
  println!("Tunadb simple key-value store");
  println!("=============================");
  println!("Type \"help\" command to start");
  println!();

  let mut curr_db = db::open(None).try_build().unwrap();
  println!("Using an in-memory database");
  println!();

  let mut input = String::new();
  loop {
    print!("> ");
    io::stdout().flush().unwrap();
    match io::stdin().read_line(&mut input)
      .map_err(|err| err.to_string())
      .and_then(|_| parse_cmd(&input)) {
      Ok(cmd) => {
        match &cmd {
          Cmd::Get(key) => {
            let val = with_table(&mut curr_db, |table| {
              table.get(key).map(|v| String::from_utf8(v).unwrap())
            });
            if let Some(v) = val {
              println!("{}", v);
            }
          },
          Cmd::Set(key, val) => {
            with_table(&mut curr_db, |table| {
              table.put(key, val);
            });
            println!("Done.");
          },
          Cmd::Del(key) => {
            with_table(&mut curr_db, |table| {
              table.del(key);
            });
            println!("Done.");
          },
          Cmd::Exists(key) => {
            let exists = with_table(&mut curr_db, |table| {
              table.get(key).is_some()
            });
            println!("{}", exists);
          },
          Cmd::List => {
            with_table(&mut curr_db, |table| {
              let keys = table.list();
              for (key, val) in &keys {
                let key = std::str::from_utf8(key).unwrap();
                let val = std::str::from_utf8(val).unwrap();
                println!("{}: {}", key, val);
              }
            });
          },
          Cmd::Open(path) => {
            match db::open(Some(path)).try_build() {
              Ok(db0) => {
                println!("Switching to database {}", path);
                curr_db = db0;
              },
              Err(err) => {
                println!("Error: {:?}", err.msg());
              }
            }
          },
          Cmd::Help => {
            println!("Available commands:");
            println!("  SET <key> <value>   sets value for the key.");
            println!("  DEL <key>           deletes the key.");
            println!("  GET <key>           returns value for the key if exists.");
            println!("  EXISTS <key>        returns true if the key exists, false otherwise.");
            println!("  LIST                lists all of the key-value pairs.");
            println!("  OPEN <path>         opens a database at the path");
            println!("  HELP                shows this message.");
            println!();
          },
          Cmd::Unknown => {
            println!("Unknown command.");
          }
        };
      },
      Err(error) => {
        println!("Error: {}", error);
      }
    }
    input.clear();
  }
}
