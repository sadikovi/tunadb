use std::io;
use std::io::Write;
use tunadb::storage::db;
use tunadb::storage::txn::{Set, create_set, get_set};

#[derive(Clone, Debug)]
enum Cmd {
  Get(Vec<u8> /* key */),
  Set(Vec<u8> /* key */, Vec<u8> /* val */),
  Del(Vec<u8> /* key */),
  Exists(Vec<u8> /* key */),
  List, // lists all of the keys and values in the database
  Open(String), // opens a database
  DebugDb, // shows debug information for the database
  DebugTable, // shows debug information for the table
  DebugPage, // shows debug information for the page
  Help,
  Quit, // close the repl
  Empty, // empty command, can be ignored
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
      Cmd::Open(key.to_string())
    },
    Some("DEBUG") | Some("debug") => {
      match advance(&mut iter)? {
        "DB" | "db" => {
          finish(&mut iter)?;
          Cmd::DebugDb
        },
        "TABLE" | "table" => {
          finish(&mut iter)?;
          Cmd::DebugTable
        },
        "PAGE" | "page" => {
          finish(&mut iter)?;
          Cmd::DebugPage
        }
        token => return Err(format!("Expected DB, TABLE, or PAGE, found '{}'", token)),
      }
    },
    Some("HELP") | Some("help") => {
      finish(&mut iter)?;
      Cmd::Help
    },
    Some("QUIT") | Some("quit") | Some("EXIT") | Some("exit") => {
      finish(&mut iter)?;
      Cmd::Quit
    },
    Some(_) => Cmd::Unknown,
    None => Cmd::Empty,
  };
  Ok(cmd)
}

fn exec_cmd(curr_db: &mut db::DB, cmd: Cmd) -> Result<bool, String> {
  match &cmd {
    Cmd::Get(key) => {
      let val = with_table(curr_db, |table| {
        table.get(key).map(|v| String::from_utf8(v).unwrap())
      });
      if let Some(v) = val {
        println!("{}", v);
      }
    },
    Cmd::Set(key, val) => {
      with_table(curr_db, |table| {
        table.put(key, val);
      });
      println!("Done.");
    },
    Cmd::Del(key) => {
      with_table(curr_db, |table| {
        table.del(key);
      });
      println!("Done.");
    },
    Cmd::Exists(key) => {
      let exists = with_table(curr_db, |table| {
        table.get(key).is_some()
      });
      println!("{}", exists);
    },
    Cmd::List => {
      with_table(curr_db, |table| {
        let mut iter = table.list(None, None);
        while let Some((key, val)) = iter.next() {
          let key = std::str::from_utf8(&key).unwrap();
          let val = std::str::from_utf8(&val).unwrap();
          println!("{}: {}", key, val);
        }
      });
    },
    Cmd::Open(path) => {
      // Errors are returned in debug output.
      *curr_db = db::open(Some(path)).try_build().map_err(|err| format!("{:?}", err))?;
      println!("Using database {}.", path);
    },
    Cmd::DebugDb => {
      let info = curr_db.stats();

      println!("      page size: {}", info.page_size);
      println!("num total pages: {}", info.num_pages);
      println!(" num free pages: {}", info.num_free_pages);
      println!(" is cache proxy: {}", info.is_proxy_cache);
      println!(" cache mem used: {} bytes", info.cache_mem_used);
      println!("  cache mem max: {} bytes", info.cache_mem_max);
      println!(" cache mem pcnt: {:.2}%", info.cache_mem_used_pcnt());
      println!("     cache hits: {}", info.cache_num_hits);
      println!("   cache misses: {}", info.cache_num_misses);
      println!("cache hit ratio: {:.2}%", info.cache_hit_pcnt());
    },
    Cmd::DebugTable => {
      let info = with_table(curr_db, |table| {
        table.btree_debug()
      });
      println!("{}", info);
    },
    Cmd::DebugPage => {
      // TODO: Add page debugging.
      println!("DebugPage is not implemented");
    },
    Cmd::Help => {
      println!("Available commands:");
      println!("  SET <key> <value>     sets value for the key.");
      println!("  DEL <key>             deletes the key.");
      println!("  GET <key>             returns value for the key if exists.");
      println!("  EXISTS <key>          returns true if the key exists, false otherwise.");
      println!("  LIST                  lists all of the key-value pairs.");
      println!("  OPEN <path>           opens a database at the path.");
      println!("  DEBUG (DB|TABLE|PAGE) shows debug information for the table or database.");
      println!("  HELP                  shows this message.");
      println!("  QUIT|EXIT             quit the REPL.");
      println!();
    },
    Cmd::Quit => {
      return Ok(false);
    }
    Cmd::Empty => {
      // do nothing
    },
    Cmd::Unknown => {
      println!("Unknown command.");
    },
  }
  Ok(true)
}

fn with_table<F, T>(db: &mut db::DB, func: F) -> T where F: Fn(&mut Set) -> T, {
  db.with_txn(true, |txn| {
    let mut table = get_set(&txn, b"kv")
      .unwrap_or_else(|| create_set(&txn, b"kv").unwrap());
    func(&mut table)
  })
}

fn main() {
  println!("=============================");
  println!("Tunadb simple key-value store");
  println!("=============================");
  println!("Type \"help\" command to start.");
  println!();

  let mut curr_db = db::open(None).try_build().unwrap();
  println!("Using an in-memory database.");
  println!();

  let mut input = String::new();
  loop {
    print!("> ");
    io::stdout().flush().unwrap();
    let res = io::stdin().read_line(&mut input)
      .map_err(|err| err.to_string())
      .and_then(|_| parse_cmd(&input))
      .and_then(|cmd| exec_cmd(&mut curr_db, cmd));

    match res {
      Ok(true) => {
        // Do nothing.
      },
      Ok(false) => {
        println!("Bye bye.");
        break;
      },
      Err(err) => {
        println!("Error: {}", err);
      },
    }

    input.clear();
  }
}
