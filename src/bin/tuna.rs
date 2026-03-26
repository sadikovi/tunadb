use std::io::{self, Write};
use tunadb::api::{Database, QueryResult};
use tunadb::sql::row::Row;
use tunadb::sql::types::{Fields, Type};

fn main() {
  let path = std::env::args().nth(1);
  let path_display = path.as_deref().unwrap_or(":memory:");

  let mut db = match Database::open(path.as_deref()) {
    Ok(db) => db,
    Err(e) => {
      eprintln!("Error opening database: {}", e);
      std::process::exit(1);
    }
  };

  println!("tunadb ({})", path_display);
  println!("Type \".help\" for usage hints.");
  println!();

  repl(&mut db);
}

fn repl(db: &mut Database) {
  let mut buf = String::new();

  loop {
    let prompt = if buf.is_empty() { "tuna> " } else { "   -> " };
    print!("{}", prompt);
    io::stdout().flush().unwrap();

    let mut line = String::new();
    match io::stdin().read_line(&mut line) {
      Ok(0) => break, // EOF (Ctrl-D)
      Ok(_) => {}
      Err(e) => { eprintln!("Error reading input: {}", e); break; }
    }

    let trimmed = line.trim();

    // Dot commands are single-line and don't require a semicolon.
    if buf.is_empty() && trimmed.starts_with('.') {
      match trimmed {
        ".quit" | ".exit" => { println!("Bye."); break; }
        ".help" => print_help(),
        other => println!("Unknown command: {}. Try \".help\".", other),
      }
      continue;
    }

    buf.push_str(&line);

    // Execute once we see a semicolon at the end of the trimmed input.
    if trimmed.ends_with(';') {
      let sql = buf.trim().trim_end_matches(';').trim();
      if !sql.is_empty() {
        run_sql(db, sql);
      }
      buf.clear();
    }
  }
}

fn run_sql(db: &mut Database, sql: &str) {
  match db.with_transaction(|txn| txn.execute(sql)) {
    Ok(result) => print_result(result),
    Err(e) => println!("Error: {}", e),
  }
}

fn print_result(result: QueryResult) {
  let fields = result.fields;
  let rows: Vec<Row> = result.rows
    .map(|r| r.expect("row error"))
    .collect();

  if fields.get().is_empty() {
    println!("OK");
    return;
  }

  // Collect cell strings.
  let headers: Vec<String> = fields.get().iter().map(|f| f.name().to_string()).collect();
  let cells: Vec<Vec<String>> = rows.iter()
    .map(|row| (0..fields.get().len()).map(|i| cell_value(row, &fields, i)).collect())
    .collect();

  // Calculate column widths.
  let mut widths: Vec<usize> = headers.iter().map(|h| h.len()).collect();
  for row_cells in &cells {
    for (i, cell) in row_cells.iter().enumerate() {
      widths[i] = widths[i].max(cell.len());
    }
  }

  // Header row.
  let header_line: Vec<String> = headers.iter().enumerate()
    .map(|(i, h)| format!(" {:<width$} ", h, width = widths[i]))
    .collect();
  println!("{}", header_line.join("|"));

  // Separator.
  let sep: Vec<String> = widths.iter().map(|w| "-".repeat(w + 2)).collect();
  println!("{}", sep.join("+"));

  // Data rows.
  for row_cells in &cells {
    let row_line: Vec<String> = row_cells.iter().enumerate()
      .map(|(i, c)| format!(" {:<width$} ", c, width = widths[i]))
      .collect();
    println!("{}", row_line.join("|"));
  }

  // Row count.
  let n = cells.len();
  println!();
  println!("({} {})", n, if n == 1 { "row" } else { "rows" });
}

fn cell_value(row: &Row, fields: &Fields, i: usize) -> String {
  if row.is_null(i) {
    return "NULL".to_string();
  }
  match fields.get()[i].data_type() {
    Type::BOOL => row.get_bool(i).to_string(),
    Type::INT => row.get_i32(i).to_string(),
    Type::BIGINT => row.get_i64(i).to_string(),
    Type::FLOAT => row.get_f32(i).to_string(),
    Type::DOUBLE => row.get_f64(i).to_string(),
    Type::TEXT => row.get_str(i).to_string(),
    Type::NULL => "NULL".to_string(),
    Type::STRUCT(_) => "<struct>".to_string(),
  }
}

fn print_help() {
  println!("Dot commands:");
  println!("  .help       Show this message.");
  println!("  .quit       Exit the REPL.");
  println!("  .exit       Exit the REPL.");
  println!();
  println!("SQL statements must end with a semicolon (;).");
  println!("Multi-line input is supported — keep typing until you add a semicolon.");
}
