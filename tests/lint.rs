use std::fs;
use std::path::Path;

fn check_files(dir: &Path, errors: &mut Vec<String>) {
  for entry in fs::read_dir(dir).unwrap() {
    let path = entry.unwrap().path();
    if path.is_dir() {
      check_files(&path, errors);
    } else if path.extension().map_or(false, |ext| ext == "rs") {
      let content = fs::read_to_string(&path).unwrap();
      for (line_num, line) in content.lines().enumerate() {
        let line_num = line_num + 1;
        if line.len() > 100 {
          errors.push(
            format!("{}:{}: line exceeds 100 chars ({})", path.display(), line_num, line.len())
          );
        }
        let indent = line.len() - line.trim_start_matches(' ').len();
        if indent % 2 != 0 {
          errors.push(
            format!(
              "{}:{}: indentation is not a multiple of 2 ({} spaces)",
              path.display(), line_num, indent
            )
          );
        }
        if line.starts_with('\t') {
          errors.push(format!("{}:{}: tab indentation", path.display(), line_num));
        }
      }
    }
  }
}

#[test]
fn test_lint() {
  let src = Path::new(".");
  let mut errors = Vec::new();
  check_files(src, &mut errors);
  if !errors.is_empty() {
    panic!("lint errors:\n{}", errors.join("\n"));
  }
}
