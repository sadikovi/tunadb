// use std::fs::File;
// use std::io::Write;
// use std::io::Seek;
// use std::io::SeekFrom;
// use std::fs::OpenOptions;

fn main() {
  // let mut handle = File::create("file.txt").unwrap();
  // handle.write_all(b"Hello, world!").unwrap();
  // handle.sync_all().unwrap();

  // let mut handle = OpenOptions::new().write(true).open("file.txt").unwrap();
  // let mut handle = File::open("file.txt").unwrap();
  // handle.seek(SeekFrom::Start(5)).unwrap();
  // handle.write_all(b"ABC").unwrap();
  // handle.sync_all().unwrap();

  println!("{}", u16::MAX);
  println!("{}", 1 << 16);
}
