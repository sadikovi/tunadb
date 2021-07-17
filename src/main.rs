use std::thread;
use std::time;

fn main() {
  let t = thread::Builder::new().name("child".to_owned()).spawn(move || {
    let total = time::Duration::from_secs(10);
    let one_sec = time::Duration::from_secs(1);
    let now = time::Instant::now();

    let mut cnt = 0;

    while now.elapsed() <= total {
      println!("{} Running child thread...", cnt);
      cnt += 1;
      thread::sleep(one_sec);
    }
  }).unwrap();

  let total = time::Duration::from_secs(5);
  let one_sec = time::Duration::from_secs(1);
  let now = time::Instant::now();

  let mut cnt = 0;

  while now.elapsed() <= total {
    println!("{} Running main thread...", cnt);
    cnt += 1;
    thread::sleep(one_sec);
  }

  t.join().unwrap();
  println!("Finished!");
}
