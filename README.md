# TunaDB

A simple single-threaded implementation of a storage engine based on
copy-on-write B+tree in Rust.

This was done mostly for educational purposes to learn more about storage
layout and B+trees. There is a number of TODOs scattered around the codebase so
you are interested, feel free to open PRs for features or bug fixes.

# Simple key-value store

You can also start a simple key-value store built on top of the storage engine.

```shell
cargo run --bin kv
```

# Build

```shell
cargo check
# or
cargo build
```

# Test

Unit tests:

```shell
cargo test
```

Integration tests:

```shell
it/run_test.sh
```
