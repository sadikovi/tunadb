# TunaDB

A simple single-threaded implementation of a storage engine based on
copy-on-write B+tree with unconstrained key and value length in Rust.

I am also working on adding other parts of the database such as query parsing,
analysis, and execution using the storage engine.

If you are interested in helping out, feel free to open PRs for features or
bug fixes. There is also a number of TODOs scattered around the codebase.

# Simple key-value store

You can also start a simple key-value store built on top of the storage engine.

```shell
cargo run --bin kv
```

# Build

```shell
cargo check
```

or

```shell
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
