# TunaDB

![build](https://github.com/sadikovi/tunadb/actions/workflows/build.yml/badge.svg)

A simple single-threaded implementation of a storage engine and a database
based on copy-on-write B+tree with unconstrained key and value length in Rust.

The project has zero dependencies and only relies on Rust Standard Library. The
only external development dependency we use is [rand](https://github.com/rust-random/rand)
crate for fuzz tests.

I am currently working on adding other parts of the database such as query
parsing, analysis, and execution using the storage engine.

If you are interested in helping out, feel free to open PRs for features or
bug fixes. There is also a number of TODOs scattered around the codebase.

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

# Simple key-value store

You can also start a simple key-value store built on top of the storage engine.

```shell
cargo run --bin kv
```
