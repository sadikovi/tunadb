# TunaDB

![build](https://github.com/sadikovi/tunadb/actions/workflows/build.yml/badge.svg)

A simple single-threaded SQL database in Rust, built on top of a copy-on-write
B+tree storage engine with unconstrained key and value length.

The SQL layer supports parsing, semantic analysis, logical and physical planning,
and execution — queries run end-to-end against real transactional storage.

The project has zero dependencies and only relies on Rust Standard Library. The
only external development dependency we use is [rand](https://github.com/rust-random/rand)
crate for fuzz tests.

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

Unit tests (storage, SQL analysis, planning, execution):

```shell
cargo test
```

SQL end-to-end integration tests:

```shell
cargo test --test sql
```

Fuzz tests for the B+tree and storage manager (runs each test 100 times):

```shell
./tests/run_fuzz_tests.sh
```

# Simple key-value store

You can also start a simple key-value store built on top of the storage engine.

```shell
cargo run --bin kv
```
