set shell := ["zsh", "-cu"]

default:
  @just --list

build:
  cargo build --workspace

run *args:
  cargo run -p abide -- {{args}}

fmt:
  cargo fmt

fmt-check:
  cargo fmt --check

clippy:
  cargo clippy --workspace --all-targets -- -D warnings

test:
  cargo test --workspace

test-lib:
  cargo test -p abide --lib

test-integration:
  cargo test -p abide --test integration

coverage:
  cargo llvm-cov -p abide --lib --tests

coverage-html:
  cargo llvm-cov -p abide --lib --tests --html

check: fmt-check clippy test

clean:
  cargo clean
