set shell := ["zsh", "-cu"]

default:
  @just --list

cargo_timeout := env_var_or_default("ABIDE_CARGO_TIMEOUT_SECS", "3600")
runner := "python3 tools/run_with_timeout.py"

build:
  {{runner}} --timeout-secs {{cargo_timeout}} --label "workspace build" -- cargo build --workspace

run *args:
  {{runner}} --timeout-secs {{cargo_timeout}} --label "abide run" -- cargo run -p abide -- {{args}}

fmt:
  cargo fmt

fmt-check:
  cargo fmt --check

clippy:
  {{runner}} --timeout-secs {{cargo_timeout}} --label "workspace clippy" -- cargo clippy --workspace --all-targets -- -D warnings

test:
  {{runner}} --timeout-secs {{cargo_timeout}} --label "workspace tests" -- cargo test --workspace

test-lib:
  {{runner}} --timeout-secs {{cargo_timeout}} --label "abide lib tests" -- cargo test -p abide --lib

test-integration:
  {{runner}} --timeout-secs {{cargo_timeout}} --label "abide integration tests" -- cargo test -p abide --test integration

test-unbounded:
  {{runner}} --timeout-secs {{cargo_timeout}} --label "abide-verify unbounded proof tests" -- env ABIDE_RUN_UNBOUNDED_PROOF_TESTS=1 cargo test -p abide-verify --lib
  {{runner}} --timeout-secs {{cargo_timeout}} --label "abide integration unbounded proof tests" -- env ABIDE_RUN_UNBOUNDED_PROOF_TESTS=1 cargo test -p abide --test integration cvc5_sygus_boundary

coverage:
  {{runner}} --timeout-secs {{cargo_timeout}} --label "abide coverage" -- cargo llvm-cov -p abide --lib --tests

coverage-html:
  {{runner}} --timeout-secs {{cargo_timeout}} --label "abide html coverage" -- cargo llvm-cov -p abide --lib --tests --html

check: fmt-check clippy test

check-strict: check test-unbounded

clean:
  cargo clean
