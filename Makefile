.PHONY: help build run fmt fmt-check clippy test test-lib test-integration coverage coverage-html check clean

CARGO := cargo
LLVM_COV := cargo llvm-cov
RUN_WITH_TIMEOUT := python3 tools/run_with_timeout.py
CARGO_TIMEOUT_SECS ?= 3600

help:
	@printf "Available targets:\n"
	@printf "  make build             Build the compiler\n"
	@printf "  make run ARGS='...'    Run the compiler with CLI args\n"
	@printf "  make fmt               Format Rust code\n"
	@printf "  make fmt-check         Check formatting without rewriting files\n"
	@printf "  make clippy            Run clippy with warnings denied\n"
	@printf "  make test              Run unit, integration, and doc tests\n"
	@printf "  make test-lib          Run library unit tests only\n"
	@printf "  make test-integration  Run integration tests only\n"
	@printf "  make coverage          Run llvm-cov and print a summary\n"
	@printf "  make coverage-html     Generate an HTML coverage report\n"
	@printf "  make check             Run fmt-check, clippy, and test\n"
	@printf "  make clean             Remove build artifacts\n"

build:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(CARGO_TIMEOUT_SECS) --label "workspace build" -- $(CARGO) build --workspace

run:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(CARGO_TIMEOUT_SECS) --label "abide run" -- $(CARGO) run -p abide -- $(ARGS)

fmt:
	$(CARGO) fmt

fmt-check:
	$(CARGO) fmt --check

clippy:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(CARGO_TIMEOUT_SECS) --label "workspace clippy" -- $(CARGO) clippy --workspace --all-targets -- -D warnings

test:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(CARGO_TIMEOUT_SECS) --label "workspace tests" -- $(CARGO) test --workspace

test-lib:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(CARGO_TIMEOUT_SECS) --label "abide lib tests" -- $(CARGO) test -p abide --lib

test-integration:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(CARGO_TIMEOUT_SECS) --label "abide integration tests" -- $(CARGO) test -p abide --test integration

coverage:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(CARGO_TIMEOUT_SECS) --label "abide coverage" -- $(LLVM_COV) -p abide --lib --tests

coverage-html:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(CARGO_TIMEOUT_SECS) --label "abide html coverage" -- $(LLVM_COV) -p abide --lib --tests --html

check: fmt-check clippy test

clean:
	$(CARGO) clean
