.PHONY: help build run fmt fmt-check clippy test test-lib test-integration coverage coverage-html check clean

CARGO := cargo
LLVM_COV := cargo llvm-cov

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
	$(CARGO) build --workspace

run:
	$(CARGO) run -p abide -- $(ARGS)

fmt:
	$(CARGO) fmt

fmt-check:
	$(CARGO) fmt --check

clippy:
	$(CARGO) clippy --workspace --all-targets -- -D warnings

test:
	$(CARGO) test --workspace

test-lib:
	$(CARGO) test -p abide --lib

test-integration:
	$(CARGO) test -p abide --test integration

coverage:
	$(LLVM_COV) -p abide --lib --tests

coverage-html:
	$(LLVM_COV) -p abide --lib --tests --html

check: fmt-check clippy test

clean:
	$(CARGO) clean
