.PHONY: help build run fmt fmt-check clippy test test-lib test-integration test-unbounded check-lang-mutants-syntax-core check-lang-mutants-syntax-core-shard-1 check-lang-mutants-syntax-core-shard-2 check-lang-mutants-syntax-core-shard-3 check-lang-mutants-syntax-core-shard-4 check-lang-mutants-syntax-expr check-lang-mutants-syntax-expr-shard-1 check-lang-mutants-syntax-expr-shard-2 check-lang-mutants-syntax-expr-shard-3 check-lang-mutants-syntax-expr-shard-4 check-lang-mutants-syntax-system check-lang-mutants-syntax-types check-lang-mutants-syntax-parser check-lang-mutants-sema-namespace check-lang-mutants-sema-namespace-shard-1 check-lang-mutants-sema-namespace-shard-2 check-lang-mutants-sema-namespace-shard-3 check-lang-mutants-sema-namespace-shard-4 check-lang-mutants-sema-loader check-lang-mutants-sema-loader-shard-1 check-lang-mutants-sema-loader-shard-2 check-lang-mutants-sema-loader-shard-3 check-lang-mutants-sema-loader-shard-4 check-lang-mutants-sema-resolution-imports check-lang-mutants-sema-resolution-imports-shard-1 check-lang-mutants-sema-resolution-imports-shard-2 check-lang-mutants-sema-resolution-imports-shard-3 check-lang-mutants-sema-resolution-imports-shard-4 check-lang-mutants-sema-resolution-types check-lang-mutants-sema-resolution-types-core check-lang-mutants-sema-resolution-types-monomorphize check-lang-mutants-sema-resolution-types-validate check-lang-mutants-sema-resolution-expr check-lang-mutants-sema-resolution-expr-core check-lang-mutants-sema-resolution-expr-core-shard-1 check-lang-mutants-sema-resolution-expr-core-shard-2 check-lang-mutants-sema-resolution-expr-core-shard-3 check-lang-mutants-sema-resolution-expr-core-shard-4 check-lang-mutants-sema-resolution-expr-relation check-lang-mutants-sema-resolution-expr-relation-shard-1 check-lang-mutants-sema-resolution-expr-relation-shard-2 check-lang-mutants-sema-resolution-expr-relation-shard-3 check-lang-mutants-sema-resolution-expr-relation-shard-4 check-lang-mutants-sema-resolution-assumptions check-lang-mutants-sema-resolution-assumptions-core check-lang-mutants-sema-resolution-assumptions-core-shard-1 check-lang-mutants-sema-resolution-assumptions-core-shard-2 check-lang-mutants-sema-resolution-assumptions-event-path check-lang-mutants-sema-resolution-assumptions-event-path-shard-1 check-lang-mutants-sema-resolution-assumptions-event-path-shard-2 check-lang-mutants-sema-checker check-lang-mutants-sema-checker-core check-lang-mutants-sema-checker-core-shard-1 check-lang-mutants-sema-checker-core-shard-2 check-lang-mutants-sema-checker-core-shard-3 check-lang-mutants-sema-checker-core-shard-4 check-lang-mutants-sema-checker-entity check-lang-mutants-sema-checker-system check-lang-mutants-sema-checker-system-core check-lang-mutants-sema-checker-system-core-shard-1 check-lang-mutants-sema-checker-system-core-shard-2 check-lang-mutants-sema-checker-system-core-shard-3 check-lang-mutants-sema-checker-system-core-shard-4 check-lang-mutants-sema-checker-system-interface check-lang-mutants-sema-checker-system-extern check-lang-mutants-sema-checker-system-return check-lang-mutants-sema-checker-system-proc-deps check-lang-mutants-sema-checker-matches check-lang-mutants-sema-checker-ctors check-lang-mutants-sema-diagnostics check-lang-mutants-ir-lowering check-lang-mutants-ir-lowering-core check-lang-mutants-ir-lowering-system check-lang-mutants-ir-lowering-expr check-lang-mutants-ir-lowering-expr-shard-1 check-lang-mutants-ir-lowering-expr-shard-2 check-lang-mutants-ir-lowering-expr-shard-3 check-lang-mutants-ir-lowering-expr-shard-4 check-lang-mutants-ir-lowering-qualify check-lang-mutants-cli-project check-lang-mutants-cli-project-baseline check-lang-mutants-cli-project-targets check-lang-mutants-cli-project-targets-shard-1 check-lang-mutants-cli-project-targets-shard-2 check-lang-mutants-cli-project-targets-shard-3 check-lang-mutants-cli-project-targets-shard-4 check-lang-mutants-cli-project-targets-shard-5 check-lang-mutants-cli-project-targets-shard-6 check-lang-mutants-cli-project-targets-shard-7 check-lang-mutants-cli-project-targets-shard-8 check-lang-mutants-cli-project-helpers check-lang-mutants-cli-project-helpers-shard-1 check-lang-mutants-cli-project-helpers-shard-2 check-lang-mutants-cli-project-helpers-shard-3 check-lang-mutants-cli-project-helpers-shard-4 check-lang-mutants-cli-project-helpers-shard-5 check-lang-mutants-cli-project-helpers-shard-6 check-lang-mutants-cli-project-helpers-shard-7 check-lang-mutants-cli-project-helpers-shard-8 check-lang-mutants-fn-vc check-lang-mutants-smt-facade check-lang-mutants-solver-routing check-lang-mutants-runtime-backend check-lang-mutants-verify coverage coverage-html check check-strict clean

.NOTPARALLEL: check-lang-mutants-syntax-core check-lang-mutants-syntax-expr check-lang-mutants-syntax-parser check-lang-mutants-sema-namespace check-lang-mutants-sema-loader check-lang-mutants-sema-resolution-imports check-lang-mutants-sema-resolution-types check-lang-mutants-sema-resolution-expr check-lang-mutants-sema-resolution-assumptions check-lang-mutants-sema-checker check-lang-mutants-ir-lowering check-lang-mutants-cli-project check-lang-mutants-cli-project-targets check-lang-mutants-cli-project-helpers check-lang-mutants-qa check-lang-mutants-qa-parse check-lang-mutants-qa-exec check-lang-mutants-qa-runner check-lang-mutants-qa-extract check-lang-mutants-lsp check-lang-mutants-verify

CARGO := cargo
CARGO_MUTANTS := cargo mutants
LLVM_COV := cargo llvm-cov
RUN_WITH_TIMEOUT := python3 tools/run_with_timeout.py
CARGO_TIMEOUT_SECS ?= 3600
MUTANTS_TIMEOUT_SECS ?= 900
MUTANTS_PROFILE ?= mutants
MUTANTS_JOBS ?= 1
MUTANTS_CARGO_BUILD_JOBS ?= 1
MUTANTS_CMAKE_BUILD_PARALLEL_LEVEL ?= 1
MUTANTS_TEST_THREADS ?= 1
MUTANTS_PER_TEST_TIMEOUT_SECS ?= 60
MUTANTS_BUILD_TIMEOUT_SECS ?= 180
MUTANTS_SHARD_TOTAL := 4
MUTANTS_CLI_SHARD_TOTAL := 32
MUTANTS_CLI_TIMEOUT_SECS ?= 1200
MUTANTS_CLI_PER_TEST_TIMEOUT_SECS ?= 75
MUTANTS_CLI_BUILD_TIMEOUT_SECS ?= 600
MUTANTS_QA_SHARD_TOTAL := 8
MUTANTS_QA_TIMEOUT_SECS ?= 1200
MUTANTS_QA_PER_TEST_TIMEOUT_SECS ?= 75
MUTANTS_QA_BUILD_TIMEOUT_SECS ?= 600
MUTANTS_LSP_SHARD_TOTAL := 8
MUTANTS_LSP_TIMEOUT_SECS ?= 1200
MUTANTS_LSP_PER_TEST_TIMEOUT_SECS ?= 75
MUTANTS_LSP_BUILD_TIMEOUT_SECS ?= 600
MUTANTS_ENV := env CARGO_BUILD_JOBS=$(MUTANTS_CARGO_BUILD_JOBS) CMAKE_BUILD_PARALLEL_LEVEL=$(MUTANTS_CMAKE_BUILD_PARALLEL_LEVEL)
MUTANTS_COMMON_ARGS := --profile $(MUTANTS_PROFILE) --jobs $(MUTANTS_JOBS) --timeout $(MUTANTS_PER_TEST_TIMEOUT_SECS) --build-timeout $(MUTANTS_BUILD_TIMEOUT_SECS)
MUTANTS_CLI_COMMON_ARGS := --profile $(MUTANTS_PROFILE) --timeout $(MUTANTS_CLI_PER_TEST_TIMEOUT_SECS) --build-timeout $(MUTANTS_CLI_BUILD_TIMEOUT_SECS) --in-place --baseline skip
MUTANTS_QA_COMMON_ARGS := --profile $(MUTANTS_PROFILE) --timeout $(MUTANTS_QA_PER_TEST_TIMEOUT_SECS) --build-timeout $(MUTANTS_QA_BUILD_TIMEOUT_SECS) --in-place --baseline skip
MUTANTS_LSP_COMMON_ARGS := --profile $(MUTANTS_PROFILE) --timeout $(MUTANTS_LSP_PER_TEST_TIMEOUT_SECS) --build-timeout $(MUTANTS_LSP_BUILD_TIMEOUT_SECS) --in-place --baseline skip
MUTANTS_LIBTEST_ARGS := -- --test-threads $(MUTANTS_TEST_THREADS)
CLI_PROJECT_HELPERS_RE := resolve_file_by_file_source_targets|resolve_whole_spec_source_targets|resolve_qa_script_targets|collect_qa_scripts_in_directory|build_verify_config|verify_names|validate_verify_solver_options|effective_overall_timeout|qa_summary_message|parse_simulation_scope_overrides
QA_RUNNER_RE := run_qa_script|run_qa_source|run_qa_script_with_hooks|run_qa_source_with_hooks|temporal_artifact_name|render_simulation_summary|explore_state_space|validate_state_space_scopes|select_exploration_systems|build_state_space_verify|slots_for_entity|state_space_artifact_name|sanitize_artifact_name|render_state_space_summary|handle_artifact_statement|load_and_build_model|rebuild_model|rebuild_ir_program|resolve_load_path|collect_abide_files
QA_EXTRACT_RE := extract|extract_interfaces|record_entity_field_meta|record_system_field_meta|extract_entity_graphs|extract_system_graphs|collect_system_field_transitions|extract_system_field_update|extract_guard_state|finite_field_states|finite_field_states_inner|finite_variant_states|enumerate_variant_states|render_variant_state|is_graphable_field_type|extract_finite_state_name|extract_system_info|collect_event_actions|display_ir_expr|display_ir_pattern|display_ir_type
QA_SUPPORT_RE := format_result|format_path|format_transitions|format_table|format_result_json|is_reachable|find_path|terminal_states|initial_states|has_cycles|find_cycle|transitions_from|transitions_to|build_adjacency|dfs_cycle|dfs_find_cycle|qa_command_candidates|qa_query_subcommand_candidates|validate_qa_source|validate_embedded_abide_blocks|base_env_for_qa_source|validate_embedded_abide_block|build_flow_model_from_paths|validate_query_reference|query_reference_validation|temporal_target_reference_validation|model_has_owner|reference_span|artifact_parts_from_result_with_name|payload_kind_label|render_state_space_graph|render_state_space_state|render_state_space_diff|render_witness_summary|render_countermodel_summary|render_proof_artifact_summary|render_witness_timeline|render_behavior_timeline|render_witness_state|render_behavior_state|render_witness_diff|render_behavior_diff|witness_state_lines|behavior_state_lines|render_state_diff|render_operational_state|operational_state_lines|render_relational_state|relational_state_lines|render_relation_id|render_witness_value|render_slot_ref|render_record
LSP_RE := verification_options|server_capabilities|verify_config_for_editor_policy|should_schedule_on_change|should_schedule_on_save|should_run_automatically|should_accept_document_version|document_version|uri_published_elsewhere|collect_diagnostics_for_root|collect_qa_diagnostics_for_root|is_qa_document_path|collect_lsp_diagnostic|qa_run_command_uri_arg|run_qa_script_for_uri|qa_run_source_for_uri|run_qa_source_to_json|diagnostic_to_lsp|related_information|definition_locations|source_for_path|collect_embedded_abide_diagnostics_for_root|location_for_span|uri_and_range_for_span|completion_item_for_symbol|completion_items_for_open_document|embedded_abide_block_at|abide_completion_items_for_source|qa_completion_items|qa_completion_context|current_line_prefix|keyword_completion_context|starts_with_any_keyword|is_word_boundary|keyword_completions|keyword_sort_text|position_to_offset|range_from_span|offset_to_position
CLI_PROJECT_SHARDS := 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32
QA_SHARDS := 1 2 3 4 5 6 7 8
LSP_SHARDS := 1 2 3 4 5 6 7 8
CLI_PROJECT_TARGET_SHARD_TARGETS := $(addprefix check-lang-mutants-cli-project-targets-shard-,$(CLI_PROJECT_SHARDS))
CLI_PROJECT_HELPER_SHARD_TARGETS := $(addprefix check-lang-mutants-cli-project-helpers-shard-,$(CLI_PROJECT_SHARDS))
QA_PARSE_SHARD_TARGETS := $(addprefix check-lang-mutants-qa-parse-shard-,$(QA_SHARDS))
QA_EXEC_SHARD_TARGETS := $(addprefix check-lang-mutants-qa-exec-shard-,$(QA_SHARDS))
QA_RUNNER_SHARD_TARGETS := $(addprefix check-lang-mutants-qa-runner-shard-,$(QA_SHARDS))
QA_EXTRACT_SHARD_TARGETS := $(addprefix check-lang-mutants-qa-extract-shard-,$(QA_SHARDS))
LSP_SHARD_TARGETS := $(addprefix check-lang-mutants-lsp-shard-,$(LSP_SHARDS))

.PHONY: check-lang-mutants-lsp check-lang-mutants-lsp-baseline $(CLI_PROJECT_TARGET_SHARD_TARGETS) $(CLI_PROJECT_HELPER_SHARD_TARGETS) $(QA_PARSE_SHARD_TARGETS) $(QA_EXEC_SHARD_TARGETS) $(QA_RUNNER_SHARD_TARGETS) $(QA_EXTRACT_SHARD_TARGETS) $(LSP_SHARD_TARGETS)
.PHONY: check-lang-mutants-core check-lang-mutants-core-baseline check-lang-mutants-core-diagnostics check-lang-mutants-core-support
.PHONY: check-lang-mutants-witness check-lang-mutants-witness-baseline check-lang-mutants-witness-operational check-lang-mutants-witness-relational-values check-lang-mutants-witness-envelopes

.NOTPARALLEL: check-lang-mutants-core
.NOTPARALLEL: check-lang-mutants-witness

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
	@printf "  make test-unbounded    Run opt-in unbounded proof backend tests\n"
	@printf "  make check-lang-mutants-syntax-core     Run syntax parser core mutation lane\n"
	@printf "  make check-lang-mutants-syntax-expr     Run syntax expression parser mutation lane\n"
	@printf "  make check-lang-mutants-syntax-system   Run syntax system parser mutation lane\n"
	@printf "  make check-lang-mutants-syntax-types    Run syntax type parser mutation lane\n"
	@printf "  make check-lang-mutants-syntax-parser   Run all syntax parser mutation lanes\n"
	@printf "  make check-lang-mutants-sema-namespace  Run sema namespace filtering mutation lane\n"
	@printf "  make check-lang-mutants-sema-loader     Run sema loader/include mutation lane\n"
	@printf "  make check-lang-mutants-sema-resolution-imports  Run sema import/alias resolution mutation lane\n"
	@printf "  make check-lang-mutants-sema-resolution-types    Run sema type/generic resolution mutation lane\n"
	@printf "  make check-lang-mutants-sema-resolution-expr     Run sema expression/relation resolution mutation lane\n"
	@printf "  make check-lang-mutants-sema-resolution-assumptions  Run sema assumption/event-path resolution mutation lane\n"
	@printf "  make check-lang-mutants-sema-checker     Run sema checker mutation lane\n"
	@printf "  make check-lang-mutants-sema-diagnostics Run sema diagnostic mutation lane\n"
	@printf "  make check-lang-mutants-ir-lowering      Run IR lowering mutation lane\n"
	@printf "  make check-lang-mutants-cli-project      Run CLI/project command mutation lane\n"
	@printf "  make check-lang-mutants-qa               Run QA parser/execution/reporting mutation lane\n"
	@printf "  make check-lang-mutants-lsp              Run LSP diagnostics/completion mutation lane\n"
	@printf "  make check-lang-mutants-core             Run core span/diagnostic/message mutation lane\n"
	@printf "  make check-lang-mutants-witness          Run witness payload/envelope mutation lane\n"
	@printf "  make check-lang-mutants-fn-vc            Run function VC mutation lane\n"
	@printf "  make check-lang-mutants-smt-facade       Run SMT facade mutation lane\n"
	@printf "  make check-lang-mutants-solver-routing   Run solver routing mutation lane\n"
	@printf "  make check-lang-mutants-runtime-backend  Run runtime backend mutation lane\n"
	@printf "  make check-lang-mutants-verify           Run all verifier mutation lanes\n"
	@printf "  Mutation lanes default to MUTANTS_JOBS=1, MUTANTS_CARGO_BUILD_JOBS=1, MUTANTS_TEST_THREADS=1, and profile=mutants\n"
	@printf "  Heavy mutation lanes are split into sequential shards with isolated output directories\n"
	@printf "  make coverage          Run llvm-cov and print a summary\n"
	@printf "  make coverage-html     Generate an HTML coverage report\n"
	@printf "  make check             Run fmt-check, clippy, and test\n"
	@printf "  make check-strict      Run check plus unbounded proof backend tests\n"
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

test-unbounded:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(CARGO_TIMEOUT_SECS) --label "abide-verify unbounded proof tests" -- env ABIDE_RUN_UNBOUNDED_PROOF_TESTS=1 $(CARGO) test -p abide-verify --lib
	$(RUN_WITH_TIMEOUT) --timeout-secs $(CARGO_TIMEOUT_SECS) --label "abide integration unbounded proof tests" -- env ABIDE_RUN_UNBOUNDED_PROOF_TESTS=1 $(CARGO) test -p abide --test integration cvc5_sygus_boundary

check-lang-mutants-core: check-lang-mutants-core-baseline check-lang-mutants-core-diagnostics check-lang-mutants-core-support

check-lang-mutants-core-baseline:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-core baseline tests" -- $(MUTANTS_ENV) $(CARGO) test -p abide-core --lib $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-core-diagnostics:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-core diagnostic mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-core --file crates/abide-core/src/diagnostic.rs --output mutants.out.core-diagnostics -- --lib diagnostic $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-core-support:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-core span/message mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-core --file crates/abide-core/src/span.rs --file crates/abide-core/src/messages.rs --output mutants.out.core-support -- --lib $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-witness: check-lang-mutants-witness-baseline check-lang-mutants-witness-operational check-lang-mutants-witness-relational-values check-lang-mutants-witness-envelopes

check-lang-mutants-witness-baseline:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-witness baseline tests" -- $(MUTANTS_ENV) $(CARGO) test -p abide-witness --lib $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-witness-operational:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-witness operational mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-witness --file crates/abide-witness/src/op.rs --output mutants.out.witness-operational -- --lib op $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-witness-relational-values:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-witness relational/value mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-witness --file crates/abide-witness/src/rel.rs --file crates/abide-witness/src/value.rs --output mutants.out.witness-relational-values -- --lib $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-witness-envelopes:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-witness envelope/evidence mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-witness --file crates/abide-witness/src/shared.rs --file crates/abide-witness/src/evidence.rs --output mutants.out.witness-envelopes -- --lib $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-syntax-core: check-lang-mutants-syntax-core-shard-1 check-lang-mutants-syntax-core-shard-2 check-lang-mutants-syntax-core-shard-3 check-lang-mutants-syntax-core-shard-4

check-lang-mutants-syntax-core-shard-1:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-syntax parser core mutants shard 1/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 0/$(MUTANTS_SHARD_TOTAL) -p abide-syntax --file crates/abide-syntax/src/parse/mod.rs --output mutants.out.syntax-core.1-of-$(MUTANTS_SHARD_TOTAL) -- --lib parse $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-syntax-core-shard-2:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-syntax parser core mutants shard 2/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 1/$(MUTANTS_SHARD_TOTAL) -p abide-syntax --file crates/abide-syntax/src/parse/mod.rs --output mutants.out.syntax-core.2-of-$(MUTANTS_SHARD_TOTAL) -- --lib parse $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-syntax-core-shard-3:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-syntax parser core mutants shard 3/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 2/$(MUTANTS_SHARD_TOTAL) -p abide-syntax --file crates/abide-syntax/src/parse/mod.rs --output mutants.out.syntax-core.3-of-$(MUTANTS_SHARD_TOTAL) -- --lib parse $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-syntax-core-shard-4:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-syntax parser core mutants shard 4/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 3/$(MUTANTS_SHARD_TOTAL) -p abide-syntax --file crates/abide-syntax/src/parse/mod.rs --output mutants.out.syntax-core.4-of-$(MUTANTS_SHARD_TOTAL) -- --lib parse $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-syntax-expr: check-lang-mutants-syntax-expr-shard-1 check-lang-mutants-syntax-expr-shard-2 check-lang-mutants-syntax-expr-shard-3 check-lang-mutants-syntax-expr-shard-4

check-lang-mutants-syntax-expr-shard-1:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-syntax expression parser mutants shard 1/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 0/$(MUTANTS_SHARD_TOTAL) -p abide-syntax --file crates/abide-syntax/src/parse/expr.rs --output mutants.out.syntax-expr.1-of-$(MUTANTS_SHARD_TOTAL) -- --lib parse $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-syntax-expr-shard-2:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-syntax expression parser mutants shard 2/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 1/$(MUTANTS_SHARD_TOTAL) -p abide-syntax --file crates/abide-syntax/src/parse/expr.rs --output mutants.out.syntax-expr.2-of-$(MUTANTS_SHARD_TOTAL) -- --lib parse $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-syntax-expr-shard-3:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-syntax expression parser mutants shard 3/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 2/$(MUTANTS_SHARD_TOTAL) -p abide-syntax --file crates/abide-syntax/src/parse/expr.rs --output mutants.out.syntax-expr.3-of-$(MUTANTS_SHARD_TOTAL) -- --lib parse $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-syntax-expr-shard-4:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-syntax expression parser mutants shard 4/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 3/$(MUTANTS_SHARD_TOTAL) -p abide-syntax --file crates/abide-syntax/src/parse/expr.rs --output mutants.out.syntax-expr.4-of-$(MUTANTS_SHARD_TOTAL) -- --lib parse $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-syntax-system:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-syntax system parser mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-syntax --file crates/abide-syntax/src/parse/system.rs --output mutants.out.syntax-system -- --lib parse $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-syntax-types:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-syntax type parser mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-syntax --file crates/abide-syntax/src/parse/types.rs --output mutants.out.syntax-types -- --lib parse $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-syntax-parser: check-lang-mutants-syntax-core check-lang-mutants-syntax-expr check-lang-mutants-syntax-system check-lang-mutants-syntax-types

check-lang-mutants-sema-namespace: check-lang-mutants-sema-namespace-shard-1 check-lang-mutants-sema-namespace-shard-2 check-lang-mutants-sema-namespace-shard-3 check-lang-mutants-sema-namespace-shard-4

check-lang-mutants-sema-namespace-shard-1:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema namespace mutants shard 1/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 0/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/env.rs --re 'build_working_namespace|key_matches_module|flatten_sorted' --output mutants.out.sema-namespace.1-of-$(MUTANTS_SHARD_TOTAL) -- --lib build_working_namespace $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-namespace-shard-2:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema namespace mutants shard 2/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 1/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/env.rs --re 'build_working_namespace|key_matches_module|flatten_sorted' --output mutants.out.sema-namespace.2-of-$(MUTANTS_SHARD_TOTAL) -- --lib build_working_namespace $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-namespace-shard-3:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema namespace mutants shard 3/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 2/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/env.rs --re 'build_working_namespace|key_matches_module|flatten_sorted' --output mutants.out.sema-namespace.3-of-$(MUTANTS_SHARD_TOTAL) -- --lib build_working_namespace $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-namespace-shard-4:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema namespace mutants shard 4/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 3/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/env.rs --re 'build_working_namespace|key_matches_module|flatten_sorted' --output mutants.out.sema-namespace.4-of-$(MUTANTS_SHARD_TOTAL) -- --lib build_working_namespace $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-loader: check-lang-mutants-sema-loader-shard-1 check-lang-mutants-sema-loader-shard-2 check-lang-mutants-sema-loader-shard-3 check-lang-mutants-sema-loader-shard-4

check-lang-mutants-sema-loader-shard-1:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema loader mutants shard 1/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 0/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/loader.rs --output mutants.out.sema-loader.1-of-$(MUTANTS_SHARD_TOTAL) -- --lib loader $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-loader-shard-2:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema loader mutants shard 2/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 1/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/loader.rs --output mutants.out.sema-loader.2-of-$(MUTANTS_SHARD_TOTAL) -- --lib loader $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-loader-shard-3:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema loader mutants shard 3/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 2/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/loader.rs --output mutants.out.sema-loader.3-of-$(MUTANTS_SHARD_TOTAL) -- --lib loader $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-loader-shard-4:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema loader mutants shard 4/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 3/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/loader.rs --output mutants.out.sema-loader.4-of-$(MUTANTS_SHARD_TOTAL) -- --lib loader $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-imports: check-lang-mutants-sema-resolution-imports-shard-1 check-lang-mutants-sema-resolution-imports-shard-2 check-lang-mutants-sema-resolution-imports-shard-3 check-lang-mutants-sema-resolution-imports-shard-4

check-lang-mutants-sema-resolution-imports-shard-1:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema import resolution mutants shard 1/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 0/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/resolve/mod.rs --re 'resolve_use_declarations|check_import_target|check_use_cycles|dfs_use_cycle|import_is_visible|bindings_without' --output mutants.out.sema-resolution-imports.1-of-$(MUTANTS_SHARD_TOTAL) -- --lib resolve $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-imports-shard-2:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema import resolution mutants shard 2/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 1/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/resolve/mod.rs --re 'resolve_use_declarations|check_import_target|check_use_cycles|dfs_use_cycle|import_is_visible|bindings_without' --output mutants.out.sema-resolution-imports.2-of-$(MUTANTS_SHARD_TOTAL) -- --lib resolve $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-imports-shard-3:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema import resolution mutants shard 3/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 2/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/resolve/mod.rs --re 'resolve_use_declarations|check_import_target|check_use_cycles|dfs_use_cycle|import_is_visible|bindings_without' --output mutants.out.sema-resolution-imports.3-of-$(MUTANTS_SHARD_TOTAL) -- --lib resolve $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-imports-shard-4:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema import resolution mutants shard 4/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 3/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/resolve/mod.rs --re 'resolve_use_declarations|check_import_target|check_use_cycles|dfs_use_cycle|import_is_visible|bindings_without' --output mutants.out.sema-resolution-imports.4-of-$(MUTANTS_SHARD_TOTAL) -- --lib resolve $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-types: check-lang-mutants-sema-resolution-types-core check-lang-mutants-sema-resolution-types-monomorphize check-lang-mutants-sema-resolution-types-validate

check-lang-mutants-sema-resolution-types-core:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema type resolution core mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-sema --file crates/abide-sema/src/elab/resolve/mod.rs --re 'resolve_all_types|resolve_type_refinement_predicates|resolve_ty|resolve_params_lr|base_ty_without_refinement' --output mutants.out.sema-resolution-types-core -- --lib resolve $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-types-monomorphize:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema generic monomorphization mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-sema --file crates/abide-sema/src/elab/resolve/monomorphize.rs --re 'format_mono_name|mono_ty_name|substitute_ty|monomorphize_inline|monomorphize_variant_fields|resolve_nested_generics|monomorphize_generics|collect_all_param_uses' --output mutants.out.sema-resolution-types-monomorphize -- --lib monomorphize $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-types-validate:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema unresolved type validation mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-sema --file crates/abide-sema/src/elab/resolve/validate.rs --re 'validate_remaining_type_params|validate_unresolved_types|collect_ty_params|collect_unresolved' --output mutants.out.sema-resolution-types-validate -- --lib validate $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-expr: check-lang-mutants-sema-resolution-expr-core check-lang-mutants-sema-resolution-expr-relation

check-lang-mutants-sema-resolution-expr-core: check-lang-mutants-sema-resolution-expr-core-shard-1 check-lang-mutants-sema-resolution-expr-core-shard-2 check-lang-mutants-sema-resolution-expr-core-shard-3 check-lang-mutants-sema-resolution-expr-core-shard-4

check-lang-mutants-sema-resolution-expr-core-shard-1:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema expression resolution core mutants shard 1/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 0/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/resolve/expr.rs --re 'resolve_expr|resolve_var_type|resolve_ctor_type_from_context|resolve_comparison_ctor_from_context|infer_field_type|infer_qualcall_type|infer_numeric_binop_type|infer_index_type|set_source_element_type' --output mutants.out.sema-resolution-expr-core.1-of-$(MUTANTS_SHARD_TOTAL) -- --lib resolve $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-expr-core-shard-2:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema expression resolution core mutants shard 2/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 1/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/resolve/expr.rs --re 'resolve_expr|resolve_var_type|resolve_ctor_type_from_context|resolve_comparison_ctor_from_context|infer_field_type|infer_qualcall_type|infer_numeric_binop_type|infer_index_type|set_source_element_type' --output mutants.out.sema-resolution-expr-core.2-of-$(MUTANTS_SHARD_TOTAL) -- --lib resolve $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-expr-core-shard-3:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema expression resolution core mutants shard 3/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 2/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/resolve/expr.rs --re 'resolve_expr|resolve_var_type|resolve_ctor_type_from_context|resolve_comparison_ctor_from_context|infer_field_type|infer_qualcall_type|infer_numeric_binop_type|infer_index_type|set_source_element_type' --output mutants.out.sema-resolution-expr-core.3-of-$(MUTANTS_SHARD_TOTAL) -- --lib resolve $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-expr-core-shard-4:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema expression resolution core mutants shard 4/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 3/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/resolve/expr.rs --re 'resolve_expr|resolve_var_type|resolve_ctor_type_from_context|resolve_comparison_ctor_from_context|infer_field_type|infer_qualcall_type|infer_numeric_binop_type|infer_index_type|set_source_element_type' --output mutants.out.sema-resolution-expr-core.4-of-$(MUTANTS_SHARD_TOTAL) -- --lib resolve $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-expr-relation: check-lang-mutants-sema-resolution-expr-relation-shard-1 check-lang-mutants-sema-resolution-expr-relation-shard-2 check-lang-mutants-sema-resolution-expr-relation-shard-3 check-lang-mutants-sema-resolution-expr-relation-shard-4

check-lang-mutants-sema-resolution-expr-relation-shard-1:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema relation expression mutants shard 1/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 0/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/resolve/expr.rs --re 'relation_columns|relation_type_from_columns|relation_type_from_projection|ty_same|infer_relation_join_type|infer_relation_set_op_type|infer_relation_product_type|relation_project_indices|infer_relation_project_type|infer_relation_transpose_type|infer_relation_closure_type|infer_relation_field_type' --output mutants.out.sema-resolution-expr-relation.1-of-$(MUTANTS_SHARD_TOTAL) -- --lib relation $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-expr-relation-shard-2:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema relation expression mutants shard 2/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 1/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/resolve/expr.rs --re 'relation_columns|relation_type_from_columns|relation_type_from_projection|ty_same|infer_relation_join_type|infer_relation_set_op_type|infer_relation_product_type|relation_project_indices|infer_relation_project_type|infer_relation_transpose_type|infer_relation_closure_type|infer_relation_field_type' --output mutants.out.sema-resolution-expr-relation.2-of-$(MUTANTS_SHARD_TOTAL) -- --lib relation $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-expr-relation-shard-3:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema relation expression mutants shard 3/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 2/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/resolve/expr.rs --re 'relation_columns|relation_type_from_columns|relation_type_from_projection|ty_same|infer_relation_join_type|infer_relation_set_op_type|infer_relation_product_type|relation_project_indices|infer_relation_project_type|infer_relation_transpose_type|infer_relation_closure_type|infer_relation_field_type' --output mutants.out.sema-resolution-expr-relation.3-of-$(MUTANTS_SHARD_TOTAL) -- --lib relation $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-expr-relation-shard-4:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema relation expression mutants shard 4/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 3/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/resolve/expr.rs --re 'relation_columns|relation_type_from_columns|relation_type_from_projection|ty_same|infer_relation_join_type|infer_relation_set_op_type|infer_relation_product_type|relation_project_indices|infer_relation_project_type|infer_relation_transpose_type|infer_relation_closure_type|infer_relation_field_type' --output mutants.out.sema-resolution-expr-relation.4-of-$(MUTANTS_SHARD_TOTAL) -- --lib relation $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-assumptions: check-lang-mutants-sema-resolution-assumptions-core check-lang-mutants-sema-resolution-assumptions-event-path

check-lang-mutants-sema-resolution-assumptions-core: check-lang-mutants-sema-resolution-assumptions-core-shard-1 check-lang-mutants-sema-resolution-assumptions-core-shard-2

check-lang-mutants-sema-resolution-assumptions-core-shard-1:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema assumption resolution mutants shard 1/2" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 0/2 -p abide-sema --file crates/abide-sema/src/elab/resolve/assumptions.rs --re 'resolve_assumption_sets|build_assume_delta|build_assume_delta_with_bindings|merge_delta_into|check_under_add_only_resolved|resolve_by_lemmas_subset_containment|format_assumption_set|compute_missing|populate_assumption_set|populate_assumption_set_from_items' --output mutants.out.sema-resolution-assumptions-core.1-of-2 -- --lib assumption $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-assumptions-core-shard-2:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema assumption resolution mutants shard 2/2" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 1/2 -p abide-sema --file crates/abide-sema/src/elab/resolve/assumptions.rs --re 'resolve_assumption_sets|build_assume_delta|build_assume_delta_with_bindings|merge_delta_into|check_under_add_only_resolved|resolve_by_lemmas_subset_containment|format_assumption_set|compute_missing|populate_assumption_set|populate_assumption_set_from_items' --output mutants.out.sema-resolution-assumptions-core.2-of-2 -- --lib assumption $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-assumptions-event-path: check-lang-mutants-sema-resolution-assumptions-event-path-shard-1 check-lang-mutants-sema-resolution-assumptions-event-path-shard-2

check-lang-mutants-sema-resolution-assumptions-event-path-shard-1:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema event path resolution mutants shard 1/2" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 0/2 -p abide-sema --file crates/abide-sema/src/elab/resolve/mod.rs --re 'resolve_event_path' --output mutants.out.sema-resolution-assumptions-event-path.1-of-2 -- --lib event_path $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-assumptions-event-path-shard-2:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema event path resolution mutants shard 2/2" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 1/2 -p abide-sema --file crates/abide-sema/src/elab/resolve/mod.rs --re 'resolve_event_path' --output mutants.out.sema-resolution-assumptions-event-path.2-of-2 -- --lib event_path $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-checker: check-lang-mutants-sema-checker-core check-lang-mutants-sema-checker-entity check-lang-mutants-sema-checker-system check-lang-mutants-sema-checker-matches check-lang-mutants-sema-checker-ctors

check-lang-mutants-sema-checker-core: check-lang-mutants-sema-checker-core-shard-1 check-lang-mutants-sema-checker-core-shard-2 check-lang-mutants-sema-checker-core-shard-3 check-lang-mutants-sema-checker-core-shard-4

check-lang-mutants-sema-checker-core-shard-1:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema checker core mutants shard 1/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 0/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/check/mod.rs --re 'check_type|check_collection_homogeneity|types_compatible|expr_compatible_with_ty|check_unresolved_constructors|check_fn_contracts|check_refinement_predicates|check_verifier_surface_expr|check_verifier_surface_expr_allowing_sequence|find_sequence_composition_span|find_unsupported_verifier_expr|check_pred_prop_cycles|collect_name_refs|dfs_find_cycle|collect_epattern_vars' --output mutants.out.sema-checker-core.1-of-$(MUTANTS_SHARD_TOTAL) -- --lib check $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-checker-core-shard-2:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema checker core mutants shard 2/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 1/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/check/mod.rs --re 'check_type|check_collection_homogeneity|types_compatible|expr_compatible_with_ty|check_unresolved_constructors|check_fn_contracts|check_refinement_predicates|check_verifier_surface_expr|check_verifier_surface_expr_allowing_sequence|find_sequence_composition_span|find_unsupported_verifier_expr|check_pred_prop_cycles|collect_name_refs|dfs_find_cycle|collect_epattern_vars' --output mutants.out.sema-checker-core.2-of-$(MUTANTS_SHARD_TOTAL) -- --lib check $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-checker-core-shard-3:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema checker core mutants shard 3/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 2/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/check/mod.rs --re 'check_type|check_collection_homogeneity|types_compatible|expr_compatible_with_ty|check_unresolved_constructors|check_fn_contracts|check_refinement_predicates|check_verifier_surface_expr|check_verifier_surface_expr_allowing_sequence|find_sequence_composition_span|find_unsupported_verifier_expr|check_pred_prop_cycles|collect_name_refs|dfs_find_cycle|collect_epattern_vars' --output mutants.out.sema-checker-core.3-of-$(MUTANTS_SHARD_TOTAL) -- --lib check $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-checker-core-shard-4:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema checker core mutants shard 4/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 3/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/check/mod.rs --re 'check_type|check_collection_homogeneity|types_compatible|expr_compatible_with_ty|check_unresolved_constructors|check_fn_contracts|check_refinement_predicates|check_verifier_surface_expr|check_verifier_surface_expr_allowing_sequence|find_sequence_composition_span|find_unsupported_verifier_expr|check_pred_prop_cycles|collect_name_refs|dfs_find_cycle|collect_epattern_vars' --output mutants.out.sema-checker-core.4-of-$(MUTANTS_SHARD_TOTAL) -- --lib check $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-checker-entity:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema entity checker mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-sema --file crates/abide-sema/src/elab/check/entity.rs --re 'check_entity|check_invariant_body_no_liveness|check_field|check_action|check_assignment' --output mutants.out.sema-checker-entity -- --lib entity $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-checker-system: check-lang-mutants-sema-checker-system-core check-lang-mutants-sema-checker-system-interface check-lang-mutants-sema-checker-system-extern check-lang-mutants-sema-checker-system-return check-lang-mutants-sema-checker-system-proc-deps

check-lang-mutants-sema-checker-system-core: check-lang-mutants-sema-checker-system-core-shard-1 check-lang-mutants-sema-checker-system-core-shard-2 check-lang-mutants-sema-checker-system-core-shard-3 check-lang-mutants-sema-checker-system-core-shard-4

check-lang-mutants-sema-checker-system-core-shard-1:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema system checker core mutants shard 1/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 0/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/check/system.rs --re 'check_system' --output mutants.out.sema-checker-system-core.1-of-$(MUTANTS_SHARD_TOTAL) -- --lib system $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-checker-system-core-shard-2:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema system checker core mutants shard 2/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 1/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/check/system.rs --re 'check_system' --output mutants.out.sema-checker-system-core.2-of-$(MUTANTS_SHARD_TOTAL) -- --lib system $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-checker-system-core-shard-3:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema system checker core mutants shard 3/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 2/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/check/system.rs --re 'check_system' --output mutants.out.sema-checker-system-core.3-of-$(MUTANTS_SHARD_TOTAL) -- --lib system $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-checker-system-core-shard-4:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema system checker core mutants shard 4/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 3/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/check/system.rs --re 'check_system' --output mutants.out.sema-checker-system-core.4-of-$(MUTANTS_SHARD_TOTAL) -- --lib system $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-checker-system-interface:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema interface conformance mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-sema --file crates/abide-sema/src/elab/check/system.rs --re 'check_interface_conformance' --output mutants.out.sema-checker-system-interface -- --lib interface $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-checker-system-extern:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema extern checker mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-sema --file crates/abide-sema/src/elab/check/system.rs --re 'check_extern' --output mutants.out.sema-checker-system-extern -- --lib check_extern $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-checker-system-return:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema system return helper mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-sema --file crates/abide-sema/src/elab/check/system.rs --re 'extract_return_ctor_name|extract_return_payload' --output mutants.out.sema-checker-system-return -- --lib return $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-checker-system-proc-deps:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema proc dependency checker mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-sema --file crates/abide-sema/src/elab/check/system.rs --re 'validate_proc_dep_cond' --output mutants.out.sema-checker-system-proc-deps -- --lib proc_dep $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-checker-matches:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema match checker mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-sema --file crates/abide-sema/src/elab/check/matches.rs --re 'check_match_exhaustiveness|pattern_is_catchall|collect_covered_ctors|check_pattern_shape|resolve_to_enum_info|resolve_field_type' --output mutants.out.sema-checker-matches -- --lib match $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-checker-ctors:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema constructor checker mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-sema --file crates/abide-sema/src/elab/check/ctors.rs --re 'walk_event_action_for_ctor_check|check_ctor_records_in_expr' --output mutants.out.sema-checker-ctors -- --lib ctor $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-diagnostics:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema diagnostic mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-sema --file crates/abide-sema/src/elab/error.rs --output mutants.out.sema-diagnostics -- --lib error $(MUTANTS_LIBTEST_ARGS)

IR_LOWERING_CORE_RE := lower_interface|lower_params|lower_type|lower_ty|lower_builtin|lower_const|lower_contracts|lower_while_contracts|lower_fn|lower_pred|lower_prop|lower_entity|lower_derived_field|lower_invariant|lower_fsm|lower_field|lower_action|lower_verify|lower_theorem|lower_axiom|lower_lemma|lower_scene|lower_given|lower_scene_action
IR_LOWERING_SYSTEM_RE := lower_system|lower_extern|lower_proc|lower_proc_params|lower_proc_node_actions|lower_proc_dep_cond|lower_query|lower_system_action|lower_event_action
IR_LOWERING_EXPR_RE := lower_expr|lower_var_expr|lower_binop_expr|lower_call_expr|lower_call_ref_expr|lower_qualified_call_expr|lower_relation_field_call|lower_relation_project_call|lower_relation_projection_columns|lower_builtin_qualified_call|lower_qualified_expr|lower_quant_expr|lower_let_expr|lower_lambda_expr|lower_tuple_lit_expr|lower_match_expr|lower_set_comp_expr|lower_rel_comp_expr|lower_while_expr|lower_aggregate_expr|lower_saw_expr|lower_ctor_record_expr|lower_pattern|lower_pattern_for_scrutinee|lower_lit|lower_binop|lower_unop

check-lang-mutants-ir-lowering: check-lang-mutants-ir-lowering-core check-lang-mutants-ir-lowering-system check-lang-mutants-ir-lowering-expr check-lang-mutants-ir-lowering-qualify

check-lang-mutants-ir-lowering-core:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-ir core lowering mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-ir --file crates/abide-ir/src/ir/lower/mod.rs --re '$(IR_LOWERING_CORE_RE)' --output mutants.out.ir-lowering-core -- --lib lower $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-ir-lowering-system:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-ir system lowering mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-ir --file crates/abide-ir/src/ir/lower/system.rs --re '$(IR_LOWERING_SYSTEM_RE)' --output mutants.out.ir-lowering-system -- --lib lower $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-ir-lowering-expr: check-lang-mutants-ir-lowering-expr-shard-1 check-lang-mutants-ir-lowering-expr-shard-2 check-lang-mutants-ir-lowering-expr-shard-3 check-lang-mutants-ir-lowering-expr-shard-4

check-lang-mutants-ir-lowering-expr-shard-1:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-ir expression lowering mutants shard 1/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 0/$(MUTANTS_SHARD_TOTAL) -p abide-ir --file crates/abide-ir/src/ir/lower/expr.rs --re '$(IR_LOWERING_EXPR_RE)' --output mutants.out.ir-lowering-expr.1-of-$(MUTANTS_SHARD_TOTAL) -- --lib lower $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-ir-lowering-expr-shard-2:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-ir expression lowering mutants shard 2/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 1/$(MUTANTS_SHARD_TOTAL) -p abide-ir --file crates/abide-ir/src/ir/lower/expr.rs --re '$(IR_LOWERING_EXPR_RE)' --output mutants.out.ir-lowering-expr.2-of-$(MUTANTS_SHARD_TOTAL) -- --lib lower $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-ir-lowering-expr-shard-3:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-ir expression lowering mutants shard 3/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 2/$(MUTANTS_SHARD_TOTAL) -p abide-ir --file crates/abide-ir/src/ir/lower/expr.rs --re '$(IR_LOWERING_EXPR_RE)' --output mutants.out.ir-lowering-expr.3-of-$(MUTANTS_SHARD_TOTAL) -- --lib lower $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-ir-lowering-expr-shard-4:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-ir expression lowering mutants shard 4/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 3/$(MUTANTS_SHARD_TOTAL) -p abide-ir --file crates/abide-ir/src/ir/lower/expr.rs --re '$(IR_LOWERING_EXPR_RE)' --output mutants.out.ir-lowering-expr.4-of-$(MUTANTS_SHARD_TOTAL) -- --lib lower $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-ir-lowering-qualify:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-ir qualification lowering mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-ir --file crates/abide-ir/src/ir/lower/qualify.rs --re 'qualify_query_vars_scoped|qualify_action_query_vars' --output mutants.out.ir-lowering-qualify -- --lib qualify $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-cli-project: check-lang-mutants-cli-project-baseline check-lang-mutants-cli-project-targets check-lang-mutants-cli-project-helpers

check-lang-mutants-cli-project-baseline:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_CLI_TIMEOUT_SECS) --label "abide CLI project mutants-profile prebuild" -- $(MUTANTS_ENV) $(CARGO) test -p abide --lib --profile $(MUTANTS_PROFILE) --no-run
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide CLI project baseline tests" -- $(MUTANTS_ENV) $(CARGO) test -p abide --lib cli::tests $(MUTANTS_LIBTEST_ARGS)
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide target discovery baseline tests" -- $(MUTANTS_ENV) $(CARGO) test -p abide --lib targets::tests $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-cli-project-targets: $(CLI_PROJECT_TARGET_SHARD_TARGETS)

$(CLI_PROJECT_TARGET_SHARD_TARGETS): check-lang-mutants-cli-project-targets-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_CLI_TIMEOUT_SECS) --label "abide CLI target discovery mutants shard $*/$(MUTANTS_CLI_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_CLI_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_CLI_SHARD_TOTAL)" -p abide --file crates/abide/src/targets.rs --output mutants.out.cli-project-targets.$*-of-$(MUTANTS_CLI_SHARD_TOTAL) -- --lib targets $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-cli-project-helpers: $(CLI_PROJECT_HELPER_SHARD_TARGETS)

$(CLI_PROJECT_HELPER_SHARD_TARGETS): check-lang-mutants-cli-project-helpers-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_CLI_TIMEOUT_SECS) --label "abide CLI helper mutants shard $*/$(MUTANTS_CLI_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_CLI_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_CLI_SHARD_TOTAL)" -p abide --file crates/abide/src/cli.rs --re '$(CLI_PROJECT_HELPERS_RE)' --output mutants.out.cli-project-helpers.$*-of-$(MUTANTS_CLI_SHARD_TOTAL) -- --lib cli $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-qa: check-lang-mutants-qa-baseline check-lang-mutants-qa-parse check-lang-mutants-qa-exec check-lang-mutants-qa-runner check-lang-mutants-qa-extract check-lang-mutants-qa-support

check-lang-mutants-qa-baseline:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_QA_TIMEOUT_SECS) --label "abide QA mutants-profile prebuild" -- $(MUTANTS_ENV) $(CARGO) test -p abide-qa --lib --profile $(MUTANTS_PROFILE) --no-run
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_QA_TIMEOUT_SECS) --label "abide QA mutants-profile baseline tests" -- $(MUTANTS_ENV) $(CARGO) test -p abide-qa --lib --profile $(MUTANTS_PROFILE) $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-qa-parse: $(QA_PARSE_SHARD_TARGETS)

$(QA_PARSE_SHARD_TARGETS): check-lang-mutants-qa-parse-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_QA_TIMEOUT_SECS) --label "abide QA parser mutants shard $*/$(MUTANTS_QA_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_QA_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_QA_SHARD_TOTAL)" -p abide-qa --file crates/abide-qa/src/qa/parse.rs --output mutants.out.qa-parse.$*-of-$(MUTANTS_QA_SHARD_TOTAL) -- --lib parse $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-qa-exec: $(QA_EXEC_SHARD_TARGETS)

$(QA_EXEC_SHARD_TARGETS): check-lang-mutants-qa-exec-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_QA_TIMEOUT_SECS) --label "abide QA execution mutants shard $*/$(MUTANTS_QA_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_QA_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_QA_SHARD_TOTAL)" -p abide-qa --file crates/abide-qa/src/qa/exec.rs --output mutants.out.qa-exec.$*-of-$(MUTANTS_QA_SHARD_TOTAL) -- --lib exec $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-qa-runner: $(QA_RUNNER_SHARD_TARGETS)

$(QA_RUNNER_SHARD_TARGETS): check-lang-mutants-qa-runner-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_QA_TIMEOUT_SECS) --label "abide QA runner mutants shard $*/$(MUTANTS_QA_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_QA_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_QA_SHARD_TOTAL)" -p abide-qa --file crates/abide-qa/src/qa/runner.rs --re '$(QA_RUNNER_RE)' --output mutants.out.qa-runner.$*-of-$(MUTANTS_QA_SHARD_TOTAL) -- --lib runner $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-qa-extract: $(QA_EXTRACT_SHARD_TARGETS)

$(QA_EXTRACT_SHARD_TARGETS): check-lang-mutants-qa-extract-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_QA_TIMEOUT_SECS) --label "abide QA extraction mutants shard $*/$(MUTANTS_QA_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_QA_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_QA_SHARD_TOTAL)" -p abide-qa --file crates/abide-qa/src/qa/extract.rs --re '$(QA_EXTRACT_RE)' --output mutants.out.qa-extract.$*-of-$(MUTANTS_QA_SHARD_TOTAL) -- --lib extract $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-qa-support: check-lang-mutants-qa-format check-lang-mutants-qa-graph check-lang-mutants-qa-complete check-lang-mutants-qa-validate check-lang-mutants-qa-artifacts

check-lang-mutants-qa-format:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_QA_TIMEOUT_SECS) --label "abide QA formatting mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_QA_COMMON_ARGS) -p abide-qa --file crates/abide-qa/src/qa/fmt.rs --re '$(QA_SUPPORT_RE)' --output mutants.out.qa-format -- --lib fmt $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-qa-graph:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_QA_TIMEOUT_SECS) --label "abide QA graph mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_QA_COMMON_ARGS) -p abide-qa --file crates/abide-qa/src/qa/graph.rs --re '$(QA_SUPPORT_RE)' --output mutants.out.qa-graph -- --lib graph $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-qa-complete:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_QA_TIMEOUT_SECS) --label "abide QA completion mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_QA_COMMON_ARGS) -p abide-qa --file crates/abide-qa/src/qa/complete.rs --re '$(QA_SUPPORT_RE)' --output mutants.out.qa-complete -- --lib complete $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-qa-validate:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_QA_TIMEOUT_SECS) --label "abide QA validation mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_QA_COMMON_ARGS) -p abide-qa --file crates/abide-qa/src/qa/validate.rs --re '$(QA_SUPPORT_RE)' --output mutants.out.qa-validate -- --lib validate $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-qa-artifacts:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_QA_TIMEOUT_SECS) --label "abide QA artifact rendering mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_QA_COMMON_ARGS) -p abide-qa --file crates/abide-qa/src/qa/artifacts.rs --re '$(QA_SUPPORT_RE)' --output mutants.out.qa-artifacts -- --lib artifacts $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-lsp: check-lang-mutants-lsp-baseline $(LSP_SHARD_TARGETS)

check-lang-mutants-lsp-baseline:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_LSP_TIMEOUT_SECS) --label "abide LSP mutants-profile prebuild" -- $(MUTANTS_ENV) $(CARGO) test -p abide-lsp --profile $(MUTANTS_PROFILE) --no-run
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_LSP_TIMEOUT_SECS) --label "abide LSP mutants-profile baseline tests" -- $(MUTANTS_ENV) $(CARGO) test -p abide-lsp --profile $(MUTANTS_PROFILE) $(MUTANTS_LIBTEST_ARGS)

$(LSP_SHARD_TARGETS): check-lang-mutants-lsp-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_LSP_TIMEOUT_SECS) --label "abide LSP mutants shard $*/$(MUTANTS_LSP_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_LSP_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_LSP_SHARD_TOTAL)" -p abide-lsp --file crates/abide-lsp/src/main.rs --re '$(LSP_RE)' --output mutants.out.lsp.$*-of-$(MUTANTS_LSP_SHARD_TOTAL) -- --bin abide-lsp tests $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-fn-vc:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-verify function VC mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-verify --file crates/abide-verify/src/verify/fn_verify.rs --output mutants.out.fn-vc -- --lib fn_contract $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-smt-facade:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-verify SMT facade mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-verify --file crates/abide-verify/src/verify/smt.rs --output mutants.out.smt-facade -- --lib smt $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-solver-routing:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-verify solver routing mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-verify --file crates/abide-verify/src/verify/solver.rs --re 'SolverCapabilities|backend_score|set_active_solver_family|is_solver_family_available|AbideSolver|z3_check_chc' --output mutants.out.solver-routing -- --lib solver $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-runtime-backend:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-verify runtime backend mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-verify --file crates/abide-verify/src/verify/solver.rs --re 'RuntimeBackend|RuntimeModel|RuntimeDynamic|RuntimeBool|RuntimeInt|RuntimeReal|RuntimeArray|RuntimeModelEval' --output mutants.out.runtime-backend -- --lib solver $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-verify: check-lang-mutants-fn-vc check-lang-mutants-smt-facade check-lang-mutants-solver-routing check-lang-mutants-runtime-backend

coverage:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(CARGO_TIMEOUT_SECS) --label "abide coverage" -- $(LLVM_COV) -p abide --lib --tests

coverage-html:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(CARGO_TIMEOUT_SECS) --label "abide html coverage" -- $(LLVM_COV) -p abide --lib --tests --html

check: fmt-check clippy test

check-strict: check test-unbounded

clean:
	$(CARGO) clean
