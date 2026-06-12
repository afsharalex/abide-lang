set shell := ["zsh", "-cu"]

default:
  @just --list

cargo_timeout := env_var_or_default("ABIDE_CARGO_TIMEOUT_SECS", "3600")
mutants_timeout := env_var_or_default("ABIDE_MUTANTS_TIMEOUT_SECS", "900")
mutants_profile := env_var_or_default("ABIDE_MUTANTS_PROFILE", "mutants")
mutants_jobs := env_var_or_default("ABIDE_MUTANTS_JOBS", "1")
mutants_cargo_build_jobs := env_var_or_default("ABIDE_MUTANTS_CARGO_BUILD_JOBS", "1")
mutants_cmake_build_parallel_level := env_var_or_default("ABIDE_MUTANTS_CMAKE_BUILD_PARALLEL_LEVEL", "1")
mutants_test_threads := env_var_or_default("ABIDE_MUTANTS_TEST_THREADS", "1")
mutants_per_test_timeout := env_var_or_default("ABIDE_MUTANTS_PER_TEST_TIMEOUT_SECS", "60")
mutants_build_timeout := env_var_or_default("ABIDE_MUTANTS_BUILD_TIMEOUT_SECS", "180")
mutants_output_dir := env_var_or_default("ABIDE_MUTANTS_OUTPUT_DIR", ".mutants-out")
mutants_shard_total := "4"
mutants_cli_shard_total := "32"
mutants_cli_timeout := env_var_or_default("ABIDE_MUTANTS_CLI_TIMEOUT_SECS", "1200")
mutants_cli_per_test_timeout := env_var_or_default("ABIDE_MUTANTS_CLI_PER_TEST_TIMEOUT_SECS", "75")
mutants_cli_build_timeout := env_var_or_default("ABIDE_MUTANTS_CLI_BUILD_TIMEOUT_SECS", "600")
mutants_qa_shard_total := "8"
mutants_qa_timeout := env_var_or_default("ABIDE_MUTANTS_QA_TIMEOUT_SECS", "1200")
mutants_qa_per_test_timeout := env_var_or_default("ABIDE_MUTANTS_QA_PER_TEST_TIMEOUT_SECS", "75")
mutants_qa_build_timeout := env_var_or_default("ABIDE_MUTANTS_QA_BUILD_TIMEOUT_SECS", "600")
mutants_lsp_shard_total := "8"
mutants_lsp_timeout := env_var_or_default("ABIDE_MUTANTS_LSP_TIMEOUT_SECS", "1200")
mutants_lsp_per_test_timeout := env_var_or_default("ABIDE_MUTANTS_LSP_PER_TEST_TIMEOUT_SECS", "75")
mutants_lsp_build_timeout := env_var_or_default("ABIDE_MUTANTS_LSP_BUILD_TIMEOUT_SECS", "600")
mutants_ide_shard_total := "8"
mutants_ide_timeout := env_var_or_default("ABIDE_MUTANTS_IDE_TIMEOUT_SECS", "1200")
mutants_ide_focused_timeout := env_var_or_default("ABIDE_MUTANTS_IDE_FOCUSED_TIMEOUT_SECS", "300")
mutants_ide_per_test_timeout := env_var_or_default("ABIDE_MUTANTS_IDE_PER_TEST_TIMEOUT_SECS", "75")
mutants_ide_build_timeout := env_var_or_default("ABIDE_MUTANTS_IDE_BUILD_TIMEOUT_SECS", "600")
mutants_verifier_expr_shard_total := "4"
mutants_verifier_expr_timeout := env_var_or_default("ABIDE_MUTANTS_VERIFY_EXPR_TIMEOUT_SECS", "1800")
mutants_verifier_expr_per_test_timeout := env_var_or_default("ABIDE_MUTANTS_VERIFY_EXPR_PER_TEST_TIMEOUT_SECS", "75")
mutants_verifier_expr_build_timeout := env_var_or_default("ABIDE_MUTANTS_VERIFY_EXPR_BUILD_TIMEOUT_SECS", "900")
runner := "python3 tools/run_with_timeout.py"
mutants_env := "env RUSTC_WRAPPER=sccache CARGO_BUILD_JOBS=" + mutants_cargo_build_jobs + " CMAKE_BUILD_PARALLEL_LEVEL=" + mutants_cmake_build_parallel_level
mutants_common_args := "--profile " + mutants_profile + " --jobs " + mutants_jobs + " --timeout " + mutants_per_test_timeout + " --build-timeout " + mutants_build_timeout
mutants_verifier_expr_common_args := "--profile " + mutants_profile + " --timeout " + mutants_verifier_expr_per_test_timeout + " --build-timeout " + mutants_verifier_expr_build_timeout + " --in-place --baseline skip"
mutants_cli_common_args := "--profile " + mutants_profile + " --timeout " + mutants_cli_per_test_timeout + " --build-timeout " + mutants_cli_build_timeout + " --in-place --baseline skip"
mutants_qa_common_args := "--profile " + mutants_profile + " --timeout " + mutants_qa_per_test_timeout + " --build-timeout " + mutants_qa_build_timeout + " --in-place --baseline skip"
mutants_lsp_common_args := "--profile " + mutants_profile + " --timeout " + mutants_lsp_per_test_timeout + " --build-timeout " + mutants_lsp_build_timeout + " --in-place --baseline skip"
mutants_ide_common_args := "--profile " + mutants_profile + " --timeout " + mutants_ide_per_test_timeout + " --build-timeout " + mutants_ide_build_timeout + " --in-place --baseline skip"
mutants_libtest_args := "-- --test-threads " + mutants_test_threads
ir_lowering_core_re := "lower_interface|lower_params|lower_type|lower_ty|lower_builtin|lower_const|lower_contracts|lower_while_contracts|lower_fn|lower_pred|lower_prop|lower_entity|lower_derived_field|lower_invariant|lower_fsm|lower_field|lower_action|lower_verify|lower_theorem|lower_axiom|lower_lemma|lower_scene|lower_given|lower_scene_action"
ir_lowering_system_re := "lower_system|lower_extern|lower_proc|lower_proc_params|lower_proc_node_actions|lower_proc_dep_cond|lower_query|lower_system_action|lower_event_action"
ir_lowering_expr_re := "lower_expr|lower_var_expr|lower_binop_expr|lower_call_expr|lower_call_ref_expr|lower_qualified_call_expr|lower_relation_field_call|lower_relation_project_call|lower_relation_projection_columns|lower_builtin_qualified_call|lower_qualified_expr|lower_quant_expr|lower_let_expr|lower_lambda_expr|lower_tuple_lit_expr|lower_match_expr|lower_set_comp_expr|lower_rel_comp_expr|lower_while_expr|lower_aggregate_expr|lower_saw_expr|lower_ctor_record_expr|lower_pattern|lower_pattern_for_scrutinee|lower_lit|lower_binop|lower_unop"
cli_project_helpers_re := "resolve_file_by_file_source_targets|resolve_whole_spec_source_targets|resolve_qa_script_targets|collect_qa_scripts_in_directory|build_verify_config|verify_names|validate_verify_solver_options|effective_overall_timeout|qa_summary_message|parse_simulation_scope_overrides"
qa_runner_re := "run_qa_script|run_qa_source|run_qa_script_with_hooks|run_qa_source_with_hooks|temporal_artifact_name|render_simulation_summary|explore_state_space|validate_state_space_scopes|select_exploration_systems|build_state_space_verify|slots_for_entity|state_space_artifact_name|sanitize_artifact_name|render_state_space_summary|handle_artifact_statement|load_and_build_model|rebuild_model|rebuild_ir_program|resolve_load_path|collect_abide_files"
qa_extract_re := "extract|extract_interfaces|record_entity_field_meta|record_system_field_meta|extract_entity_graphs|extract_system_graphs|collect_system_field_transitions|extract_system_field_update|extract_guard_state|finite_field_states|finite_field_states_inner|finite_variant_states|enumerate_variant_states|render_variant_state|is_graphable_field_type|extract_finite_state_name|extract_system_info|collect_event_actions|display_ir_expr|display_ir_pattern|display_ir_type"
qa_support_re := "format_result|format_path|format_transitions|format_table|format_result_json|is_reachable|find_path|terminal_states|initial_states|has_cycles|find_cycle|transitions_from|transitions_to|build_adjacency|dfs_cycle|dfs_find_cycle|qa_command_candidates|qa_query_subcommand_candidates|validate_qa_source|validate_embedded_abide_blocks|base_env_for_qa_source|validate_embedded_abide_block|build_flow_model_from_paths|validate_query_reference|query_reference_validation|temporal_target_reference_validation|model_has_owner|reference_span|artifact_parts_from_result_with_name|payload_kind_label|render_state_space_graph|render_state_space_state|render_state_space_diff|render_witness_summary|render_countermodel_summary|render_proof_artifact_summary|render_witness_timeline|render_behavior_timeline|render_witness_state|render_behavior_state|render_witness_diff|render_behavior_diff|witness_state_lines|behavior_state_lines|render_state_diff|render_operational_state|operational_state_lines|render_relational_state|relational_state_lines|render_relation_id|render_witness_value|render_slot_ref|render_record"
lsp_re := "verification_options|server_capabilities|verify_config_for_editor_policy|should_schedule_on_change|should_schedule_on_save|should_run_automatically|should_accept_document_version|document_version|uri_published_elsewhere|collect_diagnostics_for_root|collect_qa_diagnostics_for_root|is_qa_document_path|collect_lsp_diagnostic|qa_run_command_uri_arg|run_qa_script_for_uri|qa_run_source_for_uri|run_qa_source_to_json|diagnostic_to_lsp|related_information|definition_locations|source_for_path|collect_embedded_abide_diagnostics_for_root|location_for_span|uri_and_range_for_span|completion_item_for_symbol|completion_items_for_open_document|embedded_abide_block_at|abide_completion_items_for_source|qa_completion_items|qa_completion_context|current_line_prefix|keyword_completion_context|starts_with_any_keyword|is_word_boundary|keyword_completions|keyword_sort_text|position_to_offset|range_from_span|offset_to_position"
lsp_semantic_re := "quickfix_actions_requested|code_actions_for_document|missing_load_code_action|close_qa_abide_block_code_action|removed_field_keyword_code_action|quickfix_action|single_file_edit|diagnostic_code|range_to_offsets|symbol_at_document_position|occurrence_resolves_to_symbol|reference_locations_for_symbol|rename_changes_for_symbol|resolve_occurrence_symbol|symbol_declared_at|best_symbol_match|same_symbol_identity|completion_symbols_for_context|embedded_qa_abide_completion_items|qualifier_before_dot|qualifier_before_scope|qualifier_before_trigger|qa_completion_items_for_document|qa_model_reference_completion_kind|qa_model_reference_completion_items|qa_load_path_completion_items|qa_load_path_prefix|loaded_qa_flow_model|loaded_qa_workspace_index|qa_load_paths|qa_load_path_from_line"
lsp_project_re := "for_path|is_project_source|discover|empty|root|files|register_file|discover_dir|normalize_under_root|normalize_path_lexical|should_skip_project_dir|from_project|file_id|file_kind|file_kind_for_id|path|source_text|upsert_open_document|set_file_source|parse|lower|diagnostics|workspace_index|identifier_at|file_revision|file_state_mut|invalidate_file|invalidate_qa_diagnostics|qa_diagnostics|canonicalize|read_to_string|should_accept_document_version|document_version|uri_published_elsewhere|initialize|did_open|did_change|did_save|did_close|upsert_document|refresh_diagnostics|collect_diagnostics_for_root|collect_qa_diagnostics_for_root|collect_lsp_diagnostic|snapshot_source_for_path"
ide_workspace_index_re := "symbols_named|completion_symbols|symbols_in_module|module_exports|members_by_owner|enum_variants_by_type|visible_symbols|references_named|completion_context|classify_abide_cursor|classify_qa_cursor|current_line_prefix|clamp_to_char_boundary|starts_with_keyword|is_word_boundary|pending_contract_context|block_frames|block_depth|block_frame_from_header|declaration_block_kind|last_callable_decl_keyword|words|build_workspace_index|is_abide_source_path|identifier_at|dedup_symbols|dedup_occurrences|dedup_symbol_clones|name_occurrences_from_tokens|collect_program_symbols|module_name|collect_program_imports_and_includes|collect_use_decl|collect_program|collect_top_decl|collect_type_decl|collect_entity_decl|collect_interface_decl|collect_system_decl|collect_proc_decl|collect_proc_nodes|collect_program_decl|collect_proc_decl_with_owner|find_name_span|symbol_detail"
verifier_expr_property_quantifier_re := "property_quantifier_parts|encode_prop_quantifier_expr|encode_entity_quantifier_expr|encode_finite_enum_quantifier_expr|combine_finite_quantifier_predicates|encode_native_quantifier_expr|narrow_entity_quantifier_slots|extract_store_scoped_quantifier_body"
verifier_expr_property_constructor_re := "encode_prop_constructor_field_or_call_value|encode_prop_payload_field_value|encode_static_payload_field_value|payload_accessor_for_field|ctor_name_matches_for_payload_accessor|encode_prop_field_value|encode_prop_ctor_value|encode_prop_adt_ctor_value"
verifier_expr_slot_re := "try_encode_slot_expr|try_encode_slot_literal_expr|try_encode_slot_var_or_field_expr|try_encode_slot_field_expr|try_encode_slot_constructor_expr|try_encode_slot_constructor|try_encode_slot_choose_expr|try_encode_slot_operator_expr|try_encode_slot_binop_expr|try_encode_slot_unop_expr|try_encode_slot_app_expr|try_encode_slot_app|try_encode_slot_collection_expr|try_encode_slot_map_update_expr|try_encode_slot_index_expr|try_encode_slot_map_lit_expr|try_encode_slot_set_lit_expr|try_encode_slot_seq_lit_expr|try_encode_slot_finite_set_comp_expr|try_encode_slot_card_expr|try_encode_slot_sourced_set_comp_card|try_encode_slot_finite_set_comp_card|try_encode_slot_control_expr|try_encode_slot_store_quantifier"
verifier_expr_slot_shard_1_re := "try_encode_slot_expr|try_encode_slot_literal_expr|try_encode_slot_var_or_field_expr|try_encode_slot_field_expr"
verifier_expr_slot_shard_2_re := "try_encode_slot_constructor_expr|try_encode_slot_constructor|try_encode_slot_choose_expr|try_encode_slot_operator_expr|try_encode_slot_binop_expr|try_encode_slot_unop_expr"
verifier_expr_slot_shard_3_re := "try_encode_slot_app_expr|try_encode_slot_app|try_encode_slot_collection_expr|try_encode_slot_map_update_expr|try_encode_slot_index_expr|try_encode_slot_map_lit_expr|try_encode_slot_set_lit_expr|try_encode_slot_seq_lit_expr"
verifier_expr_slot_shard_4_re := "try_encode_slot_finite_set_comp_expr|try_encode_slot_card_expr|try_encode_slot_sourced_set_comp_card|try_encode_slot_finite_set_comp_card|try_encode_slot_control_expr|try_encode_slot_store_quantifier"
verifier_expr_collection_re := "encode_set_literal|encode_seq_literal|encode_map_literal|encode_collection_index|encode_collection_update|finite_literal_cardinality|encode_unique_projected_cardinality|int_sum_or_zero|unique_expr_count"
verifier_expr_pooled_support_re := "diagnose_pooled_sygus_expr_support|diagnose_pooled_sygus_expr_support_inner|unsupported_expr|is_pooled_sygus_finite_scalar_domain|ensure_pooled_sygus_expr_supported|ensure_pooled_sygus_action_supported|ensure_pooled_sygus_actions_supported|ensure_pooled_sygus_system_supported"

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

check-lang-mutants-core:
  just check-lang-mutants-core-baseline
  just check-lang-mutants-core-diagnostics
  just check-lang-mutants-core-support

check-lang-mutants-core-baseline:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-core baseline tests" -- {{mutants_env}} cargo test -p abide-core --lib {{mutants_libtest_args}}

check-lang-mutants-core-diagnostics:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-core diagnostic mutants" -- {{mutants_env}} cargo mutants {{mutants_common_args}} -p abide-core --file crates/abide-core/src/diagnostic.rs --output {{mutants_output_dir}}/mutants.out.core-diagnostics -- --lib diagnostic {{mutants_libtest_args}}

check-lang-mutants-core-support:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-core span/message mutants" -- {{mutants_env}} cargo mutants {{mutants_common_args}} -p abide-core --file crates/abide-core/src/span.rs --file crates/abide-core/src/messages.rs --output {{mutants_output_dir}}/mutants.out.core-support -- --lib {{mutants_libtest_args}}

check-lang-mutants-witness:
  just check-lang-mutants-witness-baseline
  just check-lang-mutants-witness-operational
  just check-lang-mutants-witness-relational-values
  just check-lang-mutants-witness-envelopes

check-lang-mutants-witness-baseline:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-witness baseline tests" -- {{mutants_env}} cargo test -p abide-witness --lib {{mutants_libtest_args}}

check-lang-mutants-witness-operational:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-witness operational mutants" -- {{mutants_env}} cargo mutants {{mutants_common_args}} -p abide-witness --file crates/abide-witness/src/op.rs --output {{mutants_output_dir}}/mutants.out.witness-operational -- --lib op {{mutants_libtest_args}}

check-lang-mutants-witness-relational-values:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-witness relational/value mutants" -- {{mutants_env}} cargo mutants {{mutants_common_args}} -p abide-witness --file crates/abide-witness/src/rel.rs --file crates/abide-witness/src/value.rs --output {{mutants_output_dir}}/mutants.out.witness-relational-values -- --lib {{mutants_libtest_args}}

check-lang-mutants-witness-envelopes:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-witness envelope/evidence mutants" -- {{mutants_env}} cargo mutants {{mutants_common_args}} -p abide-witness --file crates/abide-witness/src/shared.rs --file crates/abide-witness/src/evidence.rs --output {{mutants_output_dir}}/mutants.out.witness-envelopes -- --lib {{mutants_libtest_args}}

check-lang-mutants-syntax-core:
  just check-lang-mutants-syntax-core-shard 1
  just check-lang-mutants-syntax-core-shard 2
  just check-lang-mutants-syntax-core-shard 3
  just check-lang-mutants-syntax-core-shard 4

check-lang-mutants-syntax-core-shard shard:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-syntax parser core mutants shard {{shard}}/{{mutants_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_common_args}} --shard "$(({{shard}} - 1))/{{mutants_shard_total}}" -p abide-syntax --file crates/abide-syntax/src/parse/mod.rs --output {{mutants_output_dir}}/mutants.out.syntax-core.{{shard}}-of-{{mutants_shard_total}} -- --lib parse {{mutants_libtest_args}}

check-lang-mutants-syntax-expr:
  just check-lang-mutants-syntax-expr-shard 1
  just check-lang-mutants-syntax-expr-shard 2
  just check-lang-mutants-syntax-expr-shard 3
  just check-lang-mutants-syntax-expr-shard 4

check-lang-mutants-syntax-expr-shard shard:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-syntax expression parser mutants shard {{shard}}/{{mutants_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_common_args}} --shard "$(({{shard}} - 1))/{{mutants_shard_total}}" -p abide-syntax --file crates/abide-syntax/src/parse/expr.rs --output {{mutants_output_dir}}/mutants.out.syntax-expr.{{shard}}-of-{{mutants_shard_total}} -- --lib parse {{mutants_libtest_args}}

check-lang-mutants-syntax-system:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-syntax system parser mutants" -- {{mutants_env}} cargo mutants {{mutants_common_args}} -p abide-syntax --file crates/abide-syntax/src/parse/system.rs --output {{mutants_output_dir}}/mutants.out.syntax-system -- --lib parse {{mutants_libtest_args}}

check-lang-mutants-syntax-types:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-syntax type parser mutants" -- {{mutants_env}} cargo mutants {{mutants_common_args}} -p abide-syntax --file crates/abide-syntax/src/parse/types.rs --output {{mutants_output_dir}}/mutants.out.syntax-types -- --lib parse {{mutants_libtest_args}}

check-lang-mutants-syntax-parser: check-lang-mutants-syntax-core check-lang-mutants-syntax-expr check-lang-mutants-syntax-system check-lang-mutants-syntax-types

check-lang-mutants-sema-namespace:
  just check-lang-mutants-sema-namespace-shard 1
  just check-lang-mutants-sema-namespace-shard 2
  just check-lang-mutants-sema-namespace-shard 3
  just check-lang-mutants-sema-namespace-shard 4

check-lang-mutants-sema-namespace-shard shard:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-sema namespace mutants shard {{shard}}/{{mutants_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_common_args}} --shard "$(({{shard}} - 1))/{{mutants_shard_total}}" -p abide-sema --file crates/abide-sema/src/elab/env.rs --re 'build_working_namespace|key_matches_module|flatten_sorted' --output {{mutants_output_dir}}/mutants.out.sema-namespace.{{shard}}-of-{{mutants_shard_total}} -- --lib build_working_namespace {{mutants_libtest_args}}

check-lang-mutants-sema-loader:
  just check-lang-mutants-sema-loader-shard 1
  just check-lang-mutants-sema-loader-shard 2
  just check-lang-mutants-sema-loader-shard 3
  just check-lang-mutants-sema-loader-shard 4

check-lang-mutants-sema-loader-shard shard:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-sema loader mutants shard {{shard}}/{{mutants_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_common_args}} --shard "$(({{shard}} - 1))/{{mutants_shard_total}}" -p abide-sema --file crates/abide-sema/src/loader.rs --output {{mutants_output_dir}}/mutants.out.sema-loader.{{shard}}-of-{{mutants_shard_total}} -- --lib loader {{mutants_libtest_args}}

check-lang-mutants-sema-resolution-imports:
  just check-lang-mutants-sema-resolution-imports-shard 1
  just check-lang-mutants-sema-resolution-imports-shard 2
  just check-lang-mutants-sema-resolution-imports-shard 3
  just check-lang-mutants-sema-resolution-imports-shard 4

check-lang-mutants-sema-resolution-imports-shard shard:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-sema import resolution mutants shard {{shard}}/{{mutants_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_common_args}} --shard "$(({{shard}} - 1))/{{mutants_shard_total}}" -p abide-sema --file crates/abide-sema/src/elab/resolve/mod.rs --re 'resolve_use_declarations|check_import_target|check_use_cycles|dfs_use_cycle|import_is_visible|bindings_without' --output {{mutants_output_dir}}/mutants.out.sema-resolution-imports.{{shard}}-of-{{mutants_shard_total}} -- --lib resolve {{mutants_libtest_args}}

check-lang-mutants-sema-resolution-types:
  just check-lang-mutants-sema-resolution-types-core
  just check-lang-mutants-sema-resolution-types-monomorphize
  just check-lang-mutants-sema-resolution-types-validate

check-lang-mutants-sema-resolution-types-core:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-sema type resolution core mutants" -- {{mutants_env}} cargo mutants {{mutants_common_args}} -p abide-sema --file crates/abide-sema/src/elab/resolve/mod.rs --re 'resolve_all_types|resolve_type_refinement_predicates|resolve_ty|resolve_params_lr|base_ty_without_refinement' --output {{mutants_output_dir}}/mutants.out.sema-resolution-types-core -- --lib resolve {{mutants_libtest_args}}

check-lang-mutants-sema-resolution-types-monomorphize:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-sema generic monomorphization mutants" -- {{mutants_env}} cargo mutants {{mutants_common_args}} -p abide-sema --file crates/abide-sema/src/elab/resolve/monomorphize.rs --re 'format_mono_name|mono_ty_name|substitute_ty|monomorphize_inline|monomorphize_variant_fields|resolve_nested_generics|monomorphize_generics|collect_all_param_uses' --output {{mutants_output_dir}}/mutants.out.sema-resolution-types-monomorphize -- --lib monomorphize {{mutants_libtest_args}}

check-lang-mutants-sema-resolution-types-validate:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-sema unresolved type validation mutants" -- {{mutants_env}} cargo mutants {{mutants_common_args}} -p abide-sema --file crates/abide-sema/src/elab/resolve/validate.rs --re 'validate_remaining_type_params|validate_unresolved_types|collect_ty_params|collect_unresolved' --output {{mutants_output_dir}}/mutants.out.sema-resolution-types-validate -- --lib validate {{mutants_libtest_args}}

check-lang-mutants-sema-resolution-expr:
  just check-lang-mutants-sema-resolution-expr-core
  just check-lang-mutants-sema-resolution-expr-relation

check-lang-mutants-sema-resolution-expr-core:
  just check-lang-mutants-sema-resolution-expr-core-shard 1
  just check-lang-mutants-sema-resolution-expr-core-shard 2
  just check-lang-mutants-sema-resolution-expr-core-shard 3
  just check-lang-mutants-sema-resolution-expr-core-shard 4

check-lang-mutants-sema-resolution-expr-core-shard shard:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-sema expression resolution core mutants shard {{shard}}/{{mutants_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_common_args}} --shard "$(({{shard}} - 1))/{{mutants_shard_total}}" -p abide-sema --file crates/abide-sema/src/elab/resolve/expr.rs --re 'resolve_expr|resolve_var_type|resolve_ctor_type_from_context|resolve_comparison_ctor_from_context|infer_field_type|infer_qualcall_type|infer_numeric_binop_type|infer_index_type|set_source_element_type' --output {{mutants_output_dir}}/mutants.out.sema-resolution-expr-core.{{shard}}-of-{{mutants_shard_total}} -- --lib resolve {{mutants_libtest_args}}

check-lang-mutants-sema-resolution-expr-relation:
  just check-lang-mutants-sema-resolution-expr-relation-shard 1
  just check-lang-mutants-sema-resolution-expr-relation-shard 2
  just check-lang-mutants-sema-resolution-expr-relation-shard 3
  just check-lang-mutants-sema-resolution-expr-relation-shard 4

check-lang-mutants-sema-resolution-expr-relation-shard shard:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-sema relation expression mutants shard {{shard}}/{{mutants_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_common_args}} --shard "$(({{shard}} - 1))/{{mutants_shard_total}}" -p abide-sema --file crates/abide-sema/src/elab/resolve/expr.rs --re 'relation_columns|relation_type_from_columns|relation_type_from_projection|ty_same|infer_relation_join_type|infer_relation_set_op_type|infer_relation_product_type|relation_project_indices|infer_relation_project_type|infer_relation_transpose_type|infer_relation_closure_type|infer_relation_field_type' --output {{mutants_output_dir}}/mutants.out.sema-resolution-expr-relation.{{shard}}-of-{{mutants_shard_total}} -- --lib relation {{mutants_libtest_args}}

check-lang-mutants-sema-resolution-assumptions:
  just check-lang-mutants-sema-resolution-assumptions-core
  just check-lang-mutants-sema-resolution-assumptions-event-path

check-lang-mutants-sema-resolution-assumptions-core:
  just check-lang-mutants-sema-resolution-assumptions-core-shard 1
  just check-lang-mutants-sema-resolution-assumptions-core-shard 2

check-lang-mutants-sema-resolution-assumptions-core-shard shard:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-sema assumption resolution mutants shard {{shard}}/2" -- {{mutants_env}} cargo mutants {{mutants_common_args}} --shard "$(({{shard}} - 1))/2" -p abide-sema --file crates/abide-sema/src/elab/resolve/assumptions.rs --re 'resolve_assumption_sets|build_assume_delta|build_assume_delta_with_bindings|merge_delta_into|check_under_add_only_resolved|resolve_by_lemmas_subset_containment|format_assumption_set|compute_missing|populate_assumption_set|populate_assumption_set_from_items' --output {{mutants_output_dir}}/mutants.out.sema-resolution-assumptions-core.{{shard}}-of-2 -- --lib assumption {{mutants_libtest_args}}

check-lang-mutants-sema-resolution-assumptions-event-path:
  just check-lang-mutants-sema-resolution-assumptions-event-path-shard 1
  just check-lang-mutants-sema-resolution-assumptions-event-path-shard 2

check-lang-mutants-sema-resolution-assumptions-event-path-shard shard:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-sema event path resolution mutants shard {{shard}}/2" -- {{mutants_env}} cargo mutants {{mutants_common_args}} --shard "$(({{shard}} - 1))/2" -p abide-sema --file crates/abide-sema/src/elab/resolve/mod.rs --re 'resolve_event_path' --output {{mutants_output_dir}}/mutants.out.sema-resolution-assumptions-event-path.{{shard}}-of-2 -- --lib event_path {{mutants_libtest_args}}

check-lang-mutants-sema-checker:
  just check-lang-mutants-sema-checker-core
  just check-lang-mutants-sema-checker-entity
  just check-lang-mutants-sema-checker-system
  just check-lang-mutants-sema-checker-matches
  just check-lang-mutants-sema-checker-ctors

check-lang-mutants-sema-checker-core:
  just check-lang-mutants-sema-checker-core-shard 1
  just check-lang-mutants-sema-checker-core-shard 2
  just check-lang-mutants-sema-checker-core-shard 3
  just check-lang-mutants-sema-checker-core-shard 4

check-lang-mutants-sema-checker-core-shard shard:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-sema checker core mutants shard {{shard}}/{{mutants_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_common_args}} --shard "$(({{shard}} - 1))/{{mutants_shard_total}}" -p abide-sema --file crates/abide-sema/src/elab/check/mod.rs --re 'check_type|check_collection_homogeneity|types_compatible|expr_compatible_with_ty|check_unresolved_constructors|check_fn_contracts|check_refinement_predicates|check_verifier_surface_expr|check_verifier_surface_expr_allowing_sequence|find_sequence_composition_span|find_unsupported_verifier_expr|check_pred_prop_cycles|collect_name_refs|dfs_find_cycle|collect_epattern_vars' --output {{mutants_output_dir}}/mutants.out.sema-checker-core.{{shard}}-of-{{mutants_shard_total}} -- --lib check {{mutants_libtest_args}}

check-lang-mutants-sema-checker-entity:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-sema entity checker mutants" -- {{mutants_env}} cargo mutants {{mutants_common_args}} -p abide-sema --file crates/abide-sema/src/elab/check/entity.rs --re 'check_entity|check_invariant_body_no_liveness|check_field|check_action|check_assignment' --output {{mutants_output_dir}}/mutants.out.sema-checker-entity -- --lib entity {{mutants_libtest_args}}

check-lang-mutants-sema-checker-system:
  just check-lang-mutants-sema-checker-system-core
  just check-lang-mutants-sema-checker-system-interface
  just check-lang-mutants-sema-checker-system-extern
  just check-lang-mutants-sema-checker-system-return
  just check-lang-mutants-sema-checker-system-proc-deps

check-lang-mutants-sema-checker-system-core:
  just check-lang-mutants-sema-checker-system-core-shard 1
  just check-lang-mutants-sema-checker-system-core-shard 2
  just check-lang-mutants-sema-checker-system-core-shard 3
  just check-lang-mutants-sema-checker-system-core-shard 4

check-lang-mutants-sema-checker-system-core-shard shard:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-sema system checker core mutants shard {{shard}}/{{mutants_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_common_args}} --shard "$(({{shard}} - 1))/{{mutants_shard_total}}" -p abide-sema --file crates/abide-sema/src/elab/check/system.rs --re 'check_system' --output {{mutants_output_dir}}/mutants.out.sema-checker-system-core.{{shard}}-of-{{mutants_shard_total}} -- --lib system {{mutants_libtest_args}}

check-lang-mutants-sema-checker-system-interface:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-sema interface conformance mutants" -- {{mutants_env}} cargo mutants {{mutants_common_args}} -p abide-sema --file crates/abide-sema/src/elab/check/system.rs --re 'check_interface_conformance' --output {{mutants_output_dir}}/mutants.out.sema-checker-system-interface -- --lib interface {{mutants_libtest_args}}

check-lang-mutants-sema-checker-system-extern:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-sema extern checker mutants" -- {{mutants_env}} cargo mutants {{mutants_common_args}} -p abide-sema --file crates/abide-sema/src/elab/check/system.rs --re 'check_extern' --output {{mutants_output_dir}}/mutants.out.sema-checker-system-extern -- --lib check_extern {{mutants_libtest_args}}

check-lang-mutants-sema-checker-system-return:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-sema system return helper mutants" -- {{mutants_env}} cargo mutants {{mutants_common_args}} -p abide-sema --file crates/abide-sema/src/elab/check/system.rs --re 'extract_return_ctor_name|extract_return_payload' --output {{mutants_output_dir}}/mutants.out.sema-checker-system-return -- --lib return {{mutants_libtest_args}}

check-lang-mutants-sema-checker-system-proc-deps:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-sema proc dependency checker mutants" -- {{mutants_env}} cargo mutants {{mutants_common_args}} -p abide-sema --file crates/abide-sema/src/elab/check/system.rs --re 'validate_proc_dep_cond' --output {{mutants_output_dir}}/mutants.out.sema-checker-system-proc-deps -- --lib proc_dep {{mutants_libtest_args}}

check-lang-mutants-sema-checker-matches:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-sema match checker mutants" -- {{mutants_env}} cargo mutants {{mutants_common_args}} -p abide-sema --file crates/abide-sema/src/elab/check/matches.rs --re 'check_match_exhaustiveness|pattern_is_catchall|collect_covered_ctors|check_pattern_shape|resolve_to_enum_info|resolve_field_type' --output {{mutants_output_dir}}/mutants.out.sema-checker-matches -- --lib match {{mutants_libtest_args}}

check-lang-mutants-sema-checker-ctors:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-sema constructor checker mutants" -- {{mutants_env}} cargo mutants {{mutants_common_args}} -p abide-sema --file crates/abide-sema/src/elab/check/ctors.rs --re 'walk_event_action_for_ctor_check|check_ctor_records_in_expr' --output {{mutants_output_dir}}/mutants.out.sema-checker-ctors -- --lib ctor {{mutants_libtest_args}}

check-lang-mutants-sema-diagnostics:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-sema diagnostic mutants" -- {{mutants_env}} cargo mutants {{mutants_common_args}} -p abide-sema --file crates/abide-sema/src/elab/error.rs --output {{mutants_output_dir}}/mutants.out.sema-diagnostics -- --lib error {{mutants_libtest_args}}

check-lang-mutants-ir-lowering:
  just check-lang-mutants-ir-lowering-core
  just check-lang-mutants-ir-lowering-system
  just check-lang-mutants-ir-lowering-expr
  just check-lang-mutants-ir-lowering-qualify

check-lang-mutants-ir-lowering-core:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-ir core lowering mutants" -- {{mutants_env}} cargo mutants {{mutants_common_args}} -p abide-ir --file crates/abide-ir/src/ir/lower/mod.rs --re '{{ir_lowering_core_re}}' --output {{mutants_output_dir}}/mutants.out.ir-lowering-core -- --lib lower {{mutants_libtest_args}}

check-lang-mutants-ir-lowering-system:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-ir system lowering mutants" -- {{mutants_env}} cargo mutants {{mutants_common_args}} -p abide-ir --file crates/abide-ir/src/ir/lower/system.rs --re '{{ir_lowering_system_re}}' --output {{mutants_output_dir}}/mutants.out.ir-lowering-system -- --lib lower {{mutants_libtest_args}}

check-lang-mutants-ir-lowering-expr:
  just check-lang-mutants-ir-lowering-expr-shard 1
  just check-lang-mutants-ir-lowering-expr-shard 2
  just check-lang-mutants-ir-lowering-expr-shard 3
  just check-lang-mutants-ir-lowering-expr-shard 4

check-lang-mutants-ir-lowering-expr-shard shard:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-ir expression lowering mutants shard {{shard}}/{{mutants_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_common_args}} --shard "$(({{shard}} - 1))/{{mutants_shard_total}}" -p abide-ir --file crates/abide-ir/src/ir/lower/expr.rs --re '{{ir_lowering_expr_re}}' --output {{mutants_output_dir}}/mutants.out.ir-lowering-expr.{{shard}}-of-{{mutants_shard_total}} -- --lib lower {{mutants_libtest_args}}

check-lang-mutants-ir-lowering-qualify:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-ir qualification lowering mutants" -- {{mutants_env}} cargo mutants {{mutants_common_args}} -p abide-ir --file crates/abide-ir/src/ir/lower/qualify.rs --re 'qualify_query_vars_scoped|qualify_action_query_vars' --output {{mutants_output_dir}}/mutants.out.ir-lowering-qualify -- --lib qualify {{mutants_libtest_args}}

check-lang-mutants-cli-project:
  just check-lang-mutants-cli-project-baseline
  just check-lang-mutants-cli-project-targets
  just check-lang-mutants-cli-project-helpers

check-lang-mutants-cli-project-baseline:
  {{runner}} --timeout-secs {{mutants_cli_timeout}} --label "abide CLI project mutants-profile prebuild" -- {{mutants_env}} cargo test -p abide --lib --profile {{mutants_profile}} --no-run
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide CLI project baseline tests" -- {{mutants_env}} cargo test -p abide --lib cli::tests {{mutants_libtest_args}}
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide target discovery baseline tests" -- {{mutants_env}} cargo test -p abide --lib targets::tests {{mutants_libtest_args}}

check-lang-mutants-cli-project-targets:
  for shard in {1..32}; do just check-lang-mutants-cli-project-targets-shard "$shard"; done

check-lang-mutants-cli-project-targets-shard shard:
  {{runner}} --timeout-secs {{mutants_cli_timeout}} --label "abide CLI target discovery mutants shard {{shard}}/{{mutants_cli_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_cli_common_args}} --shard "$(({{shard}} - 1))/{{mutants_cli_shard_total}}" -p abide --file crates/abide/src/targets.rs --output {{mutants_output_dir}}/mutants.out.cli-project-targets.{{shard}}-of-{{mutants_cli_shard_total}} -- --lib targets {{mutants_libtest_args}}

check-lang-mutants-cli-project-helpers:
  for shard in {1..32}; do just check-lang-mutants-cli-project-helpers-shard "$shard"; done

check-lang-mutants-cli-project-helpers-shard shard:
  {{runner}} --timeout-secs {{mutants_cli_timeout}} --label "abide CLI helper mutants shard {{shard}}/{{mutants_cli_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_cli_common_args}} --shard "$(({{shard}} - 1))/{{mutants_cli_shard_total}}" -p abide --file crates/abide/src/cli.rs --re '{{cli_project_helpers_re}}' --output {{mutants_output_dir}}/mutants.out.cli-project-helpers.{{shard}}-of-{{mutants_cli_shard_total}} -- --lib cli {{mutants_libtest_args}}

check-lang-mutants-qa:
  just check-lang-mutants-qa-baseline
  just check-lang-mutants-qa-parse
  just check-lang-mutants-qa-exec
  just check-lang-mutants-qa-runner
  just check-lang-mutants-qa-extract
  just check-lang-mutants-qa-support

check-lang-mutants-qa-baseline:
  {{runner}} --timeout-secs {{mutants_qa_timeout}} --label "abide QA mutants-profile prebuild" -- {{mutants_env}} cargo test -p abide-qa --lib --profile {{mutants_profile}} --no-run
  {{runner}} --timeout-secs {{mutants_qa_timeout}} --label "abide QA mutants-profile baseline tests" -- {{mutants_env}} cargo test -p abide-qa --lib --profile {{mutants_profile}} {{mutants_libtest_args}}

check-lang-mutants-qa-parse:
  for shard in {1..8}; do just check-lang-mutants-qa-parse-shard "$shard"; done

check-lang-mutants-qa-parse-shard shard:
  {{runner}} --timeout-secs {{mutants_qa_timeout}} --label "abide QA parser mutants shard {{shard}}/{{mutants_qa_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_qa_common_args}} --shard "$(({{shard}} - 1))/{{mutants_qa_shard_total}}" -p abide-qa --file crates/abide-qa/src/qa/parse.rs --output {{mutants_output_dir}}/mutants.out.qa-parse.{{shard}}-of-{{mutants_qa_shard_total}} -- --lib parse {{mutants_libtest_args}}

check-lang-mutants-qa-exec:
  for shard in {1..8}; do just check-lang-mutants-qa-exec-shard "$shard"; done

check-lang-mutants-qa-exec-shard shard:
  {{runner}} --timeout-secs {{mutants_qa_timeout}} --label "abide QA execution mutants shard {{shard}}/{{mutants_qa_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_qa_common_args}} --shard "$(({{shard}} - 1))/{{mutants_qa_shard_total}}" -p abide-qa --file crates/abide-qa/src/qa/exec.rs --output {{mutants_output_dir}}/mutants.out.qa-exec.{{shard}}-of-{{mutants_qa_shard_total}} -- --lib exec {{mutants_libtest_args}}

check-lang-mutants-qa-runner:
  for shard in {1..8}; do just check-lang-mutants-qa-runner-shard "$shard"; done

check-lang-mutants-qa-runner-shard shard:
  {{runner}} --timeout-secs {{mutants_qa_timeout}} --label "abide QA runner mutants shard {{shard}}/{{mutants_qa_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_qa_common_args}} --shard "$(({{shard}} - 1))/{{mutants_qa_shard_total}}" -p abide-qa --file crates/abide-qa/src/qa/runner.rs --re '{{qa_runner_re}}' --output {{mutants_output_dir}}/mutants.out.qa-runner.{{shard}}-of-{{mutants_qa_shard_total}} -- --lib runner {{mutants_libtest_args}}

check-lang-mutants-qa-extract:
  for shard in {1..8}; do just check-lang-mutants-qa-extract-shard "$shard"; done

check-lang-mutants-qa-extract-shard shard:
  {{runner}} --timeout-secs {{mutants_qa_timeout}} --label "abide QA extraction mutants shard {{shard}}/{{mutants_qa_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_qa_common_args}} --shard "$(({{shard}} - 1))/{{mutants_qa_shard_total}}" -p abide-qa --file crates/abide-qa/src/qa/extract.rs --re '{{qa_extract_re}}' --output {{mutants_output_dir}}/mutants.out.qa-extract.{{shard}}-of-{{mutants_qa_shard_total}} -- --lib extract {{mutants_libtest_args}}

check-lang-mutants-qa-support:
  just check-lang-mutants-qa-format
  just check-lang-mutants-qa-graph
  just check-lang-mutants-qa-complete
  just check-lang-mutants-qa-validate
  just check-lang-mutants-qa-artifacts

check-lang-mutants-qa-format:
  {{runner}} --timeout-secs {{mutants_qa_timeout}} --label "abide QA formatting mutants" -- {{mutants_env}} cargo mutants {{mutants_qa_common_args}} -p abide-qa --file crates/abide-qa/src/qa/fmt.rs --re '{{qa_support_re}}' --output {{mutants_output_dir}}/mutants.out.qa-format -- --lib fmt {{mutants_libtest_args}}

check-lang-mutants-qa-graph:
  {{runner}} --timeout-secs {{mutants_qa_timeout}} --label "abide QA graph mutants" -- {{mutants_env}} cargo mutants {{mutants_qa_common_args}} -p abide-qa --file crates/abide-qa/src/qa/graph.rs --re '{{qa_support_re}}' --output {{mutants_output_dir}}/mutants.out.qa-graph -- --lib graph {{mutants_libtest_args}}

check-lang-mutants-qa-complete:
  {{runner}} --timeout-secs {{mutants_qa_timeout}} --label "abide QA completion mutants" -- {{mutants_env}} cargo mutants {{mutants_qa_common_args}} -p abide-qa --file crates/abide-qa/src/qa/complete.rs --re '{{qa_support_re}}' --output {{mutants_output_dir}}/mutants.out.qa-complete -- --lib complete {{mutants_libtest_args}}

check-lang-mutants-qa-validate:
  {{runner}} --timeout-secs {{mutants_qa_timeout}} --label "abide QA validation mutants" -- {{mutants_env}} cargo mutants {{mutants_qa_common_args}} -p abide-qa --file crates/abide-qa/src/qa/validate.rs --re '{{qa_support_re}}' --output {{mutants_output_dir}}/mutants.out.qa-validate -- --lib validate {{mutants_libtest_args}}

check-lang-mutants-qa-artifacts:
  {{runner}} --timeout-secs {{mutants_qa_timeout}} --label "abide QA artifact rendering mutants" -- {{mutants_env}} cargo mutants {{mutants_qa_common_args}} -p abide-qa --file crates/abide-qa/src/qa/artifacts.rs --re '{{qa_support_re}}' --output {{mutants_output_dir}}/mutants.out.qa-artifacts -- --lib artifacts {{mutants_libtest_args}}

check-lang-mutants-lsp:
  just check-lang-mutants-lsp-baseline
  for shard in {1..8}; do just check-lang-mutants-lsp-shard "$shard"; done

check-lang-mutants-lsp-baseline:
  {{runner}} --timeout-secs {{mutants_lsp_timeout}} --label "abide LSP mutants-profile prebuild" -- {{mutants_env}} cargo test -p abide-lsp --profile {{mutants_profile}} --no-run
  {{runner}} --timeout-secs {{mutants_lsp_timeout}} --label "abide LSP mutants-profile baseline tests" -- {{mutants_env}} cargo test -p abide-lsp --profile {{mutants_profile}} {{mutants_libtest_args}}

check-lang-mutants-lsp-shard shard:
  {{runner}} --timeout-secs {{mutants_lsp_timeout}} --label "abide LSP mutants shard {{shard}}/{{mutants_lsp_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_lsp_common_args}} --shard "$(({{shard}} - 1))/{{mutants_lsp_shard_total}}" -p abide-lsp --file crates/abide-lsp/src/main.rs --re '{{lsp_re}}' --output {{mutants_output_dir}}/mutants.out.lsp.{{shard}}-of-{{mutants_lsp_shard_total}} -- --bin abide-lsp tests {{mutants_libtest_args}}

check-lang-mutants-lsp-semantic:
  just check-lang-mutants-lsp-baseline
  for shard in {1..8}; do just check-lang-mutants-lsp-semantic-shard "$shard"; done

check-lang-mutants-lsp-semantic-shard shard:
  {{runner}} --timeout-secs {{mutants_lsp_timeout}} --label "abide LSP semantic mutants shard {{shard}}/{{mutants_lsp_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_lsp_common_args}} --shard "$(({{shard}} - 1))/{{mutants_lsp_shard_total}}" -p abide-lsp --file crates/abide-lsp/src/main.rs --re '{{lsp_semantic_re}}' --output {{mutants_output_dir}}/mutants.out.lsp-semantic.{{shard}}-of-{{mutants_lsp_shard_total}} -- --bin abide-lsp tests {{mutants_libtest_args}}

check-lang-mutants-lsp-project:
  just check-lang-mutants-lsp-baseline
  for shard in {1..8}; do just check-lang-mutants-lsp-project-shard "$shard"; done

check-lang-mutants-lsp-project-shard shard:
  {{runner}} --timeout-secs {{mutants_lsp_timeout}} --label "abide LSP project mutants shard {{shard}}/{{mutants_lsp_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_lsp_common_args}} --shard "$(({{shard}} - 1))/{{mutants_lsp_shard_total}}" -p abide-lsp --file crates/abide-lsp/src/main.rs --re '{{lsp_project_re}}' --output {{mutants_output_dir}}/mutants.out.lsp-project.{{shard}}-of-{{mutants_lsp_shard_total}} -- --bin abide-lsp tests {{mutants_libtest_args}}

check-lang-mutants-ide-workspace-index:
  just check-lang-mutants-ide-workspace-index-baseline
  for shard in {1..8}; do just check-lang-mutants-ide-workspace-index-shard "$shard"; done

check-lang-mutants-ide-workspace-index-baseline:
  {{runner}} --timeout-secs {{mutants_ide_timeout}} --label "abide IDE workspace-index mutants-profile prebuild" -- {{mutants_env}} cargo test -p abide --lib --profile {{mutants_profile}} --no-run
  {{runner}} --timeout-secs {{mutants_ide_timeout}} --label "abide IDE workspace-index baseline tests" -- {{mutants_env}} cargo test -p abide --lib --profile {{mutants_profile}} ide::tests {{mutants_libtest_args}}

check-lang-mutants-ide-workspace-index-shard shard:
  {{runner}} --timeout-secs {{mutants_ide_timeout}} --label "abide IDE workspace-index mutants shard {{shard}}/{{mutants_ide_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_ide_common_args}} --shard "$(({{shard}} - 1))/{{mutants_ide_shard_total}}" -p abide --file crates/abide/src/ide.rs --re '{{ide_workspace_index_re}}' --output {{mutants_output_dir}}/mutants.out.ide-workspace-index.{{shard}}-of-{{mutants_ide_shard_total}} -- --lib ide {{mutants_libtest_args}}

check-lang-mutants-ide-workspace-index-focused:
  just check-lang-mutants-ide-workspace-index-boundary
  just check-lang-mutants-ide-workspace-index-block-frames
  just check-lang-mutants-ide-workspace-index-find-name-span

check-lang-mutants-ide-workspace-index-boundary:
  {{runner}} --timeout-secs {{mutants_ide_focused_timeout}} --label "abide IDE boundary helper mutants" -- {{mutants_env}} cargo mutants {{mutants_ide_common_args}} -p abide --file crates/abide/src/ide.rs --re 'clamp_to_char_boundary' --output {{mutants_output_dir}}/mutants.out.ide-workspace-index.boundary -- --lib cursor_helpers_handle_utf8_boundaries_keywords_and_nested_blocks {{mutants_libtest_args}}

check-lang-mutants-ide-workspace-index-block-frames:
  {{runner}} --timeout-secs {{mutants_ide_focused_timeout}} --label "abide IDE block-frame helper mutants" -- {{mutants_env}} cargo mutants {{mutants_ide_common_args}} -p abide --file crates/abide/src/ide.rs --re 'block_frames|block_depth|block_frame_from_header' --output {{mutants_output_dir}}/mutants.out.ide-workspace-index.block-frames -- --lib cursor_helpers_handle_utf8_boundaries_keywords_and_nested_blocks {{mutants_libtest_args}}

check-lang-mutants-ide-workspace-index-find-name-span:
  {{runner}} --timeout-secs {{mutants_ide_focused_timeout}} --label "abide IDE name-span helper mutants" -- {{mutants_env}} cargo mutants {{mutants_ide_common_args}} -p abide --file crates/abide/src/ide.rs --re 'find_name_span' --output {{mutants_output_dir}}/mutants.out.ide-workspace-index.find-name-span -- --lib name_span_and_symbol_detail_are_scoped_to_decl_span {{mutants_libtest_args}}

check-lang-mutants-verifier-expr:
  just check-lang-mutants-verifier-expr-property-quantifier
  just check-lang-mutants-verifier-expr-property-constructor
  just check-lang-mutants-verifier-expr-slot
  just check-lang-mutants-verifier-expr-collections
  just check-lang-mutants-verifier-expr-pooled-support

check-lang-mutants-verifier-expr-property-quantifier:
  {{runner}} --timeout-secs {{mutants_verifier_expr_timeout}} --label "abide verifier property quantifier helper mutants" -- {{mutants_env}} cargo mutants {{mutants_verifier_expr_common_args}} -p abide-verify --file crates/abide-verify/src/verify/property.rs --re '{{verifier_expr_property_quantifier_re}}' --output {{mutants_output_dir}}/mutants.out.verifier-expr.property-quantifier -- --lib encode_prop_quantifier {{mutants_libtest_args}}

check-lang-mutants-verifier-expr-property-constructor:
  {{runner}} --timeout-secs {{mutants_verifier_expr_timeout}} --label "abide verifier property constructor/field/call helper mutants" -- {{mutants_env}} cargo mutants {{mutants_verifier_expr_common_args}} -p abide-verify --file crates/abide-verify/src/verify/property.rs --re '{{verifier_expr_property_constructor_re}}' --output {{mutants_output_dir}}/mutants.out.verifier-expr.property-constructor -- --lib encode_prop_constructor_field_or_call_helper_covers_dispatch_family {{mutants_libtest_args}}

check-lang-mutants-verifier-expr-slot:
  just check-lang-mutants-verifier-expr-slot-shard-1
  just check-lang-mutants-verifier-expr-slot-shard-2
  just check-lang-mutants-verifier-expr-slot-shard-3
  just check-lang-mutants-verifier-expr-slot-shard-4

check-lang-mutants-verifier-expr-slot-shard shard:
  just check-lang-mutants-verifier-expr-slot-shard-{{shard}}

check-lang-mutants-verifier-expr-slot-shard-1:
  {{runner}} --timeout-secs {{mutants_verifier_expr_timeout}} --label "abide verifier slot expression helper mutants shard 1/{{mutants_verifier_expr_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_verifier_expr_common_args}} -p abide-verify --file crates/abide-verify/src/verify/harness/expr.rs --re '{{verifier_expr_slot_shard_1_re}}' --output {{mutants_output_dir}}/mutants.out.verifier-expr.slot.1-of-{{mutants_verifier_expr_shard_total}} -- --lib slot_expr {{mutants_libtest_args}}

check-lang-mutants-verifier-expr-slot-shard-2:
  {{runner}} --timeout-secs {{mutants_verifier_expr_timeout}} --label "abide verifier slot expression helper mutants shard 2/{{mutants_verifier_expr_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_verifier_expr_common_args}} -p abide-verify --file crates/abide-verify/src/verify/harness/expr.rs --re '{{verifier_expr_slot_shard_2_re}}' --output {{mutants_output_dir}}/mutants.out.verifier-expr.slot.2-of-{{mutants_verifier_expr_shard_total}} -- --lib slot_expr {{mutants_libtest_args}}

check-lang-mutants-verifier-expr-slot-shard-3:
  {{runner}} --timeout-secs {{mutants_verifier_expr_timeout}} --label "abide verifier slot expression helper mutants shard 3/{{mutants_verifier_expr_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_verifier_expr_common_args}} -p abide-verify --file crates/abide-verify/src/verify/harness/expr.rs --re '{{verifier_expr_slot_shard_3_re}}' --output {{mutants_output_dir}}/mutants.out.verifier-expr.slot.3-of-{{mutants_verifier_expr_shard_total}} -- --lib slot_expr {{mutants_libtest_args}}

check-lang-mutants-verifier-expr-slot-shard-4:
  {{runner}} --timeout-secs {{mutants_verifier_expr_timeout}} --label "abide verifier slot expression helper mutants shard 4/{{mutants_verifier_expr_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_verifier_expr_common_args}} -p abide-verify --file crates/abide-verify/src/verify/harness/expr.rs --re '{{verifier_expr_slot_shard_4_re}}' --output {{mutants_output_dir}}/mutants.out.verifier-expr.slot.4-of-{{mutants_verifier_expr_shard_total}} -- --lib slot_expr {{mutants_libtest_args}}

check-lang-mutants-verifier-expr-collections:
  {{runner}} --timeout-secs {{mutants_verifier_expr_timeout}} --label "abide verifier finite collection helper mutants" -- {{mutants_env}} cargo mutants {{mutants_verifier_expr_common_args}} -p abide-verify --file crates/abide-verify/src/verify/collections.rs --re '{{verifier_expr_collection_re}}' --output {{mutants_output_dir}}/mutants.out.verifier-expr.collections -- --lib finite_collection_helpers {{mutants_libtest_args}}

check-lang-mutants-verifier-expr-pooled-support:
  {{runner}} --timeout-secs {{mutants_verifier_expr_timeout}} --label "abide verifier pooled SyGuS support diagnostic mutants" -- {{mutants_env}} cargo mutants {{mutants_verifier_expr_common_args}} -p abide-verify --file crates/abide-verify/src/verify/sygus/pooled.rs --re '{{verifier_expr_pooled_support_re}}' --output {{mutants_output_dir}}/mutants.out.verifier-expr.pooled-support -- --lib pooled_sygus {{mutants_libtest_args}}

check-lang-mutants-fn-vc:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-verify function VC mutants" -- {{mutants_env}} cargo mutants {{mutants_common_args}} -p abide-verify --file crates/abide-verify/src/verify/fn_verify.rs --output {{mutants_output_dir}}/mutants.out.fn-vc -- --lib fn_contract {{mutants_libtest_args}}

check-lang-mutants-smt-facade:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-verify SMT facade mutants" -- {{mutants_env}} cargo mutants {{mutants_common_args}} -p abide-verify --file crates/abide-verify/src/verify/smt.rs --output {{mutants_output_dir}}/mutants.out.smt-facade -- --lib smt {{mutants_libtest_args}}

check-lang-mutants-solver-routing:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-verify solver routing mutants" -- {{mutants_env}} cargo mutants {{mutants_common_args}} -p abide-verify --file crates/abide-verify/src/verify/solver.rs --re 'SolverCapabilities|backend_score|set_active_solver_family|is_solver_family_available|AbideSolver|z3_check_chc' --output {{mutants_output_dir}}/mutants.out.solver-routing -- --lib solver {{mutants_libtest_args}}

check-lang-mutants-runtime-backend:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-verify runtime backend mutants" -- {{mutants_env}} cargo mutants {{mutants_common_args}} -p abide-verify --file crates/abide-verify/src/verify/solver.rs --re 'RuntimeBackend|RuntimeModel|RuntimeDynamic|RuntimeBool|RuntimeReal|RuntimeArray|RuntimeModelEval' --output {{mutants_output_dir}}/mutants.out.runtime-backend -- --lib solver {{mutants_libtest_args}}

check-lang-mutants-verify: check-lang-mutants-fn-vc check-lang-mutants-smt-facade check-lang-mutants-solver-routing check-lang-mutants-runtime-backend check-lang-mutants-verifier-expr

coverage:
  {{runner}} --timeout-secs {{cargo_timeout}} --label "abide coverage" -- cargo llvm-cov -p abide --lib --tests

coverage-html:
  {{runner}} --timeout-secs {{cargo_timeout}} --label "abide html coverage" -- cargo llvm-cov -p abide --lib --tests --html

check: fmt-check clippy test

check-strict: check test-unbounded

clean:
  cargo clean
