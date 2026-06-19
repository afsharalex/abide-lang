.PHONY: help build run fmt fmt-check clippy test test-lib test-integration test-unbounded check-lang-mutants-syntax-core check-lang-mutants-syntax-core-shard-1 check-lang-mutants-syntax-core-shard-2 check-lang-mutants-syntax-core-shard-3 check-lang-mutants-syntax-core-shard-4 check-lang-mutants-syntax-expr check-lang-mutants-syntax-expr-shard-1 check-lang-mutants-syntax-expr-shard-2 check-lang-mutants-syntax-expr-shard-3 check-lang-mutants-syntax-expr-shard-4 check-lang-mutants-syntax-system check-lang-mutants-syntax-types check-lang-mutants-syntax-parser check-lang-mutants-sema-namespace check-lang-mutants-sema-namespace-shard-1 check-lang-mutants-sema-namespace-shard-2 check-lang-mutants-sema-namespace-shard-3 check-lang-mutants-sema-namespace-shard-4 check-lang-mutants-sema-loader check-lang-mutants-sema-loader-shard-1 check-lang-mutants-sema-loader-shard-2 check-lang-mutants-sema-loader-shard-3 check-lang-mutants-sema-loader-shard-4 check-lang-mutants-sema-resolution-imports check-lang-mutants-sema-resolution-imports-shard-1 check-lang-mutants-sema-resolution-imports-shard-2 check-lang-mutants-sema-resolution-imports-shard-3 check-lang-mutants-sema-resolution-imports-shard-4 check-lang-mutants-sema-resolution-types check-lang-mutants-sema-resolution-types-core check-lang-mutants-sema-resolution-types-monomorphize check-lang-mutants-sema-resolution-types-validate check-lang-mutants-sema-resolution-expr check-lang-mutants-sema-resolution-expr-core check-lang-mutants-sema-resolution-expr-core-shard-1 check-lang-mutants-sema-resolution-expr-core-shard-2 check-lang-mutants-sema-resolution-expr-core-shard-3 check-lang-mutants-sema-resolution-expr-core-shard-4 check-lang-mutants-sema-resolution-expr-relation check-lang-mutants-sema-resolution-expr-relation-shard-1 check-lang-mutants-sema-resolution-expr-relation-shard-2 check-lang-mutants-sema-resolution-expr-relation-shard-3 check-lang-mutants-sema-resolution-expr-relation-shard-4 check-lang-mutants-sema-resolution-assumptions check-lang-mutants-sema-resolution-assumptions-core check-lang-mutants-sema-resolution-assumptions-core-shard-1 check-lang-mutants-sema-resolution-assumptions-core-shard-2 check-lang-mutants-sema-resolution-assumptions-event-path check-lang-mutants-sema-resolution-assumptions-event-path-shard-1 check-lang-mutants-sema-resolution-assumptions-event-path-shard-2 check-lang-mutants-sema-checker check-lang-mutants-sema-checker-core check-lang-mutants-sema-checker-core-shard-1 check-lang-mutants-sema-checker-core-shard-2 check-lang-mutants-sema-checker-core-shard-3 check-lang-mutants-sema-checker-core-shard-4 check-lang-mutants-sema-checker-entity check-lang-mutants-sema-checker-system check-lang-mutants-sema-checker-system-core check-lang-mutants-sema-checker-system-core-shard-1 check-lang-mutants-sema-checker-system-core-shard-2 check-lang-mutants-sema-checker-system-core-shard-3 check-lang-mutants-sema-checker-system-core-shard-4 check-lang-mutants-sema-checker-system-interface check-lang-mutants-sema-checker-system-extern check-lang-mutants-sema-checker-system-return check-lang-mutants-sema-checker-system-proc-deps check-lang-mutants-sema-checker-matches check-lang-mutants-sema-checker-ctors check-lang-mutants-sema-diagnostics check-lang-mutants-ir-lowering check-lang-mutants-ir-lowering-core check-lang-mutants-ir-lowering-system check-lang-mutants-ir-lowering-expr check-lang-mutants-ir-lowering-expr-shard-1 check-lang-mutants-ir-lowering-expr-shard-2 check-lang-mutants-ir-lowering-expr-shard-3 check-lang-mutants-ir-lowering-expr-shard-4 check-lang-mutants-ir-lowering-qualify check-lang-mutants-cli-project check-lang-mutants-cli-project-baseline check-lang-mutants-cli-project-targets check-lang-mutants-cli-project-targets-shard-1 check-lang-mutants-cli-project-targets-shard-2 check-lang-mutants-cli-project-targets-shard-3 check-lang-mutants-cli-project-targets-shard-4 check-lang-mutants-cli-project-targets-shard-5 check-lang-mutants-cli-project-targets-shard-6 check-lang-mutants-cli-project-targets-shard-7 check-lang-mutants-cli-project-targets-shard-8 check-lang-mutants-cli-project-helpers check-lang-mutants-cli-project-helpers-shard-1 check-lang-mutants-cli-project-helpers-shard-2 check-lang-mutants-cli-project-helpers-shard-3 check-lang-mutants-cli-project-helpers-shard-4 check-lang-mutants-cli-project-helpers-shard-5 check-lang-mutants-cli-project-helpers-shard-6 check-lang-mutants-cli-project-helpers-shard-7 check-lang-mutants-cli-project-helpers-shard-8 check-lang-mutants-ide-workspace-index check-lang-mutants-ide-workspace-index-baseline check-lang-mutants-fn-vc check-lang-mutants-smt-facade check-lang-mutants-solver-routing check-lang-mutants-runtime-backend check-lang-mutants-verify coverage coverage-html check check-strict clean
.PHONY: test-fallback-soundness check-ignored-tests update-ignored-tests
.PHONY: check-lang-mutants-core-arith check-lang-mutants-core-real
.PHONY: check-lang-mutants-wnby check-lang-mutants-wnby-ir-types check-lang-mutants-wnby-sema-collect-types check-lang-mutants-wnby-syntax-lex check-lang-mutants-wnby-simulate check-lang-mutants-wnby-verify-literal check-lang-mutants-wnby-verify-support check-lang-mutants-wnby-verify-explicit check-lang-mutants-wnby-verify-float-route check-lang-mutants-wnby-verify-temporal check-lang-mutants-wnby-verify-theorem-transition check-lang-mutants-wnby-verify-relational check-lang-mutants-wnby-verify-harness check-lang-mutants-wnby-verify-ic3 check-lang-mutants-wnby-verify-sygus-core check-lang-mutants-wnby-verify-pure-scene check-lang-mutants-wnby-verify-dispatch
.PHONY: check-lang-mutants-wnby-verify-pure-scene-context check-lang-mutants-wnby-verify-pure-scene-defenv check-lang-mutants-wnby-verify-pure-scene-encode-ctors check-lang-mutants-wnby-verify-pure-scene-encode-apps check-lang-mutants-wnby-verify-pure-scene-encode-collections check-lang-mutants-wnby-verify-pure-scene-encode-lambda check-lang-mutants-wnby-verify-pure-scene-scene check-lang-mutants-wnby-verify-pure-scene-scope-walkers

.NOTPARALLEL: check-lang-mutants-syntax-core check-lang-mutants-syntax-expr check-lang-mutants-syntax-parser check-lang-mutants-sema-namespace check-lang-mutants-sema-loader check-lang-mutants-sema-resolution-imports check-lang-mutants-sema-resolution-types check-lang-mutants-sema-resolution-expr check-lang-mutants-sema-resolution-assumptions check-lang-mutants-sema-checker check-lang-mutants-ir-lowering check-lang-mutants-cli-project check-lang-mutants-cli-project-targets check-lang-mutants-cli-project-helpers check-lang-mutants-qa check-lang-mutants-qa-parse check-lang-mutants-qa-exec check-lang-mutants-qa-runner check-lang-mutants-qa-extract check-lang-mutants-lsp check-lang-mutants-lsp-semantic check-lang-mutants-lsp-project check-lang-mutants-ide-workspace-index check-lang-mutants-verify check-lang-mutants-wnby check-lang-mutants-wnby-simulate check-lang-mutants-wnby-verify-temporal check-lang-mutants-wnby-verify-theorem-transition check-lang-mutants-wnby-verify-relational check-lang-mutants-wnby-verify-harness check-lang-mutants-wnby-verify-ic3 check-lang-mutants-wnby-verify-sygus-core check-lang-mutants-wnby-verify-pure-scene check-lang-mutants-wnby-verify-dispatch
.NOTPARALLEL: check-lang-mutants-wnby-verify-pure-scene-context check-lang-mutants-wnby-verify-pure-scene-defenv check-lang-mutants-wnby-verify-pure-scene-encode-ctors check-lang-mutants-wnby-verify-pure-scene-encode-apps check-lang-mutants-wnby-verify-pure-scene-encode-collections check-lang-mutants-wnby-verify-pure-scene-encode-lambda check-lang-mutants-wnby-verify-pure-scene-scene check-lang-mutants-wnby-verify-pure-scene-scope-walkers

CARGO := cargo
CARGO_MUTANTS := cargo mutants
LLVM_COV := cargo llvm-cov
RUN_WITH_TIMEOUT := python3 tools/run_with_timeout.py
CARGO_TIMEOUT_SECS ?= 3600
UNBOUNDED_VERIFY_TESTS := theorem_proved_by_induction theorem_unprovable_when_not_inductive theorem_step_case_does_not_vacuously_prove_under_no_stutter theorem_invariant_preservation_does_not_vacuously_prove_under_no_stutter tiered_unbounded_only_returns_unknown_on_failure ic3_proves_property_induction_cannot no_ic3_flag_skips_ic3_verify_falls_to_bmc unbounded_only_no_ic3_gives_accurate_hint multi_apply_ic3_proves_property verify_all_with_independent_z3_chc_selection_preserves_ic3_proofs verify_all_with_cvc5_chc_selection_is_honest_about_current_chc_limit
FALLBACK_SOUNDNESS_VERIFY_TESTS := verifier_lowering_code_documents_silent_fallback_patterns pure_encoder_rejects_shared_unsupported_ir_corpus slot_encoder_rejects_shared_unsupported_ir_corpus property_encoder_rejects_shared_unsupported_ir_corpus check_scene_block_rejects_shared_unsupported_ir_corpus scene_precheck_rejects_shared_unsupported_ir_corpus action_precheck_rejects_shared_unsupported_ir_corpus ic3_encoders_reject_shared_unsupported_ir_corpus theorem_and_lemma_reject_shared_unsupported_ir_corpus explicit_state_eval_rejects_shared_unsupported_ir_corpus property_encoder_rejects_future_temporal_fallbacks reachable_division_by_zero_is_flagged verify_all_rejects_bare_expr_stmt_action_body liveness_body_division_is_not_silently_checked transition_update_division_by_zero_is_flagged theorem_reachable_division_by_zero_is_not_proved fn_contract_division_by_zero_is_not_proved
FALLBACK_SOUNDNESS_SLOW_FIXTURE_TESTS := fixture_collection_ops_full_smoke fixture_collections_full_smoke fixture_quantifiers_full_smoke fixture_until_full_smoke fixture_lambdas_full_smoke fixture_refinements_full_smoke
FALLBACK_SOUNDNESS_EXAMPLE_TESTS := public_examples_cover_remaining_audit_constructs public_example_verify_blocks_run_with_bounded_targets public_intentional_failure_examples_report_expected_outcomes
MUTANTS_TIMEOUT_SECS ?= 900
MUTANTS_PROFILE ?= mutants
MUTANTS_JOBS ?= 1
MUTANTS_CARGO_BUILD_JOBS ?= 1
MUTANTS_CMAKE_BUILD_PARALLEL_LEVEL ?= 1
MUTANTS_TEST_THREADS ?= 1
MUTANTS_PER_TEST_TIMEOUT_SECS ?= 60
MUTANTS_BUILD_TIMEOUT_SECS ?= 180
MUTANTS_OUTPUT_DIR ?= .mutants-out
MUTANTS_SHARD_TOTAL := 4
MUTANTS_VERIFY_TIMEOUT_SECS ?= 1800
MUTANTS_VERIFY_PER_TEST_TIMEOUT_SECS ?= 75
MUTANTS_VERIFY_BUILD_TIMEOUT_SECS ?= 900
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
MUTANTS_IDE_SHARD_TOTAL := 8
MUTANTS_IDE_TIMEOUT_SECS ?= 1200
MUTANTS_IDE_FOCUSED_TIMEOUT_SECS ?= 300
MUTANTS_IDE_PER_TEST_TIMEOUT_SECS ?= 75
MUTANTS_IDE_BUILD_TIMEOUT_SECS ?= 600
MUTANTS_VERIFY_EXPR_SHARD_TOTAL := 4
MUTANTS_VERIFY_EXPR_TIMEOUT_SECS ?= 1800
MUTANTS_VERIFY_EXPR_PER_TEST_TIMEOUT_SECS ?= 75
MUTANTS_VERIFY_EXPR_BUILD_TIMEOUT_SECS ?= 900
MUTANTS_ENV := env RUSTC_WRAPPER=sccache CARGO_BUILD_JOBS=$(MUTANTS_CARGO_BUILD_JOBS) CMAKE_BUILD_PARALLEL_LEVEL=$(MUTANTS_CMAKE_BUILD_PARALLEL_LEVEL)
MUTANTS_COMMON_ARGS := --profile $(MUTANTS_PROFILE) --jobs $(MUTANTS_JOBS) --timeout $(MUTANTS_PER_TEST_TIMEOUT_SECS) --build-timeout $(MUTANTS_BUILD_TIMEOUT_SECS)
MUTANTS_VERIFY_COMMON_ARGS := --profile $(MUTANTS_PROFILE) --timeout $(MUTANTS_VERIFY_PER_TEST_TIMEOUT_SECS) --build-timeout $(MUTANTS_VERIFY_BUILD_TIMEOUT_SECS) --in-place --baseline skip
MUTANTS_VERIFY_EXPR_COMMON_ARGS := --profile $(MUTANTS_PROFILE) --timeout $(MUTANTS_VERIFY_EXPR_PER_TEST_TIMEOUT_SECS) --build-timeout $(MUTANTS_VERIFY_EXPR_BUILD_TIMEOUT_SECS) --in-place --baseline skip
MUTANTS_CLI_COMMON_ARGS := --profile $(MUTANTS_PROFILE) --timeout $(MUTANTS_CLI_PER_TEST_TIMEOUT_SECS) --build-timeout $(MUTANTS_CLI_BUILD_TIMEOUT_SECS) --in-place --baseline skip
MUTANTS_QA_COMMON_ARGS := --profile $(MUTANTS_PROFILE) --timeout $(MUTANTS_QA_PER_TEST_TIMEOUT_SECS) --build-timeout $(MUTANTS_QA_BUILD_TIMEOUT_SECS) --in-place --baseline skip
MUTANTS_LSP_COMMON_ARGS := --profile $(MUTANTS_PROFILE) --timeout $(MUTANTS_LSP_PER_TEST_TIMEOUT_SECS) --build-timeout $(MUTANTS_LSP_BUILD_TIMEOUT_SECS) --in-place --baseline skip
MUTANTS_IDE_COMMON_ARGS := --profile $(MUTANTS_PROFILE) --timeout $(MUTANTS_IDE_PER_TEST_TIMEOUT_SECS) --build-timeout $(MUTANTS_IDE_BUILD_TIMEOUT_SECS) --in-place --baseline skip
MUTANTS_LIBTEST_ARGS := -- --test-threads $(MUTANTS_TEST_THREADS)
CLI_PROJECT_HELPERS_RE := resolve_file_by_file_source_targets|resolve_whole_spec_source_targets|resolve_qa_script_targets|collect_qa_scripts_in_directory|build_verify_config|verify_names|validate_verify_solver_options|effective_overall_timeout|qa_summary_message|parse_simulation_scope_overrides
QA_RUNNER_RE := run_qa_script|run_qa_source|run_qa_script_with_hooks|run_qa_source_with_hooks|temporal_artifact_name|render_simulation_summary|explore_state_space|validate_state_space_scopes|select_exploration_systems|build_state_space_verify|slots_for_entity|state_space_artifact_name|sanitize_artifact_name|render_state_space_summary|handle_artifact_statement|load_and_build_model|rebuild_model|rebuild_ir_program|resolve_load_path|collect_abide_files
QA_EXTRACT_RE := extract|extract_interfaces|record_entity_field_meta|record_system_field_meta|extract_entity_graphs|extract_system_graphs|collect_system_field_transitions|extract_system_field_update|extract_guard_state|finite_field_states|finite_field_states_inner|finite_variant_states|enumerate_variant_states|render_variant_state|is_graphable_field_type|extract_finite_state_name|extract_system_info|collect_event_actions|display_ir_expr|display_ir_pattern|display_ir_type
QA_SUPPORT_RE := format_result|format_path|format_transitions|format_table|format_result_json|is_reachable|find_path|terminal_states|initial_states|has_cycles|find_cycle|transitions_from|transitions_to|build_adjacency|dfs_cycle|dfs_find_cycle|qa_command_candidates|qa_query_subcommand_candidates|validate_qa_source|validate_embedded_abide_blocks|base_env_for_qa_source|validate_embedded_abide_block|build_flow_model_from_paths|validate_query_reference|query_reference_validation|temporal_target_reference_validation|model_has_owner|reference_span|artifact_parts_from_result_with_name|payload_kind_label|render_state_space_graph|render_state_space_state|render_state_space_diff|render_witness_summary|render_countermodel_summary|render_proof_artifact_summary|render_witness_timeline|render_behavior_timeline|render_witness_state|render_behavior_state|render_witness_diff|render_behavior_diff|witness_state_lines|behavior_state_lines|render_state_diff|render_operational_state|operational_state_lines|render_relational_state|relational_state_lines|render_relation_id|render_witness_value|render_slot_ref|render_record
LSP_RE := verification_options|server_capabilities|verify_config_for_editor_policy|should_schedule_on_change|should_schedule_on_save|should_run_automatically|should_accept_document_version|document_version|uri_published_elsewhere|collect_diagnostics_for_root|collect_qa_diagnostics_for_root|is_qa_document_path|collect_lsp_diagnostic|qa_run_command_uri_arg|run_qa_script_for_uri|qa_run_source_for_uri|run_qa_source_to_json|diagnostic_to_lsp|related_information|definition_locations|source_for_path|collect_embedded_abide_diagnostics_for_root|location_for_span|uri_and_range_for_span|completion_item_for_symbol|completion_items_for_open_document|embedded_abide_block_at|abide_completion_items_for_source|qa_completion_items|qa_completion_context|current_line_prefix|keyword_completion_context|starts_with_any_keyword|is_word_boundary|keyword_completions|keyword_sort_text|position_to_offset|range_from_span|offset_to_position
LSP_SEMANTIC_RE := quickfix_actions_requested|code_actions_for_document|missing_load_code_action|close_qa_abide_block_code_action|removed_field_keyword_code_action|quickfix_action|single_file_edit|diagnostic_code|range_to_offsets|symbol_at_document_position|occurrence_resolves_to_symbol|reference_locations_for_symbol|rename_changes_for_symbol|resolve_occurrence_symbol|symbol_declared_at|best_symbol_match|same_symbol_identity|completion_symbols_for_context|embedded_qa_abide_completion_items|qualifier_before_dot|qualifier_before_scope|qualifier_before_trigger|qa_completion_items_for_document|qa_model_reference_completion_kind|qa_model_reference_completion_items|qa_load_path_completion_items|qa_load_path_prefix|loaded_qa_flow_model|loaded_qa_workspace_index|qa_load_paths|qa_load_path_from_line
LSP_PROJECT_RE := for_path|is_project_source|discover|empty|root|files|register_file|discover_dir|normalize_under_root|normalize_path_lexical|should_skip_project_dir|from_project|file_id|file_kind|file_kind_for_id|path|source_text|upsert_open_document|set_file_source|parse|lower|diagnostics|workspace_index|identifier_at|file_revision|file_state_mut|invalidate_file|invalidate_qa_diagnostics|qa_diagnostics|canonicalize|read_to_string|should_accept_document_version|document_version|uri_published_elsewhere|initialize|did_open|did_change|did_save|did_close|upsert_document|refresh_diagnostics|collect_diagnostics_for_root|collect_qa_diagnostics_for_root|collect_lsp_diagnostic|snapshot_source_for_path
IDE_WORKSPACE_INDEX_RE := symbols_named|completion_symbols|symbols_in_module|module_exports|members_by_owner|enum_variants_by_type|visible_symbols|references_named|completion_context|classify_abide_cursor|classify_qa_cursor|current_line_prefix|clamp_to_char_boundary|starts_with_keyword|is_word_boundary|pending_contract_context|block_frames|block_depth|block_frame_from_header|declaration_block_kind|last_callable_decl_keyword|words|build_workspace_index|is_abide_source_path|identifier_at|dedup_symbols|dedup_occurrences|dedup_symbol_clones|name_occurrences_from_tokens|collect_program_symbols|module_name|collect_program_imports_and_includes|collect_use_decl|collect_program|collect_top_decl|collect_type_decl|collect_entity_decl|collect_interface_decl|collect_system_decl|collect_proc_decl|collect_proc_nodes|collect_program_decl|collect_proc_decl_with_owner|find_name_span|symbol_detail
SEMA_RESOLUTION_EXPR_EXPECTED_RE := resolve_if_else_with_expected_type|resolve_var_decl_expr|resolve_set_literal_expr|resolve_seq_literal_expr|resolve_map_literal_expr|resolve_collection_literal_with_expected_type|resolve_expr_with_expected_type
SEMA_RESOLUTION_EXPR_CONSTRUCTOR_RE := expected_constructor_call|expected_enum_constructor_name|expected_constructor_payload_types|expected_generic_constructor_payload_types|resolve_comparison_ctor_from_context|enum_scope_matches|enum_name_without_args|resolve_var_type|resolve_ctor_type_from_context|patch_constructor_callee|can_patch_constructor_ty|find_constructor_type
SEMA_COLLECTION_EXPR_RE := collect_qualified_call|quant_guard_body|collect_set_comp_binder|collect_call_expr|collect_quantifier_expr|collect_aggregate_expr|collect_let_expr|collect_lambda_expr|collect_match_expr|collect_set_comp_expr|collect_rel_comp_expr|collect_saw_expr|collect_control_expr|collect_expr
SEMA_VALIDATION_CONTEXT_RE := walk_expr|walk_contract|walk_field_default|walk_event_action|walk_scene_when|walk_env_exprs|validate_saw_expressions|validate_aggregate_bodies|validate_set_comprehension_sources|validate_set_comprehension_expr|validate_set_comprehension_event_action|validate_set_comprehension_field_default
VERIFIER_EXPR_PROPERTY_QUANTIFIER_RE := property_quantifier_parts|encode_prop_quantifier_expr|encode_entity_quantifier_expr|encode_finite_enum_quantifier_expr|combine_finite_quantifier_predicates|encode_native_quantifier_expr|narrow_entity_quantifier_slots|extract_store_scoped_quantifier_body
VERIFIER_EXPR_PROPERTY_CONSTRUCTOR_RE := encode_prop_constructor_field_or_call_value|encode_prop_payload_field_value|encode_static_payload_field_value|payload_accessor_for_field|ctor_name_matches_for_payload_accessor|encode_prop_field_value|encode_prop_ctor_value|encode_prop_adt_ctor_value
VERIFIER_EXPR_SLOT_RE := try_encode_slot_expr|try_encode_slot_literal_expr|try_encode_slot_var_or_field_expr|try_encode_slot_field_expr|try_encode_slot_constructor_expr|try_encode_slot_constructor|try_encode_slot_choose_expr|try_encode_slot_operator_expr|try_encode_slot_binop_expr|try_encode_slot_unop_expr|try_encode_slot_app_expr|try_encode_slot_app|try_encode_slot_collection_expr|try_encode_slot_map_update_expr|try_encode_slot_index_expr|try_encode_slot_map_lit_expr|try_encode_slot_set_lit_expr|try_encode_slot_seq_lit_expr|try_encode_slot_finite_set_comp_expr|try_encode_slot_card_expr|try_encode_slot_sourced_set_comp_card|try_encode_slot_finite_set_comp_card|try_encode_slot_control_expr|try_encode_slot_store_quantifier
VERIFIER_EXPR_SLOT_SHARD_1_RE := try_encode_slot_expr|try_encode_slot_literal_expr|try_encode_slot_var_or_field_expr|try_encode_slot_field_expr
VERIFIER_EXPR_SLOT_SHARD_2_RE := try_encode_slot_constructor_expr|try_encode_slot_constructor|try_encode_slot_choose_expr|try_encode_slot_operator_expr|try_encode_slot_binop_expr|try_encode_slot_unop_expr
VERIFIER_EXPR_SLOT_SHARD_3_RE := try_encode_slot_app_expr|try_encode_slot_app|try_encode_slot_collection_expr|try_encode_slot_map_update_expr|try_encode_slot_index_expr|try_encode_slot_map_lit_expr|try_encode_slot_set_lit_expr|try_encode_slot_seq_lit_expr
VERIFIER_EXPR_SLOT_SHARD_4_RE := try_encode_slot_finite_set_comp_expr|try_encode_slot_card_expr|try_encode_slot_sourced_set_comp_card|try_encode_slot_finite_set_comp_card|try_encode_slot_control_expr|try_encode_slot_store_quantifier
VERIFIER_EXPR_COLLECTION_RE := encode_set_literal|encode_seq_literal|encode_map_literal|encode_collection_index|encode_collection_update|finite_literal_cardinality|encode_unique_projected_cardinality|int_sum_or_zero|unique_expr_count
VERIFIER_EXPR_POOLED_SUPPORT_RE := diagnose_pooled_sygus_expr_support|diagnose_pooled_sygus_expr_support_inner|unsupported_expr|is_pooled_sygus_finite_scalar_domain|ensure_pooled_sygus_expr_supported|ensure_pooled_sygus_action_supported|ensure_pooled_sygus_actions_supported|ensure_pooled_sygus_system_supported
WNBY_SYNTAX_LEX_RE := classify_lex_error
WNBY_SIMULATE_RE := real_operand|float_operand|float_witness|try_float_binop|real_witness|try_real_binop|eval_binop|witness_values_equal|eval_unop|sim_int_op|real_witness_value|float_witness_value|normalize_float
WNBY_VERIFY_LITERAL_RE := string_literal_id
WNBY_VERIFY_SUPPORT_RE := classify_expr_support|classify_action_support|classify_quantifier|is_finite_domain|statement_like_expr_cases|property_position_unsupported_cases|unsupported_expr_cases
WNBY_VERIFY_EXPLICIT_RE := supports_state_expr|pattern_matches|fieldless_enum_variant_value|fieldless_enum_variant_value_for_type|eval_expr|eval_expr_with_store_ranges|eval_cardinality_expr|eval_quantifier|explicit_store_scoped_quantifier_body|eval_choose|eval_bool_with_store_ranges|eval_binop|eval_eq|eval_neq|eval_int_comparison|compare_reals|explicit_int_op|eval_unop|finite_values_for_type|witness_value
WNBY_VERIFY_FLOAT_ROUTE_RE := program_uses_float|ty_uses_float|expr_uses_float|action_uses_float|scrutinee_uses_float|function_uses_float|entity_uses_float|field_uses_float|system_uses_float|verify_uses_float|theorem_uses_float|scene_uses_float
WNBY_VERIFY_TEMPORAL_RE := compile_buchi_formula|lower_to_buchi_formula|lower_to_temporal_formula|buchi_atom_for|render_spot_formula|extract_liveness_pattern_inner|strip_liveness_from_conjunction|extract_liveness_pattern_with_always|action_contains_integer_div|render_hoa_acceptance_condition|local_consistency_holds|transition_consistency_holds|initial_past_consistency_holds|formula_present|formula_id_present
WNBY_VERIFY_THEOREM_TRANSITION_RE := encode_pure_property_expr|needs_property_encoder|theorem_reachable_div_by_zero|theorem_scope|theorem_store_decls|theorem_with_scope_invariants|validate_theorem_temporal_forms|handle_theorem_liveness|validate_theorem_supported_forms|validate_theorem_transition_forms|run_theorem_induction|prove_invariant_base|prove_invariant_step|assert_domain_and_lemmas|assert_transition_step|try_ic3_on_theorem|simplify_static_bool_fragments|try_extern_assume_expr_constraints|solve_transition_obligation
WNBY_VERIFY_RELATIONAL_RE := build_initial_store_instances|build_stateful_scene_sat|relational_stateful_scene_spec|create_spec|add_cardinality_constraint|relational_verify_spec|build_default_field_map|finite_field_domains|finite_type_values|encode_verify_violation_into|encode_verify_snapshot_into|relation_state_index|build_relational_verify_counterexample_witness|const_lit|and_lit|or_lit|at_most_one_lit|exactly_one_lit|classify_static_relation_solver_result|check_static_relation_assertions|encode_static_relation_assertion|lower_static_relation_expr|relation_type_from_ir_type|solve_static_relation|contains_relation_surface
WNBY_VERIFY_HARNESS_RE := expr_type|create_slot_pool|domain_constraints|initial_state_constraints_with_store_ranges|initial_active_slots_with_store_ranges|try_entity_field_initial_constraints|try_encode_field_default_expr|store_active_cardinality_constraints|try_encode_action|try_encode_action_with_vars|eval_expr_with_vars|build_apply_params|try_build_apply_params|wire_apply_refs|try_encode_guard_inner|try_encode_guard_value|try_encode_step|try_encode_step_with_params|transition_constraints|try_transition_constraints|transition_constraints_with_fire|try_transition_constraints_with_fire|try_encode_step_enabled|try_encode_step_enabled_with_params|try_encode_enabled_cross_call_branches|apply_enabled_match|enabled_match_scrutinee_branches|enabled_match_arm_condition|encode_legacy_choose|register_legacy_choose_params|encode_legacy_forall|collect_modified_entities|legacy_chain_apply_params|encode_legacy_chain_apply|legacy_inactive_slot_frame|merged_branch_params
WNBY_VERIFY_IC3_RE := try_ic3_liveness|encode_liveness_event_chc|action_mutates_state|encode_step_chc_scoped|encode_ops_chc_scoped|top_level_action_guards|encode_macro_call_chc|encode_action_match_scrutinee|encode_macro_return_expr|encode_action_guard_with_locals|encode_non_entity_guard_with_locals|encode_create_chc|ic3_lookup_ctor_variant
WNBY_VERIFY_SYGUS_RE := cvc5_sygus_enabled|cvc5_sygus_disabled_reason|type_uses_real|try_cvc5_sygus_single_entity|try_cvc5_sygus_system_safety|require_obligation_unsat|collect_system_action_updates|collect_system_exprstmt_update|collect_system_action_sequence_updates|merge_system_match_update_maps|collect_system_match_updates|encode_finite_aggregate_expr|encode_finite_map_key_membership_expr|encode_finite_source_membership|encode_finite_set_membership_term|default_term_for_type|encode_finite_map_lookup_expr_inner|ctor_name_matches|bind_static_payload_pattern_vars|encode_static_payload_pattern_cond
WNBY_VERIFY_PURE_SCENE_CONTEXT_RE := register_enum_type|collect_program_enum_types|collect_enum_types_from_expr|default_expr_to_string|default_match_arm_to_string|default_pattern_to_string
WNBY_VERIFY_PURE_SCENE_DEFENV_RE := rewrite_self_field_refs|decompose_app_chain_public|classify_app_chain_public|substitute_var|free_vars_inner|subst_match|subst_rel_comp|subst_quantifier
WNBY_VERIFY_PURE_SCENE_ENCODE_CTORS_RE := encode_pure_ctor|encode_adt_ctor|validate_ctor_fields
WNBY_VERIFY_PURE_SCENE_ENCODE_APPS_RE := encode_pure_app|verify_call_preconditions|check_fn_div_well_defined|encode_recursive_app|encode_func_application
WNBY_VERIFY_PURE_SCENE_ENCODE_COLLECTIONS_RE := encode_pure_card|encode_pure_set_comp|encode_set_comp_source_pred|combine_set_comp_restrictions|encode_projected_set_comp
WNBY_VERIFY_PURE_SCENE_ENCODE_LAMBDA_RE := encode_lambda|encode_partial_application|unique_theorem_store_name|field_refinement_obligation|expr_quantifies_over_entity
WNBY_VERIFY_PURE_SCENE_SCENE_RE := scene_solver_result|direct_choose_equality_witness|encode_scene_direct_choose_arg|scene_pass_evidence|assert_scene_then_assertions|is_supported_finite_setcomp_source|is_finite_scene_cardinality_target|extract_command_params|extract_transition_from_fire|analyze_event_fairness|diagnose_disabled_event
WNBY_VERIFY_PURE_SCENE_SCOPE_WALKERS_RE := expr_quantifies_over_entity|is_supported_finite_setcomp_source|is_finite_scene_cardinality_target
WNBY_VERIFY_DISPATCH_RE := verify_all|verify_all_with_events|verify_all_on_worker|verify_all_inner|verify_all_single|verify_all_single_impl|reconcile_solver_results|float_requires_z3_result|catch_verification_panic|record_verify_assert_precondition_obligations|check_verify_block_tiered|try_cvc5_sygus_on_verify|try_induction_on_verify|prove_induction_base|prove_induction_step|liveness_reduction_applicable|prove_liveness_by_monitor_induction|revalidate_sygus_invariant_via_z3|revalidate_pooled_sygus_invariant_via_z3|prove_liveness_by_ic3|try_ic3_on_verify|try_ic3_on_verify_with_diagnostics|check_verify_block_with_depth_search|check_div_by_zero_reachable|validate_bmc_inputs|bmc_transition_encoding|check_verify_block_lasso|check_lasso_asserts|encode_buchi_lasso_violation|expand_expr_node|expand_basic_expr_node
WNBY_VERIFY_DISPATCH_RECONCILE_RE := reconcile_solver_results|result_signature|result_name|solver_label
WNBY_VERIFY_DISPATCH_FLOAT_BACKEND_RE := float_requires_z3_result|unavailable_solver_result
WNBY_IR_TYPES_RE := simple|base_without_refinement|as_str|is_assignment|try_from|fmt
WNBY_SEMA_COLLECT_TYPES_RE := collect_entity|collect_field|collect_action|collect_assignment|elaborate_store_param|check_system_action_fsm_violations|collect_system_prime_assignments|collect_system_prime_assignments_inner|collect_match_scrutinee|collect_match_arm|base_without_refinement|domain|fmt
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
LSP_SEMANTIC_SHARD_TARGETS := $(addprefix check-lang-mutants-lsp-semantic-shard-,$(LSP_SHARDS))
LSP_PROJECT_SHARD_TARGETS := $(addprefix check-lang-mutants-lsp-project-shard-,$(LSP_SHARDS))
IDE_SHARDS := 1 2 3 4 5 6 7 8
VERIFIER_EXPR_SLOT_SHARDS := 1 2 3 4
SEMA_EXPR_HELPER_SHARDS := 1 2 3 4
IDE_WORKSPACE_INDEX_SHARD_TARGETS := $(addprefix check-lang-mutants-ide-workspace-index-shard-,$(IDE_SHARDS))
VERIFIER_EXPR_SLOT_SHARD_TARGETS := $(addprefix check-lang-mutants-verifier-expr-slot-shard-,$(VERIFIER_EXPR_SLOT_SHARDS))
SEMA_RESOLUTION_EXPR_EXPECTED_SHARD_TARGETS := $(addprefix check-lang-mutants-sema-resolution-expr-expected-shard-,$(SEMA_EXPR_HELPER_SHARDS))
SEMA_RESOLUTION_EXPR_CONSTRUCTOR_SHARD_TARGETS := $(addprefix check-lang-mutants-sema-resolution-expr-constructor-shard-,$(SEMA_EXPR_HELPER_SHARDS))
SEMA_COLLECTION_EXPR_SHARD_TARGETS := $(addprefix check-lang-mutants-sema-collection-expr-shard-,$(SEMA_EXPR_HELPER_SHARDS))
SEMA_VALIDATION_CONTEXT_SHARD_TARGETS := $(addprefix check-lang-mutants-sema-validation-context-shard-,$(SEMA_EXPR_HELPER_SHARDS))

.PHONY: check-lang-mutants-lsp check-lang-mutants-lsp-baseline check-lang-mutants-lsp-semantic check-lang-mutants-lsp-project $(CLI_PROJECT_TARGET_SHARD_TARGETS) $(CLI_PROJECT_HELPER_SHARD_TARGETS) $(QA_PARSE_SHARD_TARGETS) $(QA_EXEC_SHARD_TARGETS) $(QA_RUNNER_SHARD_TARGETS) $(QA_EXTRACT_SHARD_TARGETS) $(LSP_SHARD_TARGETS) $(LSP_SEMANTIC_SHARD_TARGETS) $(LSP_PROJECT_SHARD_TARGETS) $(IDE_WORKSPACE_INDEX_SHARD_TARGETS) check-lang-mutants-ide-workspace-index-focused check-lang-mutants-ide-workspace-index-boundary check-lang-mutants-ide-workspace-index-block-frames check-lang-mutants-ide-workspace-index-find-name-span
.PHONY: check-lang-mutants-verifier-expr check-lang-mutants-verifier-expr-property-quantifier check-lang-mutants-verifier-expr-property-constructor check-lang-mutants-verifier-expr-slot $(VERIFIER_EXPR_SLOT_SHARD_TARGETS) check-lang-mutants-verifier-expr-collections check-lang-mutants-verifier-expr-pooled-support
.PHONY: check-lang-mutants-sema-expr-helpers check-lang-mutants-sema-resolution-expr-expected $(SEMA_RESOLUTION_EXPR_EXPECTED_SHARD_TARGETS) check-lang-mutants-sema-resolution-expr-constructor $(SEMA_RESOLUTION_EXPR_CONSTRUCTOR_SHARD_TARGETS) check-lang-mutants-sema-collection-expr $(SEMA_COLLECTION_EXPR_SHARD_TARGETS) check-lang-mutants-sema-validation-context $(SEMA_VALIDATION_CONTEXT_SHARD_TARGETS)
.PHONY: check-lang-mutants-core check-lang-mutants-core-baseline check-lang-mutants-core-diagnostics check-lang-mutants-core-support
.PHONY: check-lang-mutants-witness check-lang-mutants-witness-baseline check-lang-mutants-witness-operational check-lang-mutants-witness-relational-values check-lang-mutants-witness-envelopes

.NOTPARALLEL: check-lang-mutants-sema-expr-helpers check-lang-mutants-sema-resolution-expr-expected check-lang-mutants-sema-resolution-expr-constructor check-lang-mutants-sema-collection-expr check-lang-mutants-sema-validation-context
.NOTPARALLEL: check-lang-mutants-core
.NOTPARALLEL: check-lang-mutants-witness
.NOTPARALLEL: check-lang-mutants-verifier-expr check-lang-mutants-verifier-expr-slot

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
	@printf "  make test-fallback-soundness Run opt-in fallback-soundness gate\n"
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
	@printf "  make check-lang-mutants-ide-workspace-index  Run IDE workspace index mutation lane\n"
	@printf "  make check-lang-mutants-qa               Run QA parser/execution/reporting mutation lane\n"
	@printf "  make check-lang-mutants-lsp              Run LSP diagnostics/completion mutation lane\n"
	@printf "  make check-lang-mutants-lsp-semantic     Run LSP semantic editor feature mutation lane\n"
	@printf "  make check-lang-mutants-lsp-project      Run LSP project discovery/snapshot mutation lane\n"
	@printf "  make check-lang-mutants-core             Run core span/diagnostic/message mutation lane\n"
	@printf "  make check-lang-mutants-witness          Run witness payload/envelope mutation lane\n"
	@printf "  make check-lang-mutants-fn-vc            Run function VC mutation lane\n"
	@printf "  make check-lang-mutants-smt-facade       Run SMT facade mutation lane\n"
	@printf "  make check-lang-mutants-solver-routing   Run solver routing mutation lane\n"
	@printf "  make check-lang-mutants-runtime-backend  Run runtime backend mutation lane\n"
	@printf "  make check-lang-mutants-verifier-expr    Run verifier expression helper mutation lanes\n"
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
	$(RUN_WITH_TIMEOUT) --timeout-secs $(CARGO_TIMEOUT_SECS) --label "abide-verify unbounded proof tests" -- env RUSTC_WRAPPER=sccache ABIDE_RUN_UNBOUNDED_PROOF_TESTS=1 $(CARGO) nextest run -p abide-verify --lib $(UNBOUNDED_VERIFY_TESTS) --run-ignored only
	$(RUN_WITH_TIMEOUT) --timeout-secs $(CARGO_TIMEOUT_SECS) --label "abide integration unbounded proof tests" -- env RUSTC_WRAPPER=sccache ABIDE_RUN_UNBOUNDED_PROOF_TESTS=1 ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 $(CARGO) nextest run -p abide --test integration cvc5_sygus --run-ignored only

test-fallback-soundness:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(CARGO_TIMEOUT_SECS) --label "abide-verify fallback-soundness corpus" -- env RUSTC_WRAPPER=sccache $(CARGO) nextest run -p abide-verify $(FALLBACK_SOUNDNESS_VERIFY_TESTS)
	$(RUN_WITH_TIMEOUT) --timeout-secs $(CARGO_TIMEOUT_SECS) --label "abide-verify fallback-soundness full gate" -- env RUSTC_WRAPPER=sccache $(CARGO) nextest run -p abide-verify --lib fallback_soundness_full_gate --run-ignored only
	$(RUN_WITH_TIMEOUT) --timeout-secs $(CARGO_TIMEOUT_SECS) --label "abide-verify fallback-soundness slow fixture shards" -- env RUSTC_WRAPPER=sccache $(CARGO) nextest run -p abide-verify --lib $(FALLBACK_SOUNDNESS_SLOW_FIXTURE_TESTS) --run-ignored only
	$(RUN_WITH_TIMEOUT) --timeout-secs $(CARGO_TIMEOUT_SECS) --label "abide public example fallback-soundness corpus" -- env RUSTC_WRAPPER=sccache $(CARGO) nextest run -p abide --test integration $(FALLBACK_SOUNDNESS_EXAMPLE_TESTS)

check-ignored-tests:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(CARGO_TIMEOUT_SECS) --label "ignored test inventory check" -- env RUSTC_WRAPPER=sccache python3 tools/ignored_tests_inventory.py check

update-ignored-tests:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(CARGO_TIMEOUT_SECS) --label "ignored test inventory update" -- env RUSTC_WRAPPER=sccache python3 tools/ignored_tests_inventory.py update

check-lang-mutants-core: check-lang-mutants-core-baseline check-lang-mutants-core-arith check-lang-mutants-core-real check-lang-mutants-core-diagnostics check-lang-mutants-core-support

check-lang-mutants-core-baseline:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-core baseline tests" -- $(MUTANTS_ENV) $(CARGO) test -p abide-core --lib $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-core-arith:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-core integer/real literal arithmetic mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-core --file crates/abide-core/src/arith.rs --output $(MUTANTS_OUTPUT_DIR)/mutants.out.core-arith -- --lib arith $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-core-real:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-core exact rational real mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-core --file crates/abide-core/src/real.rs --output $(MUTANTS_OUTPUT_DIR)/mutants.out.core-real -- --lib real $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-core-diagnostics:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-core diagnostic mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-core --file crates/abide-core/src/diagnostic.rs --output $(MUTANTS_OUTPUT_DIR)/mutants.out.core-diagnostics -- --lib diagnostic $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-core-support:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-core span/message mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-core --file crates/abide-core/src/span.rs --file crates/abide-core/src/messages.rs --output $(MUTANTS_OUTPUT_DIR)/mutants.out.core-support -- --lib $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-witness: check-lang-mutants-witness-baseline check-lang-mutants-witness-operational check-lang-mutants-witness-relational-values check-lang-mutants-witness-envelopes

check-lang-mutants-witness-baseline:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-witness baseline tests" -- $(MUTANTS_ENV) $(CARGO) test -p abide-witness --lib $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-witness-operational:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-witness operational mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-witness --file crates/abide-witness/src/op.rs --output $(MUTANTS_OUTPUT_DIR)/mutants.out.witness-operational -- --lib op $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-witness-relational-values:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-witness relational/value mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-witness --file crates/abide-witness/src/rel.rs --file crates/abide-witness/src/value.rs --output $(MUTANTS_OUTPUT_DIR)/mutants.out.witness-relational-values -- --lib $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-witness-envelopes:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-witness envelope/evidence mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-witness --file crates/abide-witness/src/shared.rs --file crates/abide-witness/src/evidence.rs --output $(MUTANTS_OUTPUT_DIR)/mutants.out.witness-envelopes -- --lib $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-syntax-core: check-lang-mutants-syntax-core-shard-1 check-lang-mutants-syntax-core-shard-2 check-lang-mutants-syntax-core-shard-3 check-lang-mutants-syntax-core-shard-4

check-lang-mutants-syntax-core-shard-1:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-syntax parser core mutants shard 1/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 0/$(MUTANTS_SHARD_TOTAL) -p abide-syntax --file crates/abide-syntax/src/parse/mod.rs --output $(MUTANTS_OUTPUT_DIR)/mutants.out.syntax-core.1-of-$(MUTANTS_SHARD_TOTAL) -- --lib parse $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-syntax-core-shard-2:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-syntax parser core mutants shard 2/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 1/$(MUTANTS_SHARD_TOTAL) -p abide-syntax --file crates/abide-syntax/src/parse/mod.rs --output $(MUTANTS_OUTPUT_DIR)/mutants.out.syntax-core.2-of-$(MUTANTS_SHARD_TOTAL) -- --lib parse $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-syntax-core-shard-3:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-syntax parser core mutants shard 3/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 2/$(MUTANTS_SHARD_TOTAL) -p abide-syntax --file crates/abide-syntax/src/parse/mod.rs --output $(MUTANTS_OUTPUT_DIR)/mutants.out.syntax-core.3-of-$(MUTANTS_SHARD_TOTAL) -- --lib parse $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-syntax-core-shard-4:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-syntax parser core mutants shard 4/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 3/$(MUTANTS_SHARD_TOTAL) -p abide-syntax --file crates/abide-syntax/src/parse/mod.rs --output $(MUTANTS_OUTPUT_DIR)/mutants.out.syntax-core.4-of-$(MUTANTS_SHARD_TOTAL) -- --lib parse $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-syntax-expr: check-lang-mutants-syntax-expr-shard-1 check-lang-mutants-syntax-expr-shard-2 check-lang-mutants-syntax-expr-shard-3 check-lang-mutants-syntax-expr-shard-4

check-lang-mutants-syntax-expr-shard-1:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-syntax expression parser mutants shard 1/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 0/$(MUTANTS_SHARD_TOTAL) -p abide-syntax --file crates/abide-syntax/src/parse/expr.rs --output $(MUTANTS_OUTPUT_DIR)/mutants.out.syntax-expr.1-of-$(MUTANTS_SHARD_TOTAL) -- --lib parse $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-syntax-expr-shard-2:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-syntax expression parser mutants shard 2/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 1/$(MUTANTS_SHARD_TOTAL) -p abide-syntax --file crates/abide-syntax/src/parse/expr.rs --output $(MUTANTS_OUTPUT_DIR)/mutants.out.syntax-expr.2-of-$(MUTANTS_SHARD_TOTAL) -- --lib parse $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-syntax-expr-shard-3:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-syntax expression parser mutants shard 3/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 2/$(MUTANTS_SHARD_TOTAL) -p abide-syntax --file crates/abide-syntax/src/parse/expr.rs --output $(MUTANTS_OUTPUT_DIR)/mutants.out.syntax-expr.3-of-$(MUTANTS_SHARD_TOTAL) -- --lib parse $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-syntax-expr-shard-4:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-syntax expression parser mutants shard 4/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 3/$(MUTANTS_SHARD_TOTAL) -p abide-syntax --file crates/abide-syntax/src/parse/expr.rs --output $(MUTANTS_OUTPUT_DIR)/mutants.out.syntax-expr.4-of-$(MUTANTS_SHARD_TOTAL) -- --lib parse $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-syntax-system:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-syntax system parser mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-syntax --file crates/abide-syntax/src/parse/system.rs --output $(MUTANTS_OUTPUT_DIR)/mutants.out.syntax-system -- --lib parse $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-syntax-types:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-syntax type parser mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-syntax --file crates/abide-syntax/src/parse/types.rs --output $(MUTANTS_OUTPUT_DIR)/mutants.out.syntax-types -- --lib parse $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-syntax-parser: check-lang-mutants-syntax-core check-lang-mutants-syntax-expr check-lang-mutants-syntax-system check-lang-mutants-syntax-types

check-lang-mutants-sema-namespace: check-lang-mutants-sema-namespace-shard-1 check-lang-mutants-sema-namespace-shard-2 check-lang-mutants-sema-namespace-shard-3 check-lang-mutants-sema-namespace-shard-4

check-lang-mutants-sema-namespace-shard-1:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema namespace mutants shard 1/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 0/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/env.rs --re 'build_working_namespace|key_matches_module|flatten_sorted' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-namespace.1-of-$(MUTANTS_SHARD_TOTAL) -- --lib build_working_namespace $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-namespace-shard-2:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema namespace mutants shard 2/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 1/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/env.rs --re 'build_working_namespace|key_matches_module|flatten_sorted' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-namespace.2-of-$(MUTANTS_SHARD_TOTAL) -- --lib build_working_namespace $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-namespace-shard-3:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema namespace mutants shard 3/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 2/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/env.rs --re 'build_working_namespace|key_matches_module|flatten_sorted' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-namespace.3-of-$(MUTANTS_SHARD_TOTAL) -- --lib build_working_namespace $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-namespace-shard-4:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema namespace mutants shard 4/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 3/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/env.rs --re 'build_working_namespace|key_matches_module|flatten_sorted' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-namespace.4-of-$(MUTANTS_SHARD_TOTAL) -- --lib build_working_namespace $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-loader: check-lang-mutants-sema-loader-shard-1 check-lang-mutants-sema-loader-shard-2 check-lang-mutants-sema-loader-shard-3 check-lang-mutants-sema-loader-shard-4

check-lang-mutants-sema-loader-shard-1:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema loader mutants shard 1/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 0/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/loader.rs --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-loader.1-of-$(MUTANTS_SHARD_TOTAL) -- --lib loader $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-loader-shard-2:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema loader mutants shard 2/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 1/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/loader.rs --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-loader.2-of-$(MUTANTS_SHARD_TOTAL) -- --lib loader $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-loader-shard-3:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema loader mutants shard 3/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 2/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/loader.rs --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-loader.3-of-$(MUTANTS_SHARD_TOTAL) -- --lib loader $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-loader-shard-4:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema loader mutants shard 4/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 3/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/loader.rs --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-loader.4-of-$(MUTANTS_SHARD_TOTAL) -- --lib loader $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-imports: check-lang-mutants-sema-resolution-imports-shard-1 check-lang-mutants-sema-resolution-imports-shard-2 check-lang-mutants-sema-resolution-imports-shard-3 check-lang-mutants-sema-resolution-imports-shard-4

check-lang-mutants-sema-resolution-imports-shard-1:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema import resolution mutants shard 1/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 0/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/resolve/mod.rs --re 'resolve_use_declarations|check_import_target|check_use_cycles|dfs_use_cycle|import_is_visible|bindings_without' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-resolution-imports.1-of-$(MUTANTS_SHARD_TOTAL) -- --lib resolve $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-imports-shard-2:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema import resolution mutants shard 2/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 1/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/resolve/mod.rs --re 'resolve_use_declarations|check_import_target|check_use_cycles|dfs_use_cycle|import_is_visible|bindings_without' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-resolution-imports.2-of-$(MUTANTS_SHARD_TOTAL) -- --lib resolve $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-imports-shard-3:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema import resolution mutants shard 3/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 2/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/resolve/mod.rs --re 'resolve_use_declarations|check_import_target|check_use_cycles|dfs_use_cycle|import_is_visible|bindings_without' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-resolution-imports.3-of-$(MUTANTS_SHARD_TOTAL) -- --lib resolve $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-imports-shard-4:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema import resolution mutants shard 4/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 3/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/resolve/mod.rs --re 'resolve_use_declarations|check_import_target|check_use_cycles|dfs_use_cycle|import_is_visible|bindings_without' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-resolution-imports.4-of-$(MUTANTS_SHARD_TOTAL) -- --lib resolve $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-types: check-lang-mutants-sema-resolution-types-core check-lang-mutants-sema-resolution-types-monomorphize check-lang-mutants-sema-resolution-types-validate

check-lang-mutants-sema-resolution-types-core:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema type resolution core mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-sema --file crates/abide-sema/src/elab/resolve/mod.rs --re 'resolve_all_types|resolve_type_refinement_predicates|resolve_ty|resolve_params_lr|base_ty_without_refinement' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-resolution-types-core -- --lib resolve $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-types-monomorphize:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema generic monomorphization mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-sema --file crates/abide-sema/src/elab/resolve/monomorphize.rs --re 'format_mono_name|mono_ty_name|substitute_ty|monomorphize_inline|monomorphize_variant_fields|resolve_nested_generics|monomorphize_generics|collect_all_param_uses' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-resolution-types-monomorphize -- --lib monomorphize $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-types-validate:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema unresolved type validation mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-sema --file crates/abide-sema/src/elab/resolve/validate.rs --re 'validate_remaining_type_params|validate_unresolved_types|collect_ty_params|collect_unresolved' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-resolution-types-validate -- --lib validate $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-expr: check-lang-mutants-sema-resolution-expr-core check-lang-mutants-sema-resolution-expr-relation

check-lang-mutants-sema-resolution-expr-core: check-lang-mutants-sema-resolution-expr-core-shard-1 check-lang-mutants-sema-resolution-expr-core-shard-2 check-lang-mutants-sema-resolution-expr-core-shard-3 check-lang-mutants-sema-resolution-expr-core-shard-4

check-lang-mutants-sema-resolution-expr-core-shard-1:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema expression resolution core mutants shard 1/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 0/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/resolve/expr.rs --re 'resolve_expr|resolve_var_type|resolve_ctor_type_from_context|resolve_comparison_ctor_from_context|infer_field_type|infer_qualcall_type|infer_numeric_binop_type|infer_index_type|set_source_element_type' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-resolution-expr-core.1-of-$(MUTANTS_SHARD_TOTAL) -- --lib resolve $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-expr-core-shard-2:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema expression resolution core mutants shard 2/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 1/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/resolve/expr.rs --re 'resolve_expr|resolve_var_type|resolve_ctor_type_from_context|resolve_comparison_ctor_from_context|infer_field_type|infer_qualcall_type|infer_numeric_binop_type|infer_index_type|set_source_element_type' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-resolution-expr-core.2-of-$(MUTANTS_SHARD_TOTAL) -- --lib resolve $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-expr-core-shard-3:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema expression resolution core mutants shard 3/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 2/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/resolve/expr.rs --re 'resolve_expr|resolve_var_type|resolve_ctor_type_from_context|resolve_comparison_ctor_from_context|infer_field_type|infer_qualcall_type|infer_numeric_binop_type|infer_index_type|set_source_element_type' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-resolution-expr-core.3-of-$(MUTANTS_SHARD_TOTAL) -- --lib resolve $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-expr-core-shard-4:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema expression resolution core mutants shard 4/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 3/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/resolve/expr.rs --re 'resolve_expr|resolve_var_type|resolve_ctor_type_from_context|resolve_comparison_ctor_from_context|infer_field_type|infer_qualcall_type|infer_numeric_binop_type|infer_index_type|set_source_element_type' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-resolution-expr-core.4-of-$(MUTANTS_SHARD_TOTAL) -- --lib resolve $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-expr-relation: check-lang-mutants-sema-resolution-expr-relation-shard-1 check-lang-mutants-sema-resolution-expr-relation-shard-2 check-lang-mutants-sema-resolution-expr-relation-shard-3 check-lang-mutants-sema-resolution-expr-relation-shard-4

check-lang-mutants-sema-resolution-expr-relation-shard-1:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema relation expression mutants shard 1/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 0/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/resolve/expr.rs --re 'relation_columns|relation_type_from_columns|relation_type_from_projection|ty_same|infer_relation_join_type|infer_relation_set_op_type|infer_relation_product_type|relation_project_indices|infer_relation_project_type|infer_relation_transpose_type|infer_relation_closure_type|infer_relation_field_type' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-resolution-expr-relation.1-of-$(MUTANTS_SHARD_TOTAL) -- --lib relation $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-expr-relation-shard-2:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema relation expression mutants shard 2/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 1/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/resolve/expr.rs --re 'relation_columns|relation_type_from_columns|relation_type_from_projection|ty_same|infer_relation_join_type|infer_relation_set_op_type|infer_relation_product_type|relation_project_indices|infer_relation_project_type|infer_relation_transpose_type|infer_relation_closure_type|infer_relation_field_type' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-resolution-expr-relation.2-of-$(MUTANTS_SHARD_TOTAL) -- --lib relation $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-expr-relation-shard-3:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema relation expression mutants shard 3/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 2/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/resolve/expr.rs --re 'relation_columns|relation_type_from_columns|relation_type_from_projection|ty_same|infer_relation_join_type|infer_relation_set_op_type|infer_relation_product_type|relation_project_indices|infer_relation_project_type|infer_relation_transpose_type|infer_relation_closure_type|infer_relation_field_type' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-resolution-expr-relation.3-of-$(MUTANTS_SHARD_TOTAL) -- --lib relation $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-expr-relation-shard-4:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema relation expression mutants shard 4/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 3/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/resolve/expr.rs --re 'relation_columns|relation_type_from_columns|relation_type_from_projection|ty_same|infer_relation_join_type|infer_relation_set_op_type|infer_relation_product_type|relation_project_indices|infer_relation_project_type|infer_relation_transpose_type|infer_relation_closure_type|infer_relation_field_type' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-resolution-expr-relation.4-of-$(MUTANTS_SHARD_TOTAL) -- --lib relation $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-expr-helpers: check-lang-mutants-sema-resolution-expr-expected check-lang-mutants-sema-resolution-expr-constructor check-lang-mutants-sema-collection-expr check-lang-mutants-sema-validation-context

check-lang-mutants-sema-resolution-expr-expected: $(SEMA_RESOLUTION_EXPR_EXPECTED_SHARD_TARGETS)

$(SEMA_RESOLUTION_EXPR_EXPECTED_SHARD_TARGETS): check-lang-mutants-sema-resolution-expr-expected-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema expected expression type mutants shard $*/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_SHARD_TOTAL)" -p abide-sema --file crates/abide-sema/src/elab/resolve/expr.rs --re '$(SEMA_RESOLUTION_EXPR_EXPECTED_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-resolution-expr-expected.$*-of-$(MUTANTS_SHARD_TOTAL) -- --lib resolve $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-expr-constructor: $(SEMA_RESOLUTION_EXPR_CONSTRUCTOR_SHARD_TARGETS)

$(SEMA_RESOLUTION_EXPR_CONSTRUCTOR_SHARD_TARGETS): check-lang-mutants-sema-resolution-expr-constructor-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema constructor resolution mutants shard $*/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_SHARD_TOTAL)" -p abide-sema --file crates/abide-sema/src/elab/resolve/constructor.rs --re '$(SEMA_RESOLUTION_EXPR_CONSTRUCTOR_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-resolution-expr-constructor.$*-of-$(MUTANTS_SHARD_TOTAL) -- --lib constructor $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-collection-expr: $(SEMA_COLLECTION_EXPR_SHARD_TARGETS)

$(SEMA_COLLECTION_EXPR_SHARD_TARGETS): check-lang-mutants-sema-collection-expr-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema expression collection mutants shard $*/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_SHARD_TOTAL)" -p abide-sema --file crates/abide-sema/src/elab/collect/expr.rs --re '$(SEMA_COLLECTION_EXPR_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-collection-expr.$*-of-$(MUTANTS_SHARD_TOTAL) -- --lib collect $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-validation-context: $(SEMA_VALIDATION_CONTEXT_SHARD_TARGETS)

$(SEMA_VALIDATION_CONTEXT_SHARD_TARGETS): check-lang-mutants-sema-validation-context-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema expression validation context mutants shard $*/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_SHARD_TOTAL)" -p abide-sema --file crates/abide-sema/src/elab/resolve/validate.rs --re '$(SEMA_VALIDATION_CONTEXT_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-validation-context.$*-of-$(MUTANTS_SHARD_TOTAL) -- --lib validate $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-assumptions: check-lang-mutants-sema-resolution-assumptions-core check-lang-mutants-sema-resolution-assumptions-event-path

check-lang-mutants-sema-resolution-assumptions-core: check-lang-mutants-sema-resolution-assumptions-core-shard-1 check-lang-mutants-sema-resolution-assumptions-core-shard-2

check-lang-mutants-sema-resolution-assumptions-core-shard-1:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema assumption resolution mutants shard 1/2" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 0/2 -p abide-sema --file crates/abide-sema/src/elab/resolve/assumptions.rs --re 'resolve_assumption_sets|build_assume_delta|build_assume_delta_with_bindings|merge_delta_into|check_under_add_only_resolved|resolve_by_lemmas_subset_containment|format_assumption_set|compute_missing|populate_assumption_set|populate_assumption_set_from_items' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-resolution-assumptions-core.1-of-2 -- --lib assumption $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-assumptions-core-shard-2:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema assumption resolution mutants shard 2/2" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 1/2 -p abide-sema --file crates/abide-sema/src/elab/resolve/assumptions.rs --re 'resolve_assumption_sets|build_assume_delta|build_assume_delta_with_bindings|merge_delta_into|check_under_add_only_resolved|resolve_by_lemmas_subset_containment|format_assumption_set|compute_missing|populate_assumption_set|populate_assumption_set_from_items' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-resolution-assumptions-core.2-of-2 -- --lib assumption $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-assumptions-event-path: check-lang-mutants-sema-resolution-assumptions-event-path-shard-1 check-lang-mutants-sema-resolution-assumptions-event-path-shard-2

check-lang-mutants-sema-resolution-assumptions-event-path-shard-1:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema event path resolution mutants shard 1/2" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 0/2 -p abide-sema --file crates/abide-sema/src/elab/resolve/mod.rs --re 'resolve_event_path' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-resolution-assumptions-event-path.1-of-2 -- --lib event_path $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-resolution-assumptions-event-path-shard-2:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema event path resolution mutants shard 2/2" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 1/2 -p abide-sema --file crates/abide-sema/src/elab/resolve/mod.rs --re 'resolve_event_path' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-resolution-assumptions-event-path.2-of-2 -- --lib event_path $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-checker: check-lang-mutants-sema-checker-core check-lang-mutants-sema-checker-entity check-lang-mutants-sema-checker-system check-lang-mutants-sema-checker-matches check-lang-mutants-sema-checker-ctors

check-lang-mutants-sema-checker-core: check-lang-mutants-sema-checker-core-shard-1 check-lang-mutants-sema-checker-core-shard-2 check-lang-mutants-sema-checker-core-shard-3 check-lang-mutants-sema-checker-core-shard-4

check-lang-mutants-sema-checker-core-shard-1:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema checker core mutants shard 1/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 0/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/check/mod.rs --re 'check_type|check_collection_homogeneity|types_compatible|expr_compatible_with_ty|check_unresolved_constructors|check_fn_contracts|check_refinement_predicates|check_verifier_surface_expr|check_verifier_surface_expr_allowing_sequence|find_sequence_composition_span|find_unsupported_verifier_expr|check_pred_prop_cycles|collect_name_refs|dfs_find_cycle|collect_epattern_vars' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-checker-core.1-of-$(MUTANTS_SHARD_TOTAL) -- --lib check $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-checker-core-shard-2:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema checker core mutants shard 2/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 1/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/check/mod.rs --re 'check_type|check_collection_homogeneity|types_compatible|expr_compatible_with_ty|check_unresolved_constructors|check_fn_contracts|check_refinement_predicates|check_verifier_surface_expr|check_verifier_surface_expr_allowing_sequence|find_sequence_composition_span|find_unsupported_verifier_expr|check_pred_prop_cycles|collect_name_refs|dfs_find_cycle|collect_epattern_vars' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-checker-core.2-of-$(MUTANTS_SHARD_TOTAL) -- --lib check $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-checker-core-shard-3:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema checker core mutants shard 3/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 2/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/check/mod.rs --re 'check_type|check_collection_homogeneity|types_compatible|expr_compatible_with_ty|check_unresolved_constructors|check_fn_contracts|check_refinement_predicates|check_verifier_surface_expr|check_verifier_surface_expr_allowing_sequence|find_sequence_composition_span|find_unsupported_verifier_expr|check_pred_prop_cycles|collect_name_refs|dfs_find_cycle|collect_epattern_vars' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-checker-core.3-of-$(MUTANTS_SHARD_TOTAL) -- --lib check $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-checker-core-shard-4:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema checker core mutants shard 4/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 3/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/check/mod.rs --re 'check_type|check_collection_homogeneity|types_compatible|expr_compatible_with_ty|check_unresolved_constructors|check_fn_contracts|check_refinement_predicates|check_verifier_surface_expr|check_verifier_surface_expr_allowing_sequence|find_sequence_composition_span|find_unsupported_verifier_expr|check_pred_prop_cycles|collect_name_refs|dfs_find_cycle|collect_epattern_vars' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-checker-core.4-of-$(MUTANTS_SHARD_TOTAL) -- --lib check $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-checker-entity:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema entity checker mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-sema --file crates/abide-sema/src/elab/check/entity.rs --re 'check_entity|check_invariant_body_no_liveness|check_field|check_action|check_assignment' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-checker-entity -- --lib entity $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-checker-system: check-lang-mutants-sema-checker-system-core check-lang-mutants-sema-checker-system-interface check-lang-mutants-sema-checker-system-extern check-lang-mutants-sema-checker-system-return check-lang-mutants-sema-checker-system-proc-deps

check-lang-mutants-sema-checker-system-core: check-lang-mutants-sema-checker-system-core-shard-1 check-lang-mutants-sema-checker-system-core-shard-2 check-lang-mutants-sema-checker-system-core-shard-3 check-lang-mutants-sema-checker-system-core-shard-4

check-lang-mutants-sema-checker-system-core-shard-1:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema system checker core mutants shard 1/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 0/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/check/system.rs --re 'check_system' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-checker-system-core.1-of-$(MUTANTS_SHARD_TOTAL) -- --lib system $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-checker-system-core-shard-2:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema system checker core mutants shard 2/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 1/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/check/system.rs --re 'check_system' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-checker-system-core.2-of-$(MUTANTS_SHARD_TOTAL) -- --lib system $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-checker-system-core-shard-3:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema system checker core mutants shard 3/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 2/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/check/system.rs --re 'check_system' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-checker-system-core.3-of-$(MUTANTS_SHARD_TOTAL) -- --lib system $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-checker-system-core-shard-4:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema system checker core mutants shard 4/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 3/$(MUTANTS_SHARD_TOTAL) -p abide-sema --file crates/abide-sema/src/elab/check/system.rs --re 'check_system' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-checker-system-core.4-of-$(MUTANTS_SHARD_TOTAL) -- --lib system $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-checker-system-interface:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema interface conformance mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-sema --file crates/abide-sema/src/elab/check/system.rs --re 'check_interface_conformance' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-checker-system-interface -- --lib interface $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-checker-system-extern:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema extern checker mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-sema --file crates/abide-sema/src/elab/check/system.rs --re 'check_extern' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-checker-system-extern -- --lib check_extern $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-checker-system-return:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema system return helper mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-sema --file crates/abide-sema/src/elab/check/system.rs --re 'extract_return_ctor_name|extract_return_payload' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-checker-system-return -- --lib return $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-checker-system-proc-deps:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema proc dependency checker mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-sema --file crates/abide-sema/src/elab/check/system.rs --re 'validate_proc_dep_cond' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-checker-system-proc-deps -- --lib proc_dep $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-checker-matches:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema match checker mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-sema --file crates/abide-sema/src/elab/check/matches.rs --re 'check_match_exhaustiveness|pattern_is_catchall|collect_covered_ctors|check_pattern_shape|resolve_to_enum_info|resolve_field_type' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-checker-matches -- --lib match $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-checker-ctors:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema constructor checker mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-sema --file crates/abide-sema/src/elab/check/ctors.rs --re 'walk_event_action_for_ctor_check|check_ctor_records_in_expr' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-checker-ctors -- --lib ctor $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-sema-diagnostics:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-sema diagnostic mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-sema --file crates/abide-sema/src/elab/error.rs --output $(MUTANTS_OUTPUT_DIR)/mutants.out.sema-diagnostics -- --lib error $(MUTANTS_LIBTEST_ARGS)

IR_LOWERING_CORE_RE := lower_interface|lower_params|lower_type|lower_ty|lower_builtin|lower_const|lower_contracts|lower_while_contracts|lower_fn|lower_pred|lower_prop|lower_entity|lower_derived_field|lower_invariant|lower_fsm|lower_field|lower_action|lower_verify|lower_theorem|lower_axiom|lower_lemma|lower_scene|lower_given|lower_scene_action
IR_LOWERING_SYSTEM_RE := lower_system|lower_extern|lower_proc|lower_proc_params|lower_proc_node_actions|lower_proc_dep_cond|lower_query|lower_system_action|lower_event_action
IR_LOWERING_EXPR_RE := lower_expr|lower_var_expr|lower_binop_expr|lower_call_expr|lower_call_ref_expr|lower_qualified_call_expr|lower_relation_field_call|lower_relation_project_call|lower_relation_projection_columns|lower_builtin_qualified_call|lower_qualified_expr|lower_quant_expr|lower_let_expr|lower_lambda_expr|lower_tuple_lit_expr|lower_match_expr|lower_set_comp_expr|lower_rel_comp_expr|lower_while_expr|lower_aggregate_expr|lower_saw_expr|lower_ctor_record_expr|lower_pattern|lower_pattern_for_scrutinee|lower_lit|lower_binop|lower_unop

check-lang-mutants-ir-lowering: check-lang-mutants-ir-lowering-core check-lang-mutants-ir-lowering-system check-lang-mutants-ir-lowering-expr check-lang-mutants-ir-lowering-qualify

check-lang-mutants-ir-lowering-core:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-ir core lowering mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-ir --file crates/abide-ir/src/ir/lower/mod.rs --re '$(IR_LOWERING_CORE_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.ir-lowering-core -- --lib lower $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-ir-lowering-system:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-ir system lowering mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-ir --file crates/abide-ir/src/ir/lower/system.rs --re '$(IR_LOWERING_SYSTEM_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.ir-lowering-system -- --lib lower $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-ir-lowering-expr: check-lang-mutants-ir-lowering-expr-shard-1 check-lang-mutants-ir-lowering-expr-shard-2 check-lang-mutants-ir-lowering-expr-shard-3 check-lang-mutants-ir-lowering-expr-shard-4

check-lang-mutants-ir-lowering-expr-shard-1:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-ir expression lowering mutants shard 1/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 0/$(MUTANTS_SHARD_TOTAL) -p abide-ir --file crates/abide-ir/src/ir/lower/expr.rs --re '$(IR_LOWERING_EXPR_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.ir-lowering-expr.1-of-$(MUTANTS_SHARD_TOTAL) -- --lib lower $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-ir-lowering-expr-shard-2:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-ir expression lowering mutants shard 2/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 1/$(MUTANTS_SHARD_TOTAL) -p abide-ir --file crates/abide-ir/src/ir/lower/expr.rs --re '$(IR_LOWERING_EXPR_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.ir-lowering-expr.2-of-$(MUTANTS_SHARD_TOTAL) -- --lib lower $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-ir-lowering-expr-shard-3:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-ir expression lowering mutants shard 3/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 2/$(MUTANTS_SHARD_TOTAL) -p abide-ir --file crates/abide-ir/src/ir/lower/expr.rs --re '$(IR_LOWERING_EXPR_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.ir-lowering-expr.3-of-$(MUTANTS_SHARD_TOTAL) -- --lib lower $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-ir-lowering-expr-shard-4:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-ir expression lowering mutants shard 4/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard 3/$(MUTANTS_SHARD_TOTAL) -p abide-ir --file crates/abide-ir/src/ir/lower/expr.rs --re '$(IR_LOWERING_EXPR_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.ir-lowering-expr.4-of-$(MUTANTS_SHARD_TOTAL) -- --lib lower $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-ir-lowering-qualify:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide-ir qualification lowering mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-ir --file crates/abide-ir/src/ir/lower/qualify.rs --re 'qualify_query_vars_scoped|qualify_action_query_vars' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.ir-lowering-qualify -- --lib qualify $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-cli-project: check-lang-mutants-cli-project-baseline check-lang-mutants-cli-project-targets check-lang-mutants-cli-project-helpers

check-lang-mutants-cli-project-baseline:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_CLI_TIMEOUT_SECS) --label "abide CLI project mutants-profile prebuild" -- $(MUTANTS_ENV) $(CARGO) test -p abide --lib --profile $(MUTANTS_PROFILE) --no-run
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide CLI project baseline tests" -- $(MUTANTS_ENV) $(CARGO) test -p abide --lib cli::tests $(MUTANTS_LIBTEST_ARGS)
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "abide target discovery baseline tests" -- $(MUTANTS_ENV) $(CARGO) test -p abide --lib targets::tests $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-cli-project-targets: $(CLI_PROJECT_TARGET_SHARD_TARGETS)

$(CLI_PROJECT_TARGET_SHARD_TARGETS): check-lang-mutants-cli-project-targets-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_CLI_TIMEOUT_SECS) --label "abide CLI target discovery mutants shard $*/$(MUTANTS_CLI_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_CLI_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_CLI_SHARD_TOTAL)" -p abide --file crates/abide/src/targets.rs --output $(MUTANTS_OUTPUT_DIR)/mutants.out.cli-project-targets.$*-of-$(MUTANTS_CLI_SHARD_TOTAL) -- --lib targets $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-cli-project-helpers: $(CLI_PROJECT_HELPER_SHARD_TARGETS)

$(CLI_PROJECT_HELPER_SHARD_TARGETS): check-lang-mutants-cli-project-helpers-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_CLI_TIMEOUT_SECS) --label "abide CLI helper mutants shard $*/$(MUTANTS_CLI_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_CLI_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_CLI_SHARD_TOTAL)" -p abide --file crates/abide/src/cli.rs --re '$(CLI_PROJECT_HELPERS_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.cli-project-helpers.$*-of-$(MUTANTS_CLI_SHARD_TOTAL) -- --lib cli $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-qa: check-lang-mutants-qa-baseline check-lang-mutants-qa-parse check-lang-mutants-qa-exec check-lang-mutants-qa-runner check-lang-mutants-qa-extract check-lang-mutants-qa-support

check-lang-mutants-qa-baseline:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_QA_TIMEOUT_SECS) --label "abide QA mutants-profile prebuild" -- $(MUTANTS_ENV) $(CARGO) test -p abide-qa --lib --profile $(MUTANTS_PROFILE) --no-run
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_QA_TIMEOUT_SECS) --label "abide QA mutants-profile baseline tests" -- $(MUTANTS_ENV) $(CARGO) test -p abide-qa --lib --profile $(MUTANTS_PROFILE) $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-qa-parse: $(QA_PARSE_SHARD_TARGETS)

$(QA_PARSE_SHARD_TARGETS): check-lang-mutants-qa-parse-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_QA_TIMEOUT_SECS) --label "abide QA parser mutants shard $*/$(MUTANTS_QA_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_QA_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_QA_SHARD_TOTAL)" -p abide-qa --file crates/abide-qa/src/qa/parse.rs --output $(MUTANTS_OUTPUT_DIR)/mutants.out.qa-parse.$*-of-$(MUTANTS_QA_SHARD_TOTAL) -- --lib parse $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-qa-exec: $(QA_EXEC_SHARD_TARGETS)

$(QA_EXEC_SHARD_TARGETS): check-lang-mutants-qa-exec-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_QA_TIMEOUT_SECS) --label "abide QA execution mutants shard $*/$(MUTANTS_QA_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_QA_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_QA_SHARD_TOTAL)" -p abide-qa --file crates/abide-qa/src/qa/exec.rs --output $(MUTANTS_OUTPUT_DIR)/mutants.out.qa-exec.$*-of-$(MUTANTS_QA_SHARD_TOTAL) -- --lib exec $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-qa-runner: $(QA_RUNNER_SHARD_TARGETS)

$(QA_RUNNER_SHARD_TARGETS): check-lang-mutants-qa-runner-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_QA_TIMEOUT_SECS) --label "abide QA runner mutants shard $*/$(MUTANTS_QA_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_QA_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_QA_SHARD_TOTAL)" -p abide-qa --file crates/abide-qa/src/qa/runner.rs --re '$(QA_RUNNER_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.qa-runner.$*-of-$(MUTANTS_QA_SHARD_TOTAL) -- --lib runner $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-qa-extract: $(QA_EXTRACT_SHARD_TARGETS)

$(QA_EXTRACT_SHARD_TARGETS): check-lang-mutants-qa-extract-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_QA_TIMEOUT_SECS) --label "abide QA extraction mutants shard $*/$(MUTANTS_QA_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_QA_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_QA_SHARD_TOTAL)" -p abide-qa --file crates/abide-qa/src/qa/extract.rs --re '$(QA_EXTRACT_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.qa-extract.$*-of-$(MUTANTS_QA_SHARD_TOTAL) -- --lib extract $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-qa-support: check-lang-mutants-qa-format check-lang-mutants-qa-graph check-lang-mutants-qa-complete check-lang-mutants-qa-validate check-lang-mutants-qa-artifacts

check-lang-mutants-qa-format:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_QA_TIMEOUT_SECS) --label "abide QA formatting mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_QA_COMMON_ARGS) -p abide-qa --file crates/abide-qa/src/qa/fmt.rs --re '$(QA_SUPPORT_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.qa-format -- --lib fmt $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-qa-graph:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_QA_TIMEOUT_SECS) --label "abide QA graph mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_QA_COMMON_ARGS) -p abide-qa --file crates/abide-qa/src/qa/graph.rs --re '$(QA_SUPPORT_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.qa-graph -- --lib graph $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-qa-complete:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_QA_TIMEOUT_SECS) --label "abide QA completion mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_QA_COMMON_ARGS) -p abide-qa --file crates/abide-qa/src/qa/complete.rs --re '$(QA_SUPPORT_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.qa-complete -- --lib complete $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-qa-validate:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_QA_TIMEOUT_SECS) --label "abide QA validation mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_QA_COMMON_ARGS) -p abide-qa --file crates/abide-qa/src/qa/validate.rs --re '$(QA_SUPPORT_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.qa-validate -- --lib validate $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-qa-artifacts:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_QA_TIMEOUT_SECS) --label "abide QA artifact rendering mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_QA_COMMON_ARGS) -p abide-qa --file crates/abide-qa/src/qa/artifacts.rs --re '$(QA_SUPPORT_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.qa-artifacts -- --lib artifacts $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-lsp: check-lang-mutants-lsp-baseline $(LSP_SHARD_TARGETS)

check-lang-mutants-lsp-baseline:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_LSP_TIMEOUT_SECS) --label "abide LSP mutants-profile prebuild" -- $(MUTANTS_ENV) $(CARGO) test -p abide-lsp --profile $(MUTANTS_PROFILE) --no-run
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_LSP_TIMEOUT_SECS) --label "abide LSP mutants-profile baseline tests" -- $(MUTANTS_ENV) $(CARGO) test -p abide-lsp --profile $(MUTANTS_PROFILE) $(MUTANTS_LIBTEST_ARGS)

$(LSP_SHARD_TARGETS): check-lang-mutants-lsp-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_LSP_TIMEOUT_SECS) --label "abide LSP mutants shard $*/$(MUTANTS_LSP_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_LSP_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_LSP_SHARD_TOTAL)" -p abide-lsp --file crates/abide-lsp/src/main.rs --re '$(LSP_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.lsp.$*-of-$(MUTANTS_LSP_SHARD_TOTAL) -- --bin abide-lsp tests $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-lsp-semantic: check-lang-mutants-lsp-baseline $(LSP_SEMANTIC_SHARD_TARGETS)

$(LSP_SEMANTIC_SHARD_TARGETS): check-lang-mutants-lsp-semantic-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_LSP_TIMEOUT_SECS) --label "abide LSP semantic mutants shard $*/$(MUTANTS_LSP_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_LSP_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_LSP_SHARD_TOTAL)" -p abide-lsp --file crates/abide-lsp/src/main.rs --re '$(LSP_SEMANTIC_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.lsp-semantic.$*-of-$(MUTANTS_LSP_SHARD_TOTAL) -- --bin abide-lsp tests $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-lsp-project: check-lang-mutants-lsp-baseline $(LSP_PROJECT_SHARD_TARGETS)

$(LSP_PROJECT_SHARD_TARGETS): check-lang-mutants-lsp-project-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_LSP_TIMEOUT_SECS) --label "abide LSP project mutants shard $*/$(MUTANTS_LSP_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_LSP_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_LSP_SHARD_TOTAL)" -p abide-lsp --file crates/abide-lsp/src/main.rs --re '$(LSP_PROJECT_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.lsp-project.$*-of-$(MUTANTS_LSP_SHARD_TOTAL) -- --bin abide-lsp tests $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-ide-workspace-index: check-lang-mutants-ide-workspace-index-baseline $(IDE_WORKSPACE_INDEX_SHARD_TARGETS)

check-lang-mutants-ide-workspace-index-baseline:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_IDE_TIMEOUT_SECS) --label "abide IDE workspace-index mutants-profile prebuild" -- $(MUTANTS_ENV) $(CARGO) test -p abide --lib --profile $(MUTANTS_PROFILE) --no-run
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_IDE_TIMEOUT_SECS) --label "abide IDE workspace-index baseline tests" -- $(MUTANTS_ENV) $(CARGO) test -p abide --lib --profile $(MUTANTS_PROFILE) ide::tests $(MUTANTS_LIBTEST_ARGS)

$(IDE_WORKSPACE_INDEX_SHARD_TARGETS): check-lang-mutants-ide-workspace-index-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_IDE_TIMEOUT_SECS) --label "abide IDE workspace-index mutants shard $*/$(MUTANTS_IDE_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_IDE_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_IDE_SHARD_TOTAL)" -p abide --file crates/abide/src/ide.rs --re '$(IDE_WORKSPACE_INDEX_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.ide-workspace-index.$*-of-$(MUTANTS_IDE_SHARD_TOTAL) -- --lib ide $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-ide-workspace-index-focused: check-lang-mutants-ide-workspace-index-boundary check-lang-mutants-ide-workspace-index-block-frames check-lang-mutants-ide-workspace-index-find-name-span

check-lang-mutants-ide-workspace-index-boundary:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_IDE_FOCUSED_TIMEOUT_SECS) --label "abide IDE boundary helper mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_IDE_COMMON_ARGS) -p abide --file crates/abide/src/ide.rs --re 'clamp_to_char_boundary' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.ide-workspace-index.boundary -- --lib cursor_helpers_handle_utf8_boundaries_keywords_and_nested_blocks $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-ide-workspace-index-block-frames:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_IDE_FOCUSED_TIMEOUT_SECS) --label "abide IDE block-frame helper mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_IDE_COMMON_ARGS) -p abide --file crates/abide/src/ide.rs --re 'block_frames|block_depth|block_frame_from_header' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.ide-workspace-index.block-frames -- --lib cursor_helpers_handle_utf8_boundaries_keywords_and_nested_blocks $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-ide-workspace-index-find-name-span:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_IDE_FOCUSED_TIMEOUT_SECS) --label "abide IDE name-span helper mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_IDE_COMMON_ARGS) -p abide --file crates/abide/src/ide.rs --re 'find_name_span' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.ide-workspace-index.find-name-span -- --lib name_span_and_symbol_detail_are_scoped_to_decl_span $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-verifier-expr: check-lang-mutants-verifier-expr-property-quantifier check-lang-mutants-verifier-expr-property-constructor check-lang-mutants-verifier-expr-slot check-lang-mutants-verifier-expr-collections check-lang-mutants-verifier-expr-pooled-support

check-lang-mutants-verifier-expr-property-quantifier:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_EXPR_TIMEOUT_SECS) --label "abide verifier property quantifier helper mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_EXPR_COMMON_ARGS) -p abide-verify --file crates/abide-verify/src/verify/property.rs --re '$(VERIFIER_EXPR_PROPERTY_QUANTIFIER_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.verifier-expr.property-quantifier -- --lib encode_prop_quantifier $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-verifier-expr-property-constructor:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_EXPR_TIMEOUT_SECS) --label "abide verifier property constructor/field/call helper mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_EXPR_COMMON_ARGS) -p abide-verify --file crates/abide-verify/src/verify/property.rs --re '$(VERIFIER_EXPR_PROPERTY_CONSTRUCTOR_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.verifier-expr.property-constructor -- --lib encode_prop_constructor_field_or_call_helper_covers_dispatch_family $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-verifier-expr-slot: $(VERIFIER_EXPR_SLOT_SHARD_TARGETS)

check-lang-mutants-verifier-expr-slot-shard-1:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_EXPR_TIMEOUT_SECS) --label "abide verifier slot expression helper mutants shard 1/$(MUTANTS_VERIFY_EXPR_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_EXPR_COMMON_ARGS) -p abide-verify --file crates/abide-verify/src/verify/harness/expr.rs --re '$(VERIFIER_EXPR_SLOT_SHARD_1_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.verifier-expr.slot.1-of-$(MUTANTS_VERIFY_EXPR_SHARD_TOTAL) -- --lib slot_expr $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-verifier-expr-slot-shard-2:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_EXPR_TIMEOUT_SECS) --label "abide verifier slot expression helper mutants shard 2/$(MUTANTS_VERIFY_EXPR_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_EXPR_COMMON_ARGS) -p abide-verify --file crates/abide-verify/src/verify/harness/expr.rs --re '$(VERIFIER_EXPR_SLOT_SHARD_2_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.verifier-expr.slot.2-of-$(MUTANTS_VERIFY_EXPR_SHARD_TOTAL) -- --lib slot_expr $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-verifier-expr-slot-shard-3:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_EXPR_TIMEOUT_SECS) --label "abide verifier slot expression helper mutants shard 3/$(MUTANTS_VERIFY_EXPR_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_EXPR_COMMON_ARGS) -p abide-verify --file crates/abide-verify/src/verify/harness/expr.rs --re '$(VERIFIER_EXPR_SLOT_SHARD_3_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.verifier-expr.slot.3-of-$(MUTANTS_VERIFY_EXPR_SHARD_TOTAL) -- --lib slot_expr $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-verifier-expr-slot-shard-4:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_EXPR_TIMEOUT_SECS) --label "abide verifier slot expression helper mutants shard 4/$(MUTANTS_VERIFY_EXPR_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_EXPR_COMMON_ARGS) -p abide-verify --file crates/abide-verify/src/verify/harness/expr.rs --re '$(VERIFIER_EXPR_SLOT_SHARD_4_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.verifier-expr.slot.4-of-$(MUTANTS_VERIFY_EXPR_SHARD_TOTAL) -- --lib slot_expr $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-verifier-expr-collections:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_EXPR_TIMEOUT_SECS) --label "abide verifier finite collection helper mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_EXPR_COMMON_ARGS) -p abide-verify --file crates/abide-verify/src/verify/collections.rs --re '$(VERIFIER_EXPR_COLLECTION_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.verifier-expr.collections -- --lib finite_collection_helpers $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-verifier-expr-pooled-support:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_EXPR_TIMEOUT_SECS) --label "abide verifier pooled SyGuS support diagnostic mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_EXPR_COMMON_ARGS) -p abide-verify --file crates/abide-verify/src/verify/sygus/pooled.rs --re '$(VERIFIER_EXPR_POOLED_SUPPORT_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.verifier-expr.pooled-support -- --lib pooled_sygus $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-fn-vc: check-lang-mutants-fn-vc-shard-1 check-lang-mutants-fn-vc-shard-2 check-lang-mutants-fn-vc-shard-3 check-lang-mutants-fn-vc-shard-4

check-lang-mutants-fn-vc-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "abide-verify function VC mutants shard $*/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_SHARD_TOTAL)" -p abide-verify --file crates/abide-verify/src/verify/fn_verify.rs --output $(MUTANTS_OUTPUT_DIR)/mutants.out.fn-vc.$*-of-$(MUTANTS_SHARD_TOTAL) -- --lib fn_contract $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-smt-facade: check-lang-mutants-smt-facade-shard-1 check-lang-mutants-smt-facade-shard-2 check-lang-mutants-smt-facade-shard-3 check-lang-mutants-smt-facade-shard-4

check-lang-mutants-smt-facade-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "abide-verify SMT facade mutants shard $*/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_SHARD_TOTAL)" -p abide-verify --file crates/abide-verify/src/verify/smt.rs --output $(MUTANTS_OUTPUT_DIR)/mutants.out.smt-facade.$*-of-$(MUTANTS_SHARD_TOTAL) -- --lib smt $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-solver-routing: check-lang-mutants-solver-routing-shard-1 check-lang-mutants-solver-routing-shard-2 check-lang-mutants-solver-routing-shard-3 check-lang-mutants-solver-routing-shard-4

check-lang-mutants-solver-routing-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "abide-verify solver routing mutants shard $*/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_SHARD_TOTAL)" -p abide-verify --file crates/abide-verify/src/verify/solver.rs --re 'SolverCapabilities|backend_score|set_active_solver_family|is_solver_family_available|AbideSolver|z3_check_chc' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.solver-routing.$*-of-$(MUTANTS_SHARD_TOTAL) -- --lib solver $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-runtime-backend: check-lang-mutants-runtime-backend-shard-1 check-lang-mutants-runtime-backend-shard-2 check-lang-mutants-runtime-backend-shard-3 check-lang-mutants-runtime-backend-shard-4

check-lang-mutants-runtime-backend-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "abide-verify runtime backend mutants shard $*/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_SHARD_TOTAL)" -p abide-verify --file crates/abide-verify/src/verify/solver.rs --re 'RuntimeBackend|RuntimeModel|RuntimeDynamic|RuntimeBool|RuntimeInt|RuntimeReal|RuntimeArray|RuntimeModelEval' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.runtime-backend.$*-of-$(MUTANTS_SHARD_TOTAL) -- --lib solver $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-verify: check-lang-mutants-fn-vc check-lang-mutants-smt-facade check-lang-mutants-solver-routing check-lang-mutants-runtime-backend check-lang-mutants-verifier-expr

check-lang-mutants-wnby: check-lang-mutants-core check-lang-mutants-syntax-parser check-lang-mutants-sema-expr-helpers check-lang-mutants-sema-checker check-lang-mutants-ir-lowering check-lang-mutants-fn-vc check-lang-mutants-smt-facade check-lang-mutants-solver-routing check-lang-mutants-runtime-backend check-lang-mutants-verifier-expr check-lang-mutants-wnby-ir-types check-lang-mutants-wnby-sema-collect-types check-lang-mutants-wnby-syntax-lex check-lang-mutants-wnby-simulate check-lang-mutants-wnby-verify-literal check-lang-mutants-wnby-verify-support check-lang-mutants-wnby-verify-explicit check-lang-mutants-wnby-verify-float-route check-lang-mutants-wnby-verify-temporal check-lang-mutants-wnby-verify-theorem-transition check-lang-mutants-wnby-verify-relational check-lang-mutants-wnby-verify-harness check-lang-mutants-wnby-verify-ic3 check-lang-mutants-wnby-verify-sygus-core check-lang-mutants-wnby-verify-pure-scene check-lang-mutants-wnby-verify-dispatch

check-lang-mutants-wnby-ir-types:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "wnby IR typed-operator/type helper mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-ir --file crates/abide-ir/src/ir/types.rs --re '$(WNBY_IR_TYPES_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.ir-types -- --lib types $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-wnby-sema-collect-types:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "wnby sema collection/type helper mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-sema --file crates/abide-sema/src/elab/collect/entity.rs --file crates/abide-sema/src/elab/collect/system.rs --file crates/abide-sema/src/elab/types.rs --re '$(WNBY_SEMA_COLLECT_TYPES_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.sema-collect-types -- --lib collect $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-wnby-syntax-lex:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "wnby lexer overflow/diagnostic mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) -p abide-syntax --file crates/abide-syntax/src/lex.rs --re '$(WNBY_SYNTAX_LEX_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.syntax-lex -- --lib lex $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-wnby-simulate:
	$(MAKE) check-lang-mutants-wnby-simulate-shard-1
	$(MAKE) check-lang-mutants-wnby-simulate-shard-2
	$(MAKE) check-lang-mutants-wnby-simulate-shard-3
	$(MAKE) check-lang-mutants-wnby-simulate-shard-4

check-lang-mutants-wnby-simulate-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_TIMEOUT_SECS) --label "wnby simulator concrete-semantics mutants shard $*/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_SHARD_TOTAL)" -p abide --file crates/abide/src/simulate.rs --re '$(WNBY_SIMULATE_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.simulate.$*-of-$(MUTANTS_SHARD_TOTAL) -- --lib simulate $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-wnby-verify-literal:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby verifier literal/string mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) -p abide-verify --file crates/abide-verify/src/verify/literal.rs --re '$(WNBY_VERIFY_LITERAL_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-literal -- --lib literal $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-wnby-verify-support:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby verifier support/corpus mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) -p abide-verify --file crates/abide-verify/src/verify/support.rs --file crates/abide-verify/src/verify/unsupported_corpus.rs --re '$(WNBY_VERIFY_SUPPORT_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-support -- --lib support $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-wnby-verify-explicit:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby explicit-state evaluator mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) -p abide-verify --file crates/abide-verify/src/verify/explicit.rs --re '$(WNBY_VERIFY_EXPLICIT_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-explicit -- --lib explicit $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-wnby-verify-float-route:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby verifier float-routing mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) -p abide-verify --file crates/abide-verify/src/verify/float_route.rs --re '$(WNBY_VERIFY_FLOAT_ROUTE_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-float-route -- --lib float_route $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-wnby-verify-temporal:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby temporal/liveness mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard 0/$(MUTANTS_SHARD_TOTAL) -p abide-verify --file crates/abide-verify/src/verify/temporal.rs --file crates/abide-verify/src/verify/ltl.rs --re '$(WNBY_VERIFY_TEMPORAL_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-temporal.1-of-$(MUTANTS_SHARD_TOTAL) -- --lib temporal $(MUTANTS_LIBTEST_ARGS)
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby temporal/liveness mutants shard 2/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard 1/$(MUTANTS_SHARD_TOTAL) -p abide-verify --file crates/abide-verify/src/verify/temporal.rs --file crates/abide-verify/src/verify/ltl.rs --re '$(WNBY_VERIFY_TEMPORAL_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-temporal.2-of-$(MUTANTS_SHARD_TOTAL) -- --lib temporal $(MUTANTS_LIBTEST_ARGS)
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby temporal/liveness mutants shard 3/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard 2/$(MUTANTS_SHARD_TOTAL) -p abide-verify --file crates/abide-verify/src/verify/temporal.rs --file crates/abide-verify/src/verify/ltl.rs --re '$(WNBY_VERIFY_TEMPORAL_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-temporal.3-of-$(MUTANTS_SHARD_TOTAL) -- --lib temporal $(MUTANTS_LIBTEST_ARGS)
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby temporal/liveness mutants shard 4/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard 3/$(MUTANTS_SHARD_TOTAL) -p abide-verify --file crates/abide-verify/src/verify/temporal.rs --file crates/abide-verify/src/verify/ltl.rs --re '$(WNBY_VERIFY_TEMPORAL_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-temporal.4-of-$(MUTANTS_SHARD_TOTAL) -- --lib temporal $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-wnby-verify-theorem-transition:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby theorem/transition mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard 0/$(MUTANTS_SHARD_TOTAL) -p abide-verify --file crates/abide-verify/src/verify/theorem.rs --file crates/abide-verify/src/verify/transition.rs --re '$(WNBY_VERIFY_THEOREM_TRANSITION_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-theorem-transition.1-of-$(MUTANTS_SHARD_TOTAL) -- --lib theorem $(MUTANTS_LIBTEST_ARGS)
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby theorem/transition mutants shard 2/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard 1/$(MUTANTS_SHARD_TOTAL) -p abide-verify --file crates/abide-verify/src/verify/theorem.rs --file crates/abide-verify/src/verify/transition.rs --re '$(WNBY_VERIFY_THEOREM_TRANSITION_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-theorem-transition.2-of-$(MUTANTS_SHARD_TOTAL) -- --lib theorem $(MUTANTS_LIBTEST_ARGS)
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby theorem/transition mutants shard 3/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard 2/$(MUTANTS_SHARD_TOTAL) -p abide-verify --file crates/abide-verify/src/verify/theorem.rs --file crates/abide-verify/src/verify/transition.rs --re '$(WNBY_VERIFY_THEOREM_TRANSITION_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-theorem-transition.3-of-$(MUTANTS_SHARD_TOTAL) -- --lib theorem $(MUTANTS_LIBTEST_ARGS)
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby theorem/transition mutants shard 4/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard 3/$(MUTANTS_SHARD_TOTAL) -p abide-verify --file crates/abide-verify/src/verify/theorem.rs --file crates/abide-verify/src/verify/transition.rs --re '$(WNBY_VERIFY_THEOREM_TRANSITION_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-theorem-transition.4-of-$(MUTANTS_SHARD_TOTAL) -- --lib theorem $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-wnby-verify-relational:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby relational backend mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard 0/$(MUTANTS_SHARD_TOTAL) -p abide-verify --file crates/abide-verify/src/verify/relational.rs --file crates/abide-verify/src/verify/relation_sat.rs --re '$(WNBY_VERIFY_RELATIONAL_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-relational.1-of-$(MUTANTS_SHARD_TOTAL) -- --lib relational $(MUTANTS_LIBTEST_ARGS)
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby relational backend mutants shard 2/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard 1/$(MUTANTS_SHARD_TOTAL) -p abide-verify --file crates/abide-verify/src/verify/relational.rs --file crates/abide-verify/src/verify/relation_sat.rs --re '$(WNBY_VERIFY_RELATIONAL_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-relational.2-of-$(MUTANTS_SHARD_TOTAL) -- --lib relational $(MUTANTS_LIBTEST_ARGS)
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby relational backend mutants shard 3/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard 2/$(MUTANTS_SHARD_TOTAL) -p abide-verify --file crates/abide-verify/src/verify/relational.rs --file crates/abide-verify/src/verify/relation_sat.rs --re '$(WNBY_VERIFY_RELATIONAL_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-relational.3-of-$(MUTANTS_SHARD_TOTAL) -- --lib relational $(MUTANTS_LIBTEST_ARGS)
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby relational backend mutants shard 4/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard 3/$(MUTANTS_SHARD_TOTAL) -p abide-verify --file crates/abide-verify/src/verify/relational.rs --file crates/abide-verify/src/verify/relation_sat.rs --re '$(WNBY_VERIFY_RELATIONAL_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-relational.4-of-$(MUTANTS_SHARD_TOTAL) -- --lib relational $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-wnby-verify-harness:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby harness transition/action mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard 0/$(MUTANTS_SHARD_TOTAL) -p abide-verify --file crates/abide-verify/src/verify/harness.rs --file crates/abide-verify/src/verify/harness/action.rs --file crates/abide-verify/src/verify/harness/guard.rs --file crates/abide-verify/src/verify/harness/step.rs --file crates/abide-verify/src/verify/harness/step/branching.rs --file crates/abide-verify/src/verify/harness/temporal.rs --re '$(WNBY_VERIFY_HARNESS_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-harness.1-of-$(MUTANTS_SHARD_TOTAL) -- --lib harness $(MUTANTS_LIBTEST_ARGS)
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby harness transition/action mutants shard 2/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard 1/$(MUTANTS_SHARD_TOTAL) -p abide-verify --file crates/abide-verify/src/verify/harness.rs --file crates/abide-verify/src/verify/harness/action.rs --file crates/abide-verify/src/verify/harness/guard.rs --file crates/abide-verify/src/verify/harness/step.rs --file crates/abide-verify/src/verify/harness/step/branching.rs --file crates/abide-verify/src/verify/harness/temporal.rs --re '$(WNBY_VERIFY_HARNESS_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-harness.2-of-$(MUTANTS_SHARD_TOTAL) -- --lib harness $(MUTANTS_LIBTEST_ARGS)
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby harness transition/action mutants shard 3/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard 2/$(MUTANTS_SHARD_TOTAL) -p abide-verify --file crates/abide-verify/src/verify/harness.rs --file crates/abide-verify/src/verify/harness/action.rs --file crates/abide-verify/src/verify/harness/guard.rs --file crates/abide-verify/src/verify/harness/step.rs --file crates/abide-verify/src/verify/harness/step/branching.rs --file crates/abide-verify/src/verify/harness/temporal.rs --re '$(WNBY_VERIFY_HARNESS_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-harness.3-of-$(MUTANTS_SHARD_TOTAL) -- --lib harness $(MUTANTS_LIBTEST_ARGS)
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby harness transition/action mutants shard 4/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard 3/$(MUTANTS_SHARD_TOTAL) -p abide-verify --file crates/abide-verify/src/verify/harness.rs --file crates/abide-verify/src/verify/harness/action.rs --file crates/abide-verify/src/verify/harness/guard.rs --file crates/abide-verify/src/verify/harness/step.rs --file crates/abide-verify/src/verify/harness/step/branching.rs --file crates/abide-verify/src/verify/harness/temporal.rs --re '$(WNBY_VERIFY_HARNESS_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-harness.4-of-$(MUTANTS_SHARD_TOTAL) -- --lib harness $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-wnby-verify-ic3:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby IC3/liveness mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard 0/$(MUTANTS_SHARD_TOTAL) -p abide-verify --file crates/abide-verify/src/verify/ic3/liveness.rs --file crates/abide-verify/src/verify/ic3/system/actions.rs --file crates/abide-verify/src/verify/ic3/multi_slot/expr.rs --file crates/abide-verify/src/verify/ic3/multi_slot/patterns.rs --file crates/abide-verify/src/verify/ic3/system/expr.rs --re '$(WNBY_VERIFY_IC3_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-ic3.1-of-$(MUTANTS_SHARD_TOTAL) -- --lib ic3 $(MUTANTS_LIBTEST_ARGS)
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby IC3/liveness mutants shard 2/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard 1/$(MUTANTS_SHARD_TOTAL) -p abide-verify --file crates/abide-verify/src/verify/ic3/liveness.rs --file crates/abide-verify/src/verify/ic3/system/actions.rs --file crates/abide-verify/src/verify/ic3/multi_slot/expr.rs --file crates/abide-verify/src/verify/ic3/multi_slot/patterns.rs --file crates/abide-verify/src/verify/ic3/system/expr.rs --re '$(WNBY_VERIFY_IC3_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-ic3.2-of-$(MUTANTS_SHARD_TOTAL) -- --lib ic3 $(MUTANTS_LIBTEST_ARGS)
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby IC3/liveness mutants shard 3/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard 2/$(MUTANTS_SHARD_TOTAL) -p abide-verify --file crates/abide-verify/src/verify/ic3/liveness.rs --file crates/abide-verify/src/verify/ic3/system/actions.rs --file crates/abide-verify/src/verify/ic3/multi_slot/expr.rs --file crates/abide-verify/src/verify/ic3/multi_slot/patterns.rs --file crates/abide-verify/src/verify/ic3/system/expr.rs --re '$(WNBY_VERIFY_IC3_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-ic3.3-of-$(MUTANTS_SHARD_TOTAL) -- --lib ic3 $(MUTANTS_LIBTEST_ARGS)
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby IC3/liveness mutants shard 4/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard 3/$(MUTANTS_SHARD_TOTAL) -p abide-verify --file crates/abide-verify/src/verify/ic3/liveness.rs --file crates/abide-verify/src/verify/ic3/system/actions.rs --file crates/abide-verify/src/verify/ic3/multi_slot/expr.rs --file crates/abide-verify/src/verify/ic3/multi_slot/patterns.rs --file crates/abide-verify/src/verify/ic3/system/expr.rs --re '$(WNBY_VERIFY_IC3_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-ic3.4-of-$(MUTANTS_SHARD_TOTAL) -- --lib ic3 $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-wnby-verify-sygus-core:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby SyGuS core/revalidation mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard 0/$(MUTANTS_SHARD_TOTAL) -p abide-verify --file crates/abide-verify/src/verify/sygus.rs --file crates/abide-verify/src/verify/sygus/core.rs --re '$(WNBY_VERIFY_SYGUS_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-sygus-core.1-of-$(MUTANTS_SHARD_TOTAL) -- --lib sygus $(MUTANTS_LIBTEST_ARGS)
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby SyGuS core/revalidation mutants shard 2/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard 1/$(MUTANTS_SHARD_TOTAL) -p abide-verify --file crates/abide-verify/src/verify/sygus.rs --file crates/abide-verify/src/verify/sygus/core.rs --re '$(WNBY_VERIFY_SYGUS_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-sygus-core.2-of-$(MUTANTS_SHARD_TOTAL) -- --lib sygus $(MUTANTS_LIBTEST_ARGS)
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby SyGuS core/revalidation mutants shard 3/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard 2/$(MUTANTS_SHARD_TOTAL) -p abide-verify --file crates/abide-verify/src/verify/sygus.rs --file crates/abide-verify/src/verify/sygus/core.rs --re '$(WNBY_VERIFY_SYGUS_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-sygus-core.3-of-$(MUTANTS_SHARD_TOTAL) -- --lib sygus $(MUTANTS_LIBTEST_ARGS)
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby SyGuS core/revalidation mutants shard 4/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard 3/$(MUTANTS_SHARD_TOTAL) -p abide-verify --file crates/abide-verify/src/verify/sygus.rs --file crates/abide-verify/src/verify/sygus/core.rs --re '$(WNBY_VERIFY_SYGUS_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-sygus-core.4-of-$(MUTANTS_SHARD_TOTAL) -- --lib sygus $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-wnby-verify-temporal-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby temporal/liveness mutants shard $*/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_SHARD_TOTAL)" -p abide-verify --file crates/abide-verify/src/verify/temporal.rs --file crates/abide-verify/src/verify/ltl.rs --re '$(WNBY_VERIFY_TEMPORAL_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-temporal.$*-of-$(MUTANTS_SHARD_TOTAL) -- --lib temporal $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-wnby-verify-theorem-transition-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby theorem/transition mutants shard $*/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_SHARD_TOTAL)" -p abide-verify --file crates/abide-verify/src/verify/theorem.rs --file crates/abide-verify/src/verify/transition.rs --re '$(WNBY_VERIFY_THEOREM_TRANSITION_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-theorem-transition.$*-of-$(MUTANTS_SHARD_TOTAL) -- --lib theorem $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-wnby-verify-relational-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby relational backend mutants shard $*/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_SHARD_TOTAL)" -p abide-verify --file crates/abide-verify/src/verify/relational.rs --file crates/abide-verify/src/verify/relation_sat.rs --re '$(WNBY_VERIFY_RELATIONAL_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-relational.$*-of-$(MUTANTS_SHARD_TOTAL) -- --lib relational $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-wnby-verify-harness-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby harness transition/action mutants shard $*/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_SHARD_TOTAL)" -p abide-verify --file crates/abide-verify/src/verify/harness.rs --file crates/abide-verify/src/verify/harness/action.rs --file crates/abide-verify/src/verify/harness/guard.rs --file crates/abide-verify/src/verify/harness/step.rs --file crates/abide-verify/src/verify/harness/step/branching.rs --file crates/abide-verify/src/verify/harness/temporal.rs --re '$(WNBY_VERIFY_HARNESS_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-harness.$*-of-$(MUTANTS_SHARD_TOTAL) -- --lib harness $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-wnby-verify-ic3-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby IC3/liveness mutants shard $*/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_SHARD_TOTAL)" -p abide-verify --file crates/abide-verify/src/verify/ic3/liveness.rs --file crates/abide-verify/src/verify/ic3/system/actions.rs --file crates/abide-verify/src/verify/ic3/multi_slot/expr.rs --file crates/abide-verify/src/verify/ic3/multi_slot/patterns.rs --file crates/abide-verify/src/verify/ic3/system/expr.rs --re '$(WNBY_VERIFY_IC3_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-ic3.$*-of-$(MUTANTS_SHARD_TOTAL) -- --lib ic3 $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-wnby-verify-sygus-core-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby SyGuS core/revalidation mutants shard $*/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_SHARD_TOTAL)" -p abide-verify --file crates/abide-verify/src/verify/sygus.rs --file crates/abide-verify/src/verify/sygus/core.rs --re '$(WNBY_VERIFY_SYGUS_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-sygus-core.$*-of-$(MUTANTS_SHARD_TOTAL) -- --lib sygus $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-wnby-verify-pure-scene:
	$(MAKE) check-lang-mutants-wnby-verify-pure-scene-context
	$(MAKE) check-lang-mutants-wnby-verify-pure-scene-defenv
	$(MAKE) check-lang-mutants-wnby-verify-pure-scene-encode-ctors
	$(MAKE) check-lang-mutants-wnby-verify-pure-scene-encode-apps
	$(MAKE) check-lang-mutants-wnby-verify-pure-scene-encode-collections
	$(MAKE) check-lang-mutants-wnby-verify-pure-scene-encode-lambda
	$(MAKE) check-lang-mutants-wnby-verify-pure-scene-scene
	$(MAKE) check-lang-mutants-wnby-verify-pure-scene-scope-walkers

check-lang-mutants-wnby-verify-pure-scene-shard-%:
	@echo "The broad pure/scene shard was split after it caused excessive filesystem churn. Use check-lang-mutants-wnby-verify-pure-scene or one of its focused child targets."

check-lang-mutants-wnby-verify-pure-scene-context:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby pure/scene context/default mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) -p abide-verify --file crates/abide-verify/src/verify/context.rs --re '$(WNBY_VERIFY_PURE_SCENE_CONTEXT_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-pure-scene.context -- --lib pure_scene $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-wnby-verify-pure-scene-defenv:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby pure/scene defenv mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) -p abide-verify --file crates/abide-verify/src/verify/defenv.rs --re '$(WNBY_VERIFY_PURE_SCENE_DEFENV_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-pure-scene.defenv -- --lib pure_scene $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-wnby-verify-pure-scene-encode-ctors:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby pure/scene encode constructor mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) -p abide-verify --file crates/abide-verify/src/verify/encode.rs --re '$(WNBY_VERIFY_PURE_SCENE_ENCODE_CTORS_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-pure-scene.encode-ctors -- --lib pure_scene $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-wnby-verify-pure-scene-encode-apps:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby pure/scene encode application mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) -p abide-verify --file crates/abide-verify/src/verify/encode.rs --re '$(WNBY_VERIFY_PURE_SCENE_ENCODE_APPS_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-pure-scene.encode-apps -- --lib pure_scene $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-wnby-verify-pure-scene-encode-collections:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby pure/scene encode collection mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) -p abide-verify --file crates/abide-verify/src/verify/encode.rs --re '$(WNBY_VERIFY_PURE_SCENE_ENCODE_COLLECTIONS_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-pure-scene.encode-collections -- --lib pure_scene $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-wnby-verify-pure-scene-encode-lambda:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby pure/scene encode lambda/refinement mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) -p abide-verify --file crates/abide-verify/src/verify/encode.rs --re '$(WNBY_VERIFY_PURE_SCENE_ENCODE_LAMBDA_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-pure-scene.encode-lambda -- --lib pure_scene $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-wnby-verify-pure-scene-scene:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby pure/scene scene mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) -p abide-verify --file crates/abide-verify/src/verify/scene.rs --re '$(WNBY_VERIFY_PURE_SCENE_SCENE_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-pure-scene.scene -- --lib pure_scene $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-wnby-verify-pure-scene-scope-walkers:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby pure/scene scope/walker mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) -p abide-verify --file crates/abide-verify/src/verify/scope.rs --file crates/abide-verify/src/verify/walkers.rs --re '$(WNBY_VERIFY_PURE_SCENE_SCOPE_WALKERS_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-pure-scene.scope-walkers -- --lib pure_scene $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-wnby-verify-dispatch:
	$(MAKE) check-lang-mutants-wnby-verify-dispatch-reconcile
	$(MAKE) check-lang-mutants-wnby-verify-dispatch-float-backend

check-lang-mutants-wnby-verify-dispatch-reconcile:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby verifier dispatch reconciliation mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) -p abide-verify --file crates/abide-verify/src/verify/mod.rs --re '$(WNBY_VERIFY_DISPATCH_RECONCILE_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-dispatch.reconcile -- --lib solver_result_reconciliation $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-wnby-verify-dispatch-float-backend:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby verifier dispatch float-backend mutants" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) -p abide-verify --file crates/abide-verify/src/verify/mod.rs --re '$(WNBY_VERIFY_DISPATCH_FLOAT_BACKEND_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-dispatch.float-backend -- --lib float_requires_z3_result $(MUTANTS_LIBTEST_ARGS)

check-lang-mutants-wnby-verify-dispatch-broad-shard-%:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(MUTANTS_VERIFY_TIMEOUT_SECS) --label "wnby verifier dispatch/lasso mutants shard $*/$(MUTANTS_SHARD_TOTAL)" -- $(MUTANTS_ENV) $(CARGO_MUTANTS) $(MUTANTS_VERIFY_COMMON_ARGS) --shard "$$(($* - 1))/$(MUTANTS_SHARD_TOTAL)" -p abide-verify --file crates/abide-verify/src/verify/mod.rs --re '$(WNBY_VERIFY_DISPATCH_RE)' --output $(MUTANTS_OUTPUT_DIR)/mutants.out.wnby.verify-dispatch.$*-of-$(MUTANTS_SHARD_TOTAL) -- --lib verify $(MUTANTS_LIBTEST_ARGS)

coverage:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(CARGO_TIMEOUT_SECS) --label "abide coverage" -- $(LLVM_COV) -p abide --lib --tests

coverage-html:
	$(RUN_WITH_TIMEOUT) --timeout-secs $(CARGO_TIMEOUT_SECS) --label "abide html coverage" -- $(LLVM_COV) -p abide --lib --tests --html

check: fmt-check clippy test

check-strict: check test-unbounded

clean:
	$(CARGO) clean
