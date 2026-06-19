set shell := ["zsh", "-cu"]

default:
  @just --list

cargo_timeout := env_var_or_default("ABIDE_CARGO_TIMEOUT_SECS", "3600")
unbounded_verify_tests := "theorem_proved_by_induction theorem_unprovable_when_not_inductive theorem_step_case_does_not_vacuously_prove_under_no_stutter theorem_invariant_preservation_does_not_vacuously_prove_under_no_stutter tiered_unbounded_only_returns_unknown_on_failure ic3_proves_property_induction_cannot no_ic3_flag_skips_ic3_verify_falls_to_bmc unbounded_only_no_ic3_gives_accurate_hint multi_apply_ic3_proves_property verify_all_with_independent_z3_chc_selection_preserves_ic3_proofs verify_all_with_cvc5_chc_selection_is_honest_about_current_chc_limit"
fallback_soundness_verify_tests := "verifier_lowering_code_documents_silent_fallback_patterns pure_encoder_rejects_shared_unsupported_ir_corpus slot_encoder_rejects_shared_unsupported_ir_corpus property_encoder_rejects_shared_unsupported_ir_corpus check_scene_block_rejects_shared_unsupported_ir_corpus scene_precheck_rejects_shared_unsupported_ir_corpus action_precheck_rejects_shared_unsupported_ir_corpus ic3_encoders_reject_shared_unsupported_ir_corpus theorem_and_lemma_reject_shared_unsupported_ir_corpus explicit_state_eval_rejects_shared_unsupported_ir_corpus property_encoder_rejects_future_temporal_fallbacks reachable_division_by_zero_is_flagged verify_all_rejects_bare_expr_stmt_action_body liveness_body_division_is_not_silently_checked transition_update_division_by_zero_is_flagged theorem_reachable_division_by_zero_is_not_proved fn_contract_division_by_zero_is_not_proved"
fallback_soundness_slow_fixture_tests := "fixture_collection_ops_full_smoke fixture_collections_full_smoke fixture_quantifiers_full_smoke fixture_until_full_smoke fixture_lambdas_full_smoke fixture_refinements_full_smoke"
fallback_soundness_example_tests := "public_examples_cover_remaining_audit_constructs public_example_verify_blocks_run_with_bounded_targets public_intentional_failure_examples_report_expected_outcomes"
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
mutants_verify_timeout := env_var_or_default("ABIDE_MUTANTS_VERIFY_TIMEOUT_SECS", "1800")
mutants_verify_per_test_timeout := env_var_or_default("ABIDE_MUTANTS_VERIFY_PER_TEST_TIMEOUT_SECS", "75")
mutants_verify_build_timeout := env_var_or_default("ABIDE_MUTANTS_VERIFY_BUILD_TIMEOUT_SECS", "900")
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
mutants_verify_common_args := "--profile " + mutants_profile + " --timeout " + mutants_verify_per_test_timeout + " --build-timeout " + mutants_verify_build_timeout + " --in-place --baseline skip"
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
sema_resolution_expr_expected_re := "resolve_if_else_with_expected_type|resolve_var_decl_expr|resolve_set_literal_expr|resolve_seq_literal_expr|resolve_map_literal_expr|resolve_collection_literal_with_expected_type|resolve_expr_with_expected_type"
sema_resolution_expr_constructor_re := "expected_constructor_call|expected_enum_constructor_name|expected_constructor_payload_types|expected_generic_constructor_payload_types|resolve_comparison_ctor_from_context|enum_scope_matches|enum_name_without_args|resolve_var_type|resolve_ctor_type_from_context|patch_constructor_callee|can_patch_constructor_ty|find_constructor_type"
sema_collection_expr_re := "collect_qualified_call|quant_guard_body|collect_set_comp_binder|collect_call_expr|collect_quantifier_expr|collect_aggregate_expr|collect_let_expr|collect_lambda_expr|collect_match_expr|collect_set_comp_expr|collect_rel_comp_expr|collect_saw_expr|collect_control_expr|collect_expr"
sema_validation_context_re := "walk_expr|walk_contract|walk_field_default|walk_event_action|walk_scene_when|walk_env_exprs|validate_saw_expressions|validate_aggregate_bodies|validate_set_comprehension_sources|validate_set_comprehension_expr|validate_set_comprehension_event_action|validate_set_comprehension_field_default"
verifier_expr_property_quantifier_re := "property_quantifier_parts|encode_prop_quantifier_expr|encode_entity_quantifier_expr|encode_finite_enum_quantifier_expr|combine_finite_quantifier_predicates|encode_native_quantifier_expr|narrow_entity_quantifier_slots|extract_store_scoped_quantifier_body"
verifier_expr_property_constructor_re := "encode_prop_constructor_field_or_call_value|encode_prop_payload_field_value|encode_static_payload_field_value|payload_accessor_for_field|ctor_name_matches_for_payload_accessor|encode_prop_field_value|encode_prop_ctor_value|encode_prop_adt_ctor_value"
verifier_expr_slot_re := "try_encode_slot_expr|try_encode_slot_literal_expr|try_encode_slot_var_or_field_expr|try_encode_slot_field_expr|try_encode_slot_constructor_expr|try_encode_slot_constructor|try_encode_slot_choose_expr|try_encode_slot_operator_expr|try_encode_slot_binop_expr|try_encode_slot_unop_expr|try_encode_slot_app_expr|try_encode_slot_app|try_encode_slot_collection_expr|try_encode_slot_map_update_expr|try_encode_slot_index_expr|try_encode_slot_map_lit_expr|try_encode_slot_set_lit_expr|try_encode_slot_seq_lit_expr|try_encode_slot_finite_set_comp_expr|try_encode_slot_card_expr|try_encode_slot_sourced_set_comp_card|try_encode_slot_finite_set_comp_card|try_encode_slot_control_expr|try_encode_slot_store_quantifier"
verifier_expr_slot_shard_1_re := "try_encode_slot_expr|try_encode_slot_literal_expr|try_encode_slot_var_or_field_expr|try_encode_slot_field_expr"
verifier_expr_slot_shard_2_re := "try_encode_slot_constructor_expr|try_encode_slot_constructor|try_encode_slot_choose_expr|try_encode_slot_operator_expr|try_encode_slot_binop_expr|try_encode_slot_unop_expr"
verifier_expr_slot_shard_3_re := "try_encode_slot_app_expr|try_encode_slot_app|try_encode_slot_collection_expr|try_encode_slot_map_update_expr|try_encode_slot_index_expr|try_encode_slot_map_lit_expr|try_encode_slot_set_lit_expr|try_encode_slot_seq_lit_expr"
verifier_expr_slot_shard_4_re := "try_encode_slot_finite_set_comp_expr|try_encode_slot_card_expr|try_encode_slot_sourced_set_comp_card|try_encode_slot_finite_set_comp_card|try_encode_slot_control_expr|try_encode_slot_store_quantifier"
verifier_expr_collection_re := "encode_set_literal|encode_seq_literal|encode_map_literal|encode_collection_index|encode_collection_update|finite_literal_cardinality|encode_unique_projected_cardinality|int_sum_or_zero|unique_expr_count"
verifier_expr_pooled_support_re := "diagnose_pooled_sygus_expr_support|diagnose_pooled_sygus_expr_support_inner|unsupported_expr|is_pooled_sygus_finite_scalar_domain|ensure_pooled_sygus_expr_supported|ensure_pooled_sygus_action_supported|ensure_pooled_sygus_actions_supported|ensure_pooled_sygus_system_supported"
wnby_syntax_lex_re := "classify_lex_error"
wnby_simulate_re := "real_operand|float_operand|float_witness|try_float_binop|real_witness|try_real_binop|eval_binop|witness_values_equal|eval_unop|sim_int_op|real_witness_value|float_witness_value|normalize_float"
wnby_verify_literal_re := "string_literal_id"
wnby_verify_support_re := "classify_expr_support|classify_action_support|classify_quantifier|is_finite_domain|statement_like_expr_cases|property_position_unsupported_cases|unsupported_expr_cases"
wnby_verify_explicit_re := "supports_state_expr|pattern_matches|fieldless_enum_variant_value|fieldless_enum_variant_value_for_type|eval_expr|eval_expr_with_store_ranges|eval_cardinality_expr|eval_quantifier|explicit_store_scoped_quantifier_body|eval_choose|eval_bool_with_store_ranges|eval_binop|eval_eq|eval_neq|eval_int_comparison|compare_reals|explicit_int_op|eval_unop|finite_values_for_type|witness_value"
wnby_verify_float_route_re := "program_uses_float|ty_uses_float|expr_uses_float|action_uses_float|scrutinee_uses_float|function_uses_float|entity_uses_float|field_uses_float|system_uses_float|verify_uses_float|theorem_uses_float|scene_uses_float"
wnby_verify_temporal_re := "compile_buchi_formula|lower_to_buchi_formula|lower_to_temporal_formula|buchi_atom_for|render_spot_formula|extract_liveness_pattern_inner|strip_liveness_from_conjunction|extract_liveness_pattern_with_always|action_contains_integer_div|render_hoa_acceptance_condition|local_consistency_holds|transition_consistency_holds|initial_past_consistency_holds|formula_present|formula_id_present"
wnby_verify_theorem_transition_re := "encode_pure_property_expr|needs_property_encoder|theorem_reachable_div_by_zero|theorem_scope|theorem_store_decls|theorem_with_scope_invariants|validate_theorem_temporal_forms|handle_theorem_liveness|validate_theorem_supported_forms|validate_theorem_transition_forms|run_theorem_induction|prove_invariant_base|prove_invariant_step|assert_domain_and_lemmas|assert_transition_step|try_ic3_on_theorem|simplify_static_bool_fragments|try_extern_assume_expr_constraints|solve_transition_obligation"
wnby_verify_relational_re := "build_initial_store_instances|build_stateful_scene_sat|relational_stateful_scene_spec|create_spec|add_cardinality_constraint|relational_verify_spec|build_default_field_map|finite_field_domains|finite_type_values|encode_verify_violation_into|encode_verify_snapshot_into|relation_state_index|build_relational_verify_counterexample_witness|const_lit|and_lit|or_lit|at_most_one_lit|exactly_one_lit|classify_static_relation_solver_result|check_static_relation_assertions|encode_static_relation_assertion|lower_static_relation_expr|relation_type_from_ir_type|solve_static_relation|contains_relation_surface"
wnby_verify_harness_re := "expr_type|create_slot_pool|domain_constraints|initial_state_constraints_with_store_ranges|initial_active_slots_with_store_ranges|try_entity_field_initial_constraints|try_encode_field_default_expr|store_active_cardinality_constraints|try_encode_action|try_encode_action_with_vars|eval_expr_with_vars|build_apply_params|try_build_apply_params|wire_apply_refs|try_encode_guard_inner|try_encode_guard_value|try_encode_step|try_encode_step_with_params|transition_constraints|try_transition_constraints|transition_constraints_with_fire|try_transition_constraints_with_fire|try_encode_step_enabled|try_encode_step_enabled_with_params|try_encode_enabled_cross_call_branches|apply_enabled_match|enabled_match_scrutinee_branches|enabled_match_arm_condition|encode_legacy_choose|register_legacy_choose_params|encode_legacy_forall|collect_modified_entities|legacy_chain_apply_params|encode_legacy_chain_apply|legacy_inactive_slot_frame|merged_branch_params"
wnby_verify_ic3_re := "try_ic3_liveness|encode_liveness_event_chc|action_mutates_state|encode_step_chc_scoped|encode_ops_chc_scoped|top_level_action_guards|encode_macro_call_chc|encode_action_match_scrutinee|encode_macro_return_expr|encode_action_guard_with_locals|encode_non_entity_guard_with_locals|encode_create_chc|ic3_lookup_ctor_variant"
wnby_verify_sygus_re := "cvc5_sygus_enabled|cvc5_sygus_disabled_reason|type_uses_real|try_cvc5_sygus_single_entity|try_cvc5_sygus_system_safety|require_obligation_unsat|collect_system_action_updates|collect_system_exprstmt_update|collect_system_action_sequence_updates|merge_system_match_update_maps|collect_system_match_updates|encode_finite_aggregate_expr|encode_finite_map_key_membership_expr|encode_finite_source_membership|encode_finite_set_membership_term|default_term_for_type|encode_finite_map_lookup_expr_inner|ctor_name_matches|bind_static_payload_pattern_vars|encode_static_payload_pattern_cond"
wnby_verify_pure_scene_context_re := "register_enum_type|collect_program_enum_types|collect_enum_types_from_expr|default_expr_to_string|default_match_arm_to_string|default_pattern_to_string"
wnby_verify_pure_scene_defenv_re := "rewrite_self_field_refs|decompose_app_chain_public|classify_app_chain_public|substitute_var|free_vars_inner|subst_match|subst_rel_comp|subst_quantifier"
wnby_verify_pure_scene_encode_ctors_re := "encode_pure_ctor|encode_adt_ctor|validate_ctor_fields"
wnby_verify_pure_scene_encode_apps_re := "encode_pure_app|verify_call_preconditions|check_fn_div_well_defined|encode_recursive_app|encode_func_application"
wnby_verify_pure_scene_encode_collections_re := "encode_pure_card|encode_pure_set_comp|encode_set_comp_source_pred|combine_set_comp_restrictions|encode_projected_set_comp"
wnby_verify_pure_scene_encode_lambda_re := "encode_lambda|encode_partial_application|unique_theorem_store_name|field_refinement_obligation|expr_quantifies_over_entity"
wnby_verify_pure_scene_scene_re := "scene_solver_result|direct_choose_equality_witness|encode_scene_direct_choose_arg|scene_pass_evidence|assert_scene_then_assertions|is_supported_finite_setcomp_source|is_finite_scene_cardinality_target|extract_command_params|extract_transition_from_fire|analyze_event_fairness|diagnose_disabled_event"
wnby_verify_pure_scene_scope_walkers_re := "expr_quantifies_over_entity|is_supported_finite_setcomp_source|is_finite_scene_cardinality_target"
wnby_verify_dispatch_re := "verify_all|verify_all_with_events|verify_all_on_worker|verify_all_inner|verify_all_single|verify_all_single_impl|reconcile_solver_results|float_requires_z3_result|catch_verification_panic|record_verify_assert_precondition_obligations|check_verify_block_tiered|try_cvc5_sygus_on_verify|try_induction_on_verify|prove_induction_base|prove_induction_step|liveness_reduction_applicable|prove_liveness_by_monitor_induction|revalidate_sygus_invariant_via_z3|revalidate_pooled_sygus_invariant_via_z3|prove_liveness_by_ic3|try_ic3_on_verify|try_ic3_on_verify_with_diagnostics|check_verify_block_with_depth_search|check_div_by_zero_reachable|validate_bmc_inputs|bmc_transition_encoding|check_verify_block_lasso|check_lasso_asserts|encode_buchi_lasso_violation|expand_expr_node|expand_basic_expr_node"
wnby_verify_dispatch_reconcile_re := "reconcile_solver_results|result_signature|result_name|solver_label"
wnby_verify_dispatch_float_backend_re := "float_requires_z3_result|unavailable_solver_result"
wnby_ir_types_re := "simple|base_without_refinement|as_str|is_assignment|try_from|fmt"
wnby_sema_collect_types_re := "collect_entity|collect_field|collect_action|collect_assignment|elaborate_store_param|check_system_action_fsm_violations|collect_system_prime_assignments|collect_system_prime_assignments_inner|collect_match_scrutinee|collect_match_arm|base_without_refinement|domain|fmt"

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
  {{runner}} --timeout-secs {{cargo_timeout}} --label "abide-verify unbounded proof tests" -- env RUSTC_WRAPPER=sccache ABIDE_RUN_UNBOUNDED_PROOF_TESTS=1 cargo nextest run -p abide-verify --lib {{unbounded_verify_tests}} --run-ignored only
  {{runner}} --timeout-secs {{cargo_timeout}} --label "abide integration unbounded proof tests" -- env RUSTC_WRAPPER=sccache ABIDE_RUN_UNBOUNDED_PROOF_TESTS=1 ABIDE_ENABLE_INPROCESS_CVC5_SYGUS=1 cargo nextest run -p abide --test integration cvc5_sygus --run-ignored only

test-fallback-soundness:
  {{runner}} --timeout-secs {{cargo_timeout}} --label "abide-verify fallback-soundness corpus" -- env RUSTC_WRAPPER=sccache cargo nextest run -p abide-verify {{fallback_soundness_verify_tests}}
  {{runner}} --timeout-secs {{cargo_timeout}} --label "abide-verify fallback-soundness full gate" -- env RUSTC_WRAPPER=sccache cargo nextest run -p abide-verify --lib fallback_soundness_full_gate --run-ignored only
  {{runner}} --timeout-secs {{cargo_timeout}} --label "abide-verify fallback-soundness slow fixture shards" -- env RUSTC_WRAPPER=sccache cargo nextest run -p abide-verify --lib {{fallback_soundness_slow_fixture_tests}} --run-ignored only
  {{runner}} --timeout-secs {{cargo_timeout}} --label "abide public example fallback-soundness corpus" -- env RUSTC_WRAPPER=sccache cargo nextest run -p abide --test integration {{fallback_soundness_example_tests}}

check-ignored-tests:
  {{runner}} --timeout-secs {{cargo_timeout}} --label "ignored test inventory check" -- env RUSTC_WRAPPER=sccache python3 tools/ignored_tests_inventory.py check

update-ignored-tests:
  {{runner}} --timeout-secs {{cargo_timeout}} --label "ignored test inventory update" -- env RUSTC_WRAPPER=sccache python3 tools/ignored_tests_inventory.py update

check-lang-mutants-core:
  just check-lang-mutants-core-baseline
  just check-lang-mutants-core-arith
  just check-lang-mutants-core-real
  just check-lang-mutants-core-diagnostics
  just check-lang-mutants-core-support

check-lang-mutants-core-baseline:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-core baseline tests" -- {{mutants_env}} cargo test -p abide-core --lib {{mutants_libtest_args}}

check-lang-mutants-core-arith:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-core integer/real literal arithmetic mutants" -- {{mutants_env}} cargo mutants {{mutants_common_args}} -p abide-core --file crates/abide-core/src/arith.rs --output {{mutants_output_dir}}/mutants.out.core-arith -- --lib arith {{mutants_libtest_args}}

check-lang-mutants-core-real:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-core exact rational real mutants" -- {{mutants_env}} cargo mutants {{mutants_common_args}} -p abide-core --file crates/abide-core/src/real.rs --output {{mutants_output_dir}}/mutants.out.core-real -- --lib real {{mutants_libtest_args}}

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

check-lang-mutants-sema-expr-helpers:
  just check-lang-mutants-sema-resolution-expr-expected
  just check-lang-mutants-sema-resolution-expr-constructor
  just check-lang-mutants-sema-collection-expr
  just check-lang-mutants-sema-validation-context

check-lang-mutants-sema-resolution-expr-expected:
  just check-lang-mutants-sema-resolution-expr-expected-shard 1
  just check-lang-mutants-sema-resolution-expr-expected-shard 2
  just check-lang-mutants-sema-resolution-expr-expected-shard 3
  just check-lang-mutants-sema-resolution-expr-expected-shard 4

check-lang-mutants-sema-resolution-expr-expected-shard shard:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-sema expected expression type mutants shard {{shard}}/{{mutants_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_common_args}} --shard "$(({{shard}} - 1))/{{mutants_shard_total}}" -p abide-sema --file crates/abide-sema/src/elab/resolve/expr.rs --re '{{sema_resolution_expr_expected_re}}' --output {{mutants_output_dir}}/mutants.out.sema-resolution-expr-expected.{{shard}}-of-{{mutants_shard_total}} -- --lib resolve {{mutants_libtest_args}}

check-lang-mutants-sema-resolution-expr-constructor:
  just check-lang-mutants-sema-resolution-expr-constructor-shard 1
  just check-lang-mutants-sema-resolution-expr-constructor-shard 2
  just check-lang-mutants-sema-resolution-expr-constructor-shard 3
  just check-lang-mutants-sema-resolution-expr-constructor-shard 4

check-lang-mutants-sema-resolution-expr-constructor-shard shard:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-sema constructor resolution mutants shard {{shard}}/{{mutants_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_common_args}} --shard "$(({{shard}} - 1))/{{mutants_shard_total}}" -p abide-sema --file crates/abide-sema/src/elab/resolve/constructor.rs --re '{{sema_resolution_expr_constructor_re}}' --output {{mutants_output_dir}}/mutants.out.sema-resolution-expr-constructor.{{shard}}-of-{{mutants_shard_total}} -- --lib constructor {{mutants_libtest_args}}

check-lang-mutants-sema-collection-expr:
  just check-lang-mutants-sema-collection-expr-shard 1
  just check-lang-mutants-sema-collection-expr-shard 2
  just check-lang-mutants-sema-collection-expr-shard 3
  just check-lang-mutants-sema-collection-expr-shard 4

check-lang-mutants-sema-collection-expr-shard shard:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-sema expression collection mutants shard {{shard}}/{{mutants_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_common_args}} --shard "$(({{shard}} - 1))/{{mutants_shard_total}}" -p abide-sema --file crates/abide-sema/src/elab/collect/expr.rs --re '{{sema_collection_expr_re}}' --output {{mutants_output_dir}}/mutants.out.sema-collection-expr.{{shard}}-of-{{mutants_shard_total}} -- --lib collect {{mutants_libtest_args}}

check-lang-mutants-sema-validation-context:
  just check-lang-mutants-sema-validation-context-shard 1
  just check-lang-mutants-sema-validation-context-shard 2
  just check-lang-mutants-sema-validation-context-shard 3
  just check-lang-mutants-sema-validation-context-shard 4

check-lang-mutants-sema-validation-context-shard shard:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "abide-sema expression validation context mutants shard {{shard}}/{{mutants_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_common_args}} --shard "$(({{shard}} - 1))/{{mutants_shard_total}}" -p abide-sema --file crates/abide-sema/src/elab/resolve/validate.rs --re '{{sema_validation_context_re}}' --output {{mutants_output_dir}}/mutants.out.sema-validation-context.{{shard}}-of-{{mutants_shard_total}} -- --lib validate {{mutants_libtest_args}}

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
  just check-lang-mutants-fn-vc-shard 1
  just check-lang-mutants-fn-vc-shard 2
  just check-lang-mutants-fn-vc-shard 3
  just check-lang-mutants-fn-vc-shard 4

check-lang-mutants-fn-vc-shard shard:
  {{runner}} --timeout-secs {{mutants_verify_timeout}} --label "abide-verify function VC mutants shard {{shard}}/{{mutants_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_verify_common_args}} --shard "$(({{shard}} - 1))/{{mutants_shard_total}}" -p abide-verify --file crates/abide-verify/src/verify/fn_verify.rs --output {{mutants_output_dir}}/mutants.out.fn-vc.{{shard}}-of-{{mutants_shard_total}} -- --lib fn_contract {{mutants_libtest_args}}

check-lang-mutants-smt-facade:
  just check-lang-mutants-smt-facade-shard 1
  just check-lang-mutants-smt-facade-shard 2
  just check-lang-mutants-smt-facade-shard 3
  just check-lang-mutants-smt-facade-shard 4

check-lang-mutants-smt-facade-shard shard:
  {{runner}} --timeout-secs {{mutants_verify_timeout}} --label "abide-verify SMT facade mutants shard {{shard}}/{{mutants_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_verify_common_args}} --shard "$(({{shard}} - 1))/{{mutants_shard_total}}" -p abide-verify --file crates/abide-verify/src/verify/smt.rs --output {{mutants_output_dir}}/mutants.out.smt-facade.{{shard}}-of-{{mutants_shard_total}} -- --lib smt {{mutants_libtest_args}}

check-lang-mutants-solver-routing:
  just check-lang-mutants-solver-routing-shard 1
  just check-lang-mutants-solver-routing-shard 2
  just check-lang-mutants-solver-routing-shard 3
  just check-lang-mutants-solver-routing-shard 4

check-lang-mutants-solver-routing-shard shard:
  {{runner}} --timeout-secs {{mutants_verify_timeout}} --label "abide-verify solver routing mutants shard {{shard}}/{{mutants_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_verify_common_args}} --shard "$(({{shard}} - 1))/{{mutants_shard_total}}" -p abide-verify --file crates/abide-verify/src/verify/solver.rs --re 'SolverCapabilities|backend_score|set_active_solver_family|is_solver_family_available|AbideSolver|z3_check_chc' --output {{mutants_output_dir}}/mutants.out.solver-routing.{{shard}}-of-{{mutants_shard_total}} -- --lib solver {{mutants_libtest_args}}

check-lang-mutants-runtime-backend:
  just check-lang-mutants-runtime-backend-shard 1
  just check-lang-mutants-runtime-backend-shard 2
  just check-lang-mutants-runtime-backend-shard 3
  just check-lang-mutants-runtime-backend-shard 4

check-lang-mutants-runtime-backend-shard shard:
  {{runner}} --timeout-secs {{mutants_verify_timeout}} --label "abide-verify runtime backend mutants shard {{shard}}/{{mutants_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_verify_common_args}} --shard "$(({{shard}} - 1))/{{mutants_shard_total}}" -p abide-verify --file crates/abide-verify/src/verify/solver.rs --re 'RuntimeBackend|RuntimeModel|RuntimeDynamic|RuntimeBool|RuntimeReal|RuntimeArray|RuntimeModelEval' --output {{mutants_output_dir}}/mutants.out.runtime-backend.{{shard}}-of-{{mutants_shard_total}} -- --lib solver {{mutants_libtest_args}}

check-lang-mutants-verify: check-lang-mutants-fn-vc check-lang-mutants-smt-facade check-lang-mutants-solver-routing check-lang-mutants-runtime-backend check-lang-mutants-verifier-expr

check-lang-mutants-wnby: check-lang-mutants-core check-lang-mutants-syntax-parser check-lang-mutants-sema-expr-helpers check-lang-mutants-sema-checker check-lang-mutants-ir-lowering check-lang-mutants-fn-vc check-lang-mutants-smt-facade check-lang-mutants-solver-routing check-lang-mutants-runtime-backend check-lang-mutants-verifier-expr check-lang-mutants-wnby-ir-types check-lang-mutants-wnby-sema-collect-types check-lang-mutants-wnby-syntax-lex check-lang-mutants-wnby-simulate check-lang-mutants-wnby-verify-literal check-lang-mutants-wnby-verify-support check-lang-mutants-wnby-verify-explicit check-lang-mutants-wnby-verify-float-route check-lang-mutants-wnby-verify-temporal check-lang-mutants-wnby-verify-theorem-transition check-lang-mutants-wnby-verify-relational check-lang-mutants-wnby-verify-harness check-lang-mutants-wnby-verify-ic3 check-lang-mutants-wnby-verify-sygus-core check-lang-mutants-wnby-verify-pure-scene check-lang-mutants-wnby-verify-dispatch

check-lang-mutants-wnby-ir-types:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "wnby IR typed-operator/type helper mutants" -- {{mutants_env}} cargo mutants {{mutants_common_args}} -p abide-ir --file crates/abide-ir/src/ir/types.rs --re '{{wnby_ir_types_re}}' --output {{mutants_output_dir}}/mutants.out.wnby.ir-types -- --lib types {{mutants_libtest_args}}

check-lang-mutants-wnby-sema-collect-types:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "wnby sema collection/type helper mutants" -- {{mutants_env}} cargo mutants {{mutants_common_args}} -p abide-sema --file crates/abide-sema/src/elab/collect/entity.rs --file crates/abide-sema/src/elab/collect/system.rs --file crates/abide-sema/src/elab/types.rs --re '{{wnby_sema_collect_types_re}}' --output {{mutants_output_dir}}/mutants.out.wnby.sema-collect-types -- --lib collect {{mutants_libtest_args}}

check-lang-mutants-wnby-syntax-lex:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "wnby lexer overflow/diagnostic mutants" -- {{mutants_env}} cargo mutants {{mutants_common_args}} -p abide-syntax --file crates/abide-syntax/src/lex.rs --re '{{wnby_syntax_lex_re}}' --output {{mutants_output_dir}}/mutants.out.wnby.syntax-lex -- --lib lex {{mutants_libtest_args}}

check-lang-mutants-wnby-simulate:
  just check-lang-mutants-wnby-simulate-shard 1
  just check-lang-mutants-wnby-simulate-shard 2
  just check-lang-mutants-wnby-simulate-shard 3
  just check-lang-mutants-wnby-simulate-shard 4

check-lang-mutants-wnby-simulate-shard shard:
  {{runner}} --timeout-secs {{mutants_timeout}} --label "wnby simulator concrete-semantics mutants shard {{shard}}/{{mutants_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_common_args}} --shard "$(({{shard}} - 1))/{{mutants_shard_total}}" -p abide --file crates/abide/src/simulate.rs --re '{{wnby_simulate_re}}' --output {{mutants_output_dir}}/mutants.out.wnby.simulate.{{shard}}-of-{{mutants_shard_total}} -- --lib simulate {{mutants_libtest_args}}

check-lang-mutants-wnby-verify-literal:
  {{runner}} --timeout-secs {{mutants_verify_timeout}} --label "wnby verifier literal/string mutants" -- {{mutants_env}} cargo mutants {{mutants_verify_common_args}} -p abide-verify --file crates/abide-verify/src/verify/literal.rs --re '{{wnby_verify_literal_re}}' --output {{mutants_output_dir}}/mutants.out.wnby.verify-literal -- --lib literal {{mutants_libtest_args}}

check-lang-mutants-wnby-verify-support:
  {{runner}} --timeout-secs {{mutants_verify_timeout}} --label "wnby verifier support/corpus mutants" -- {{mutants_env}} cargo mutants {{mutants_verify_common_args}} -p abide-verify --file crates/abide-verify/src/verify/support.rs --file crates/abide-verify/src/verify/unsupported_corpus.rs --re '{{wnby_verify_support_re}}' --output {{mutants_output_dir}}/mutants.out.wnby.verify-support -- --lib support {{mutants_libtest_args}}

check-lang-mutants-wnby-verify-explicit:
  {{runner}} --timeout-secs {{mutants_verify_timeout}} --label "wnby explicit-state evaluator mutants" -- {{mutants_env}} cargo mutants {{mutants_verify_common_args}} -p abide-verify --file crates/abide-verify/src/verify/explicit.rs --re '{{wnby_verify_explicit_re}}' --output {{mutants_output_dir}}/mutants.out.wnby.verify-explicit -- --lib explicit {{mutants_libtest_args}}

check-lang-mutants-wnby-verify-float-route:
  {{runner}} --timeout-secs {{mutants_verify_timeout}} --label "wnby verifier float-routing mutants" -- {{mutants_env}} cargo mutants {{mutants_verify_common_args}} -p abide-verify --file crates/abide-verify/src/verify/float_route.rs --re '{{wnby_verify_float_route_re}}' --output {{mutants_output_dir}}/mutants.out.wnby.verify-float-route -- --lib float_route {{mutants_libtest_args}}

check-lang-mutants-wnby-verify-temporal:
  just check-lang-mutants-wnby-verify-temporal-shard 1
  just check-lang-mutants-wnby-verify-temporal-shard 2
  just check-lang-mutants-wnby-verify-temporal-shard 3
  just check-lang-mutants-wnby-verify-temporal-shard 4

check-lang-mutants-wnby-verify-temporal-shard shard:
  {{runner}} --timeout-secs {{mutants_verify_timeout}} --label "wnby temporal/liveness mutants shard {{shard}}/{{mutants_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_verify_common_args}} --shard "$(({{shard}} - 1))/{{mutants_shard_total}}" -p abide-verify --file crates/abide-verify/src/verify/temporal.rs --file crates/abide-verify/src/verify/ltl.rs --re '{{wnby_verify_temporal_re}}' --output {{mutants_output_dir}}/mutants.out.wnby.verify-temporal.{{shard}}-of-{{mutants_shard_total}} -- --lib temporal {{mutants_libtest_args}}

check-lang-mutants-wnby-verify-theorem-transition:
  just check-lang-mutants-wnby-verify-theorem-transition-shard 1
  just check-lang-mutants-wnby-verify-theorem-transition-shard 2
  just check-lang-mutants-wnby-verify-theorem-transition-shard 3
  just check-lang-mutants-wnby-verify-theorem-transition-shard 4

check-lang-mutants-wnby-verify-theorem-transition-shard shard:
  {{runner}} --timeout-secs {{mutants_verify_timeout}} --label "wnby theorem/transition mutants shard {{shard}}/{{mutants_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_verify_common_args}} --shard "$(({{shard}} - 1))/{{mutants_shard_total}}" -p abide-verify --file crates/abide-verify/src/verify/theorem.rs --file crates/abide-verify/src/verify/transition.rs --re '{{wnby_verify_theorem_transition_re}}' --output {{mutants_output_dir}}/mutants.out.wnby.verify-theorem-transition.{{shard}}-of-{{mutants_shard_total}} -- --lib theorem {{mutants_libtest_args}}

check-lang-mutants-wnby-verify-relational:
  just check-lang-mutants-wnby-verify-relational-shard 1
  just check-lang-mutants-wnby-verify-relational-shard 2
  just check-lang-mutants-wnby-verify-relational-shard 3
  just check-lang-mutants-wnby-verify-relational-shard 4

check-lang-mutants-wnby-verify-relational-shard shard:
  {{runner}} --timeout-secs {{mutants_verify_timeout}} --label "wnby relational backend mutants shard {{shard}}/{{mutants_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_verify_common_args}} --shard "$(({{shard}} - 1))/{{mutants_shard_total}}" -p abide-verify --file crates/abide-verify/src/verify/relational.rs --file crates/abide-verify/src/verify/relation_sat.rs --re '{{wnby_verify_relational_re}}' --output {{mutants_output_dir}}/mutants.out.wnby.verify-relational.{{shard}}-of-{{mutants_shard_total}} -- --lib relational {{mutants_libtest_args}}

check-lang-mutants-wnby-verify-harness:
  just check-lang-mutants-wnby-verify-harness-shard 1
  just check-lang-mutants-wnby-verify-harness-shard 2
  just check-lang-mutants-wnby-verify-harness-shard 3
  just check-lang-mutants-wnby-verify-harness-shard 4

check-lang-mutants-wnby-verify-harness-shard shard:
  {{runner}} --timeout-secs {{mutants_verify_timeout}} --label "wnby harness transition/action mutants shard {{shard}}/{{mutants_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_verify_common_args}} --shard "$(({{shard}} - 1))/{{mutants_shard_total}}" -p abide-verify --file crates/abide-verify/src/verify/harness.rs --file crates/abide-verify/src/verify/harness/action.rs --file crates/abide-verify/src/verify/harness/guard.rs --file crates/abide-verify/src/verify/harness/step.rs --file crates/abide-verify/src/verify/harness/step/branching.rs --file crates/abide-verify/src/verify/harness/temporal.rs --re '{{wnby_verify_harness_re}}' --output {{mutants_output_dir}}/mutants.out.wnby.verify-harness.{{shard}}-of-{{mutants_shard_total}} -- --lib harness {{mutants_libtest_args}}

check-lang-mutants-wnby-verify-ic3:
  just check-lang-mutants-wnby-verify-ic3-shard 1
  just check-lang-mutants-wnby-verify-ic3-shard 2
  just check-lang-mutants-wnby-verify-ic3-shard 3
  just check-lang-mutants-wnby-verify-ic3-shard 4

check-lang-mutants-wnby-verify-ic3-shard shard:
  {{runner}} --timeout-secs {{mutants_verify_timeout}} --label "wnby IC3/liveness mutants shard {{shard}}/{{mutants_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_verify_common_args}} --shard "$(({{shard}} - 1))/{{mutants_shard_total}}" -p abide-verify --file crates/abide-verify/src/verify/ic3/liveness.rs --file crates/abide-verify/src/verify/ic3/system/actions.rs --file crates/abide-verify/src/verify/ic3/multi_slot/expr.rs --file crates/abide-verify/src/verify/ic3/multi_slot/patterns.rs --file crates/abide-verify/src/verify/ic3/system/expr.rs --re '{{wnby_verify_ic3_re}}' --output {{mutants_output_dir}}/mutants.out.wnby.verify-ic3.{{shard}}-of-{{mutants_shard_total}} -- --lib ic3 {{mutants_libtest_args}}

check-lang-mutants-wnby-verify-sygus-core:
  just check-lang-mutants-wnby-verify-sygus-core-shard 1
  just check-lang-mutants-wnby-verify-sygus-core-shard 2
  just check-lang-mutants-wnby-verify-sygus-core-shard 3
  just check-lang-mutants-wnby-verify-sygus-core-shard 4

check-lang-mutants-wnby-verify-sygus-core-shard shard:
  {{runner}} --timeout-secs {{mutants_verify_timeout}} --label "wnby SyGuS core/revalidation mutants shard {{shard}}/{{mutants_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_verify_common_args}} --shard "$(({{shard}} - 1))/{{mutants_shard_total}}" -p abide-verify --file crates/abide-verify/src/verify/sygus.rs --file crates/abide-verify/src/verify/sygus/core.rs --re '{{wnby_verify_sygus_re}}' --output {{mutants_output_dir}}/mutants.out.wnby.verify-sygus-core.{{shard}}-of-{{mutants_shard_total}} -- --lib sygus {{mutants_libtest_args}}

check-lang-mutants-wnby-verify-pure-scene:
  just check-lang-mutants-wnby-verify-pure-scene-context
  just check-lang-mutants-wnby-verify-pure-scene-defenv
  just check-lang-mutants-wnby-verify-pure-scene-encode-ctors
  just check-lang-mutants-wnby-verify-pure-scene-encode-apps
  just check-lang-mutants-wnby-verify-pure-scene-encode-collections
  just check-lang-mutants-wnby-verify-pure-scene-encode-lambda
  just check-lang-mutants-wnby-verify-pure-scene-scene
  just check-lang-mutants-wnby-verify-pure-scene-scope-walkers

check-lang-mutants-wnby-verify-pure-scene-shard shard:
  @echo "The broad pure/scene shard was split after it caused excessive filesystem churn. Use check-lang-mutants-wnby-verify-pure-scene or one of its focused child targets."

check-lang-mutants-wnby-verify-pure-scene-context:
  {{runner}} --timeout-secs {{mutants_verify_timeout}} --label "wnby pure/scene context/default mutants" -- {{mutants_env}} cargo mutants {{mutants_verify_common_args}} -p abide-verify --file crates/abide-verify/src/verify/context.rs --re '{{wnby_verify_pure_scene_context_re}}' --output {{mutants_output_dir}}/mutants.out.wnby.verify-pure-scene.context -- --lib pure_scene {{mutants_libtest_args}}

check-lang-mutants-wnby-verify-pure-scene-defenv:
  {{runner}} --timeout-secs {{mutants_verify_timeout}} --label "wnby pure/scene defenv mutants" -- {{mutants_env}} cargo mutants {{mutants_verify_common_args}} -p abide-verify --file crates/abide-verify/src/verify/defenv.rs --re '{{wnby_verify_pure_scene_defenv_re}}' --output {{mutants_output_dir}}/mutants.out.wnby.verify-pure-scene.defenv -- --lib pure_scene {{mutants_libtest_args}}

check-lang-mutants-wnby-verify-pure-scene-encode-ctors:
  {{runner}} --timeout-secs {{mutants_verify_timeout}} --label "wnby pure/scene encode constructor mutants" -- {{mutants_env}} cargo mutants {{mutants_verify_common_args}} -p abide-verify --file crates/abide-verify/src/verify/encode.rs --re '{{wnby_verify_pure_scene_encode_ctors_re}}' --output {{mutants_output_dir}}/mutants.out.wnby.verify-pure-scene.encode-ctors -- --lib pure_scene {{mutants_libtest_args}}

check-lang-mutants-wnby-verify-pure-scene-encode-apps:
  {{runner}} --timeout-secs {{mutants_verify_timeout}} --label "wnby pure/scene encode application mutants" -- {{mutants_env}} cargo mutants {{mutants_verify_common_args}} -p abide-verify --file crates/abide-verify/src/verify/encode.rs --re '{{wnby_verify_pure_scene_encode_apps_re}}' --output {{mutants_output_dir}}/mutants.out.wnby.verify-pure-scene.encode-apps -- --lib pure_scene {{mutants_libtest_args}}

check-lang-mutants-wnby-verify-pure-scene-encode-collections:
  {{runner}} --timeout-secs {{mutants_verify_timeout}} --label "wnby pure/scene encode collection mutants" -- {{mutants_env}} cargo mutants {{mutants_verify_common_args}} -p abide-verify --file crates/abide-verify/src/verify/encode.rs --re '{{wnby_verify_pure_scene_encode_collections_re}}' --output {{mutants_output_dir}}/mutants.out.wnby.verify-pure-scene.encode-collections -- --lib pure_scene {{mutants_libtest_args}}

check-lang-mutants-wnby-verify-pure-scene-encode-lambda:
  {{runner}} --timeout-secs {{mutants_verify_timeout}} --label "wnby pure/scene encode lambda/refinement mutants" -- {{mutants_env}} cargo mutants {{mutants_verify_common_args}} -p abide-verify --file crates/abide-verify/src/verify/encode.rs --re '{{wnby_verify_pure_scene_encode_lambda_re}}' --output {{mutants_output_dir}}/mutants.out.wnby.verify-pure-scene.encode-lambda -- --lib pure_scene {{mutants_libtest_args}}

check-lang-mutants-wnby-verify-pure-scene-scene:
  {{runner}} --timeout-secs {{mutants_verify_timeout}} --label "wnby pure/scene scene mutants" -- {{mutants_env}} cargo mutants {{mutants_verify_common_args}} -p abide-verify --file crates/abide-verify/src/verify/scene.rs --re '{{wnby_verify_pure_scene_scene_re}}' --output {{mutants_output_dir}}/mutants.out.wnby.verify-pure-scene.scene -- --lib pure_scene {{mutants_libtest_args}}

check-lang-mutants-wnby-verify-pure-scene-scope-walkers:
  {{runner}} --timeout-secs {{mutants_verify_timeout}} --label "wnby pure/scene scope/walker mutants" -- {{mutants_env}} cargo mutants {{mutants_verify_common_args}} -p abide-verify --file crates/abide-verify/src/verify/scope.rs --file crates/abide-verify/src/verify/walkers.rs --re '{{wnby_verify_pure_scene_scope_walkers_re}}' --output {{mutants_output_dir}}/mutants.out.wnby.verify-pure-scene.scope-walkers -- --lib pure_scene {{mutants_libtest_args}}

check-lang-mutants-wnby-verify-dispatch:
  just check-lang-mutants-wnby-verify-dispatch-reconcile
  just check-lang-mutants-wnby-verify-dispatch-float-backend

check-lang-mutants-wnby-verify-dispatch-reconcile:
  {{runner}} --timeout-secs {{mutants_verify_timeout}} --label "wnby verifier dispatch reconciliation mutants" -- {{mutants_env}} cargo mutants {{mutants_verify_common_args}} -p abide-verify --file crates/abide-verify/src/verify/mod.rs --re '{{wnby_verify_dispatch_reconcile_re}}' --output {{mutants_output_dir}}/mutants.out.wnby.verify-dispatch.reconcile -- --lib solver_result_reconciliation {{mutants_libtest_args}}

check-lang-mutants-wnby-verify-dispatch-float-backend:
  {{runner}} --timeout-secs {{mutants_verify_timeout}} --label "wnby verifier dispatch float-backend mutants" -- {{mutants_env}} cargo mutants {{mutants_verify_common_args}} -p abide-verify --file crates/abide-verify/src/verify/mod.rs --re '{{wnby_verify_dispatch_float_backend_re}}' --output {{mutants_output_dir}}/mutants.out.wnby.verify-dispatch.float-backend -- --lib float_requires_z3_result {{mutants_libtest_args}}

check-lang-mutants-wnby-verify-dispatch-broad-shard shard:
  {{runner}} --timeout-secs {{mutants_verify_timeout}} --label "wnby verifier dispatch/lasso mutants shard {{shard}}/{{mutants_shard_total}}" -- {{mutants_env}} cargo mutants {{mutants_verify_common_args}} --shard "$(({{shard}} - 1))/{{mutants_shard_total}}" -p abide-verify --file crates/abide-verify/src/verify/mod.rs --re '{{wnby_verify_dispatch_re}}' --output {{mutants_output_dir}}/mutants.out.wnby.verify-dispatch.{{shard}}-of-{{mutants_shard_total}} -- --lib verify {{mutants_libtest_args}}

coverage:
  {{runner}} --timeout-secs {{cargo_timeout}} --label "abide coverage" -- cargo llvm-cov -p abide --lib --tests

coverage-html:
  {{runner}} --timeout-secs {{cargo_timeout}} --label "abide html coverage" -- cargo llvm-cov -p abide --lib --tests --html

check: fmt-check clippy test

check-strict: check test-unbounded

clean:
  cargo clean
