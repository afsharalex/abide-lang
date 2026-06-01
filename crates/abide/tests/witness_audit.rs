use std::io::Write;
use std::path::PathBuf;

use abide::elab;
use abide::ir;
use abide::lex;
use abide::loader;
use abide::parse::Parser;
use abide::verify::{self, VerificationResult, VerifyConfig, WitnessSemantics};
use abide::witness::{op, rel, WitnessValue};

fn parse_file(path: &str) -> abide::ast::Program {
    let src = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read {path}: {e}"));
    let tokens = lex::lex(&src).unwrap_or_else(|errors| {
        panic!("lex errors in {path}: {errors:?}");
    });
    let mut parser = Parser::new(tokens);
    let program = parser.parse_program().unwrap_or_else(|e| {
        panic!("parse error in {path}: {e}");
    });
    assert!(
        !program.decls.is_empty(),
        "{path} should have at least one declaration"
    );
    program
}

fn elaborate_file(path: &str) -> elab::types::ElabResult {
    let program = parse_file(path);
    let (result, errors) = elab::elaborate(&program);
    let actual_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        actual_errors.is_empty(),
        "{path} should elaborate without errors: {actual_errors:?}"
    );
    result
}

fn load_and_elaborate_files(paths: &[&str]) -> elab::types::ElabResult {
    let path_bufs: Vec<PathBuf> = paths.iter().map(PathBuf::from).collect();
    let (env, load_errors, _all_paths) = loader::load_files(&path_bufs);
    assert!(
        load_errors.is_empty(),
        "{paths:?} should load without errors: {load_errors:?}"
    );
    assert!(
        env.include_load_errors.is_empty(),
        "{paths:?} should have no include errors: {:?}",
        env.include_load_errors
    );

    let (result, errors) = elab::elaborate_env(env);
    let actual_errors: Vec<_> = errors
        .iter()
        .filter(|e| !matches!(e.severity, elab::error::Severity::Warning))
        .collect();
    assert!(
        actual_errors.is_empty(),
        "{paths:?} should elaborate without errors: {actual_errors:?}"
    );
    result
}

fn lower_file(path: &str) -> ir::types::IRProgram {
    let result = elaborate_file(path);
    let (ir_program, _lower_diag) = ir::lower(&result);
    ir_program
}

fn lower_source(src: &str) -> ir::types::IRProgram {
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("test.ab");
    let mut f = std::fs::File::create(&file).expect("create");
    f.write_all(src.as_bytes()).expect("write");
    drop(f);
    lower_file(file.to_str().expect("utf8 test path"))
}

fn verify_source_with_config(src: &str, config: &VerifyConfig) -> Vec<VerificationResult> {
    let prog = lower_source(src);
    verify::verify_all(&prog, config)
}

fn verify_files_with_config(paths: &[&str], config: &VerifyConfig) -> Vec<VerificationResult> {
    let result = load_and_elaborate_files(paths);
    let (prog, _lower_diag) = ir::lower(&result);
    verify::verify_all(&prog, config)
}

fn result_named<'a>(results: &'a [VerificationResult], name: &str) -> &'a VerificationResult {
    results
        .iter()
        .find(|result| match result {
            VerificationResult::Proved { name: n, .. }
            | VerificationResult::Admitted { name: n, .. }
            | VerificationResult::Checked { name: n, .. }
            | VerificationResult::Counterexample { name: n, .. }
            | VerificationResult::ScenePass { name: n, .. }
            | VerificationResult::SceneFail { name: n, .. }
            | VerificationResult::SceneUnknown { name: n, .. }
            | VerificationResult::Unprovable { name: n, .. }
            | VerificationResult::FnContractProved { name: n, .. }
            | VerificationResult::FnContractAdmitted { name: n, .. }
            | VerificationResult::FnContractFailed { name: n, .. }
            | VerificationResult::LivenessViolation { name: n, .. }
            | VerificationResult::Deadlock { name: n, .. } => n == name,
        })
        .unwrap_or_else(|| panic!("expected verification result named `{name}`, got: {results:?}"))
}

fn system_field<'a>(state: &'a op::State, system: &str, field: &str) -> &'a WitnessValue {
    state
        .system_fields()
        .get(system)
        .and_then(|fields| fields.get(field))
        .unwrap_or_else(|| panic!("expected system field {system}.{field} in state: {state:?}"))
}

fn tuple_value(
    relation: &rel::RelationInstance,
    tuple_index: usize,
    value_index: usize,
) -> &WitnessValue {
    relation
        .tuples()
        .get(tuple_index)
        .and_then(|tuple| tuple.values().get(value_index))
        .unwrap_or_else(|| panic!("expected tuple {tuple_index}[{value_index}] in {relation:?}"))
}

fn enum_variant(value: &WitnessValue, expected_enum: &str, expected_variant: &str) -> bool {
    matches!(
        value,
        WitnessValue::EnumVariant {
            enum_name,
            variant,
            ..
        } if enum_name == expected_enum && variant == expected_variant
    )
}

fn signal_color<'a>(state: &'a op::State, slot: &op::EntitySlotRef) -> Option<&'a str> {
    let value = state
        .entity_slots()
        .get(slot)
        .filter(|entity| entity.active())?
        .fields()
        .get("color")?;
    match value {
        WitnessValue::EnumVariant {
            enum_name, variant, ..
        } if enum_name == "Light" => Some(variant.as_str()),
        _ => None,
    }
}

fn unfair_signal_lasso_violation_slot(witness: &op::LassoWitness) -> Option<op::EntitySlotRef> {
    let behavior = witness.behavior();
    let loop_start = witness.loop_start();
    let loop_states = &behavior.states()[loop_start..];
    let loop_entry = behavior.state(loop_start)?;

    loop_entry.entity_slots().iter().find_map(|(slot, entity)| {
        if slot.entity() != "Signal" || !entity.active() {
            return None;
        }
        if signal_color(loop_entry, slot) != Some("Red") {
            return None;
        }
        loop_states
            .iter()
            .all(|state| signal_color(state, slot) == Some("Red"))
            .then(|| slot.clone())
    })
}

#[test]
fn operational_counterexample_audit_tracks_system_field_enums_and_steps() {
    let src = r"module T

enum Screen = home | compose
enum Mode = normal | editing

system Ui {
  screen: Screen = @home
  mode: Mode = @normal

  command handle() requires screen == @home {
    screen' = @compose
  }
}

verify v {
  assume {
    let ui = Ui {}
  }
  assert always screen == @home
}
";

    let results = verify_source_with_config(src, &VerifyConfig::default());
    let result = result_named(&results, "v");
    let VerificationResult::Counterexample {
        replay: Some(replay),
        ..
    } = result
    else {
        panic!("expected counterexample with replay metadata, got: {result:?}");
    };
    assert!(replay.checked, "operational witness should replay");
    assert!(
        replay.property_violated,
        "replay should confirm the asserted safety property is violated"
    );

    let witness = result
        .operational_witness()
        .expect("counterexample should carry an operational witness");
    witness
        .validate()
        .expect("operational witness should validate");

    let op::OperationalWitness::Counterexample { behavior } = witness else {
        panic!("expected counterexample witness, got: {witness:?}");
    };

    assert_eq!(behavior.states().len(), 2);
    assert_eq!(behavior.transitions().len(), 1);

    let initial = behavior.state(0).expect("initial state");
    let next = behavior.state(1).expect("next state");
    assert!(enum_variant(
        system_field(initial, "Ui", "mode"),
        "Mode",
        "normal"
    ));
    assert!(enum_variant(
        system_field(next, "Ui", "mode"),
        "Mode",
        "normal"
    ));
    assert!(enum_variant(
        system_field(initial, "Ui", "screen"),
        "Screen",
        "home"
    ));
    assert!(
        enum_variant(system_field(next, "Ui", "screen"), "Screen", "compose"),
        "the witness must include the state that falsifies `screen == @home`"
    );

    let transition = behavior.transition(0).expect("first transition");
    assert_eq!(transition.atomic_steps().len(), 1);
    let step = &transition.atomic_steps()[0];
    assert_eq!(step.system(), "Ui");
    assert_eq!(step.command(), "handle");
    assert_eq!(step.step_name(), Some("handle"));
}

#[test]
fn relational_counterexample_audit_exposes_relation_native_system_fields() {
    let src = r"module T

enum Screen = home | compose
enum Mode = normal | editing

system Ui {
  screen: Screen = @home
  mode: Mode = @normal

  command handle() requires screen == @home {
    screen' = @compose
  }
}

verify v {
  assume {
    let ui = Ui {}
  }
  assert always screen == @home
}
";

    let config = VerifyConfig {
        witness_semantics: WitnessSemantics::Relational,
        ..VerifyConfig::default()
    };
    let results = verify_source_with_config(src, &config);
    let result = result_named(&results, "v");
    assert!(
        matches!(result, VerificationResult::Counterexample { .. }),
        "expected relational counterexample result, got: {result:?}"
    );
    let witness = result
        .relational_witness()
        .expect("counterexample should carry a relational witness");
    witness
        .validate()
        .expect("relational witness should validate");

    let temporal = witness
        .as_temporal()
        .expect("bounded counterexample should produce a temporal relational witness");
    assert!(
        temporal.states().len() >= 2,
        "relational witness should expose at least the initial state and first violating successor"
    );
    assert_eq!(temporal.loop_start(), None);

    let initial = &temporal.states()[0];

    let mode_initial = initial
        .field_relation("Ui", "mode")
        .expect("Ui.mode relation in initial state");
    assert_eq!(mode_initial.arity(), 2);
    assert!(
        matches!(
        tuple_value(mode_initial, 0, 1),
        WitnessValue::EnumVariant { enum_name, variant, .. }
            if enum_name == "Mode" && variant == "normal"
        ),
        "initial mode tuple should preserve non-mutated system state"
    );
    let screen_initial = initial
        .field_relation("Ui", "screen")
        .expect("Ui.screen relation in initial state");
    assert!(
        matches!(
            tuple_value(screen_initial, 0, 1),
            WitnessValue::EnumVariant { enum_name, variant, .. }
                if enum_name == "Screen" && variant == "home"
        ),
        "initial screen tuple should satisfy the asserted property"
    );

    let compose_state = temporal
        .states()
        .iter()
        .find(|state| {
            state.field_relation("Ui", "screen").is_some_and(|screen| {
                matches!(
                    tuple_value(screen, 0, 1),
                    WitnessValue::EnumVariant { enum_name, variant, .. }
                        if enum_name == "Screen" && variant == "compose"
                )
            })
        })
        .expect("relational witness should include the violating compose state");
    let screen_compose = compose_state
        .field_relation("Ui", "screen")
        .expect("Ui.screen relation in compose state");
    assert_eq!(screen_compose.arity(), 2);
    assert!(
        matches!(
            tuple_value(screen_compose, 0, 1),
            WitnessValue::EnumVariant { enum_name, variant, .. }
                if enum_name == "Screen" && variant == "compose"
        ),
        "relational witness must expose a state that violates `screen == @home`"
    );
}

#[test]
fn liveness_witness_audit_exposes_semantic_lasso_violation() {
    let results =
        verify_files_with_config(&["tests/fixtures/fairness.ab"], &VerifyConfig::default());
    let result = result_named(&results, "unfair_signal");
    assert!(
        matches!(result, VerificationResult::LivenessViolation { .. }),
        "expected liveness violation result, got: {result:?}"
    );
    let witness = result
        .operational_witness()
        .expect("liveness violation should carry an operational witness");
    witness
        .validate()
        .expect("liveness witness should validate");

    let op::OperationalWitness::Liveness { witness } = witness else {
        panic!("expected liveness witness, got: {witness:?}");
    };

    assert!(witness.loop_start() < witness.behavior().states().len());
    assert!(!witness.behavior().transitions().is_empty());
    assert_eq!(
        witness.behavior().transitions().len() + 1,
        witness.behavior().states().len()
    );
    let red_slot = unfair_signal_lasso_violation_slot(witness)
        .expect("lasso should keep some active red signal from ever becoming green");
    assert_eq!(red_slot.entity(), "Signal");

    let unrelated = op::LassoWitness::new(
        op::Behavior::builder()
            .state(op::State::builder().build())
            .build()
            .expect("valid unrelated behavior"),
        0,
    )
    .expect("valid unrelated lasso envelope");
    assert!(
        unfair_signal_lasso_violation_slot(&unrelated).is_none(),
        "audit helper must reject a lasso unrelated to the unfair_signal property"
    );
}
