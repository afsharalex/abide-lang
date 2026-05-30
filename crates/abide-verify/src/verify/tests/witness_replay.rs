use super::*;

#[test]
fn bmc_counterexample_replay_metadata_accepts_valid_operational_trace() {
    let ir = lower_fixture("shortest_counterexample.ab");
    let results = verify_all(
        &ir,
        &VerifyConfig {
            bounded_only: true,
            ..VerifyConfig::default()
        },
    );
    assert_eq!(results.len(), 1);

    let VerificationResult::Counterexample {
        replay: Some(replay),
        ..
    } = &results[0]
    else {
        panic!(
            "expected counterexample with replay metadata, got {}",
            results[0]
        );
    };

    assert!(replay.checked, "valid operational trace should replay");
    assert!(
        replay.property_violated,
        "replay should confirm property violation"
    );
    assert_eq!(replay.steps, 1);
}

#[test]
fn bmc_counterexample_replay_rejects_corrupted_operational_trace() {
    let ir = lower_fixture("shortest_counterexample.ab");
    let results = verify_all(
        &ir,
        &VerifyConfig {
            bounded_only: true,
            ..VerifyConfig::default()
        },
    );
    let witness = results[0]
        .operational_witness()
        .expect("counterexample should carry operational witness");
    let behavior = witness.behavior();
    let corrupted = op::OperationalWitness::counterexample(
        op::Behavior::from_parts(
            vec![behavior.states()[0].clone(), behavior.states()[0].clone()],
            behavior.transitions().to_vec(),
        )
        .expect("corrupted behavior still has valid topology"),
    )
    .expect("valid operational witness envelope");

    let replay = replay_counterexample_witness(&ir, &ir.verifies[0], &corrupted);

    assert!(!replay.checked, "corrupted transition should not replay");
    assert!(
        replay
            .error
            .as_deref()
            .is_some_and(|error| error.contains("no matching operational successor")),
        "expected successor mismatch, got {replay:?}"
    );
}
