use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::str::FromStr;

use miette::{IntoDiagnostic, NamedSource, WrapErr};

use crate::diagnostic::Diagnostic;
use crate::verify;
use crate::witness::op;
use abide_witness::{rel, EvidencePayload};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum VerifyReportFormat {
    Json,
    Html,
    Markdown,
}

impl VerifyReportFormat {
    fn extension(self) -> &'static str {
        match self {
            Self::Json => "json",
            Self::Html => "html",
            Self::Markdown => "md",
        }
    }
}

impl FromStr for VerifyReportFormat {
    type Err = String;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        match value {
            "json" => Ok(Self::Json),
            "html" => Ok(Self::Html),
            "markdown" | "md" => Ok(Self::Markdown),
            other => Err(format!(
                "unsupported report format `{other}`; expected one of: json, html, markdown"
            )),
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct VerifyReportRequest {
    format: VerifyReportFormat,
    output_dir: PathBuf,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TextArt {
    Utf8,
    Ascii,
}

impl TextArt {
    fn branch(self) -> &'static str {
        match self {
            Self::Utf8 => "├─",
            Self::Ascii => "|-",
        }
    }

    fn elbow(self) -> &'static str {
        match self {
            Self::Utf8 => "└─",
            Self::Ascii => "`-",
        }
    }

    fn vertical(self) -> &'static str {
        match self {
            Self::Utf8 => "│",
            Self::Ascii => "|",
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct RenderedAssignment {
    pub(crate) entity: String,
    pub(crate) field: String,
    pub(crate) value: String,
}

#[derive(Clone, Debug)]
pub(crate) struct RenderedTraceChange {
    pub(crate) entity: String,
    pub(crate) field: String,
    pub(crate) before: Option<String>,
    pub(crate) after: Option<String>,
}

#[derive(Clone, Debug)]
pub(crate) struct RenderedTraceObservation {
    pub(crate) name: String,
    pub(crate) value: String,
}

#[derive(Clone, Debug)]
pub(crate) struct RenderedTraceStep {
    pub(crate) step: usize,
    pub(crate) event: Option<String>,
    pub(crate) assignments: Vec<RenderedAssignment>,
    pub(crate) changes: Vec<RenderedTraceChange>,
    pub(crate) observations: Vec<RenderedTraceObservation>,
}

#[derive(Clone, Debug)]
pub(crate) struct RenderedFairnessEntry {
    pub(crate) kind: String,
    pub(crate) system: String,
    pub(crate) event: String,
    pub(crate) status: String,
}

#[derive(Clone, Debug)]
pub(crate) struct RenderedEventDiagnostic {
    pub(crate) system: String,
    pub(crate) event: String,
    pub(crate) reason: String,
}

#[derive(Clone, Debug)]
pub(crate) enum OperationalTraceView {
    Linear {
        steps: Vec<RenderedTraceStep>,
    },
    Lasso {
        prefix: Vec<RenderedTraceStep>,
        loop_steps: Vec<RenderedTraceStep>,
        loop_start: usize,
        fairness: Vec<RenderedFairnessEntry>,
    },
    Deadlock {
        steps: Vec<RenderedTraceStep>,
        deadlock_step: usize,
        reason: String,
        event_diagnostics: Vec<RenderedEventDiagnostic>,
    },
}

pub(crate) fn operational_trace_view(
    result: &verify::VerificationResult,
) -> Option<OperationalTraceView> {
    match result {
        verify::VerificationResult::Counterexample { .. } => {
            result
                .operational_witness()
                .map(|operational| OperationalTraceView::Linear {
                    steps: render_trace_steps_from_behavior(operational.behavior()),
                })
        }
        verify::VerificationResult::Deadlock {
            step,
            reason,
            event_diagnostics,
            ..
        } => result
            .operational_witness()
            .map(|operational| OperationalTraceView::Deadlock {
                steps: render_trace_steps_from_behavior(operational.behavior()),
                deadlock_step: *step,
                reason: reason.clone(),
                event_diagnostics: event_diagnostics
                    .iter()
                    .map(|diag| RenderedEventDiagnostic {
                        system: diag.system.clone(),
                        event: diag.event.clone(),
                        reason: diag.reason.clone(),
                    })
                    .collect(),
            }),
        verify::VerificationResult::LivenessViolation {
            loop_start,
            fairness_analysis,
            ..
        } => result.operational_witness().map(|operational| {
            let steps = render_trace_steps_from_behavior(operational.behavior());
            let split_at = (*loop_start).min(steps.len());
            OperationalTraceView::Lasso {
                prefix: steps[..split_at].to_vec(),
                loop_steps: steps[split_at..].to_vec(),
                loop_start: *loop_start,
                fairness: fairness_analysis
                    .iter()
                    .map(|entry| RenderedFairnessEntry {
                        kind: match entry.kind {
                            verify::FairnessKind::Weak => "WF".to_owned(),
                            verify::FairnessKind::Strong => "SF".to_owned(),
                        },
                        system: entry.system.clone(),
                        event: entry.event.clone(),
                        status: match entry.status {
                            verify::FairnessStatus::EnabledAndFired => "ENABLED + FIRED".to_owned(),
                            verify::FairnessStatus::EnabledButStarved => {
                                "ENABLED + NEVER FIRED".to_owned()
                            }
                            verify::FairnessStatus::NeverEnabled => "NEVER ENABLED".to_owned(),
                        },
                    })
                    .collect(),
            }
        }),
        _ => None,
    }
}

fn render_trace_steps_from_behavior(behavior: &op::Behavior) -> Vec<RenderedTraceStep> {
    let system_count = behavior_system_count(behavior);
    behavior
        .states()
        .iter()
        .enumerate()
        .map(|(step, state)| {
            let assignments = rendered_assignments_for_state(state);
            let changes = behavior
                .transition_after_state(step)
                .and_then(|_| {
                    behavior
                        .state(step + 1)
                        .map(|next| rendered_changes_between_states(state, next))
                })
                .unwrap_or_default();

            let observations = behavior
                .transition_after_state(step)
                .map(|transition| {
                    transition
                        .observations()
                        .iter()
                        .map(|observation| RenderedTraceObservation {
                            name: observation.name().to_owned(),
                            value: render_witness_value(observation.value()),
                        })
                        .collect::<Vec<_>>()
                })
                .unwrap_or_default();

            RenderedTraceStep {
                step,
                event: behavior
                    .transition_after_state(step)
                    .and_then(|transition| render_transition_event_label(transition, system_count)),
                assignments,
                changes,
                observations,
            }
        })
        .collect()
}

fn rendered_assignments_for_state(state: &op::State) -> Vec<RenderedAssignment> {
    rendered_assignment_map_for_state(state)
        .into_iter()
        .map(|((entity, field), value)| RenderedAssignment {
            entity,
            field,
            value,
        })
        .collect()
}

fn rendered_assignment_map_for_state(state: &op::State) -> BTreeMap<(String, String), String> {
    let mut assignments = BTreeMap::new();
    for (slot_ref, entity_state) in state.entity_slots() {
        if !entity_state.active() {
            continue;
        }
        let entity_label = format!("{}[{}]", slot_ref.entity(), slot_ref.slot());
        for (field, value) in entity_state.fields() {
            assignments.insert(
                (entity_label.clone(), field.clone()),
                render_witness_value(value),
            );
        }
    }
    for (system, fields) in state.system_fields() {
        for (field, value) in fields {
            assignments.insert(
                (format!("System::{system}"), field.clone()),
                render_witness_value(value),
            );
        }
    }
    assignments
}

fn rendered_changes_between_states(
    before: &op::State,
    after: &op::State,
) -> Vec<RenderedTraceChange> {
    let before = rendered_assignment_map_for_state(before);
    let after = rendered_assignment_map_for_state(after);
    let keys = before
        .keys()
        .chain(after.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    keys.into_iter()
        .filter_map(|(entity, field)| {
            let before_value = before.get(&(entity.clone(), field.clone())).cloned();
            let after_value = after.get(&(entity.clone(), field.clone())).cloned();
            (before_value != after_value).then_some(RenderedTraceChange {
                entity,
                field,
                before: before_value,
                after: after_value,
            })
        })
        .collect()
}

fn behavior_system_count(behavior: &op::Behavior) -> usize {
    let mut systems = HashSet::new();
    for state in behavior.states() {
        systems.extend(state.system_fields().keys().map(String::as_str));
    }
    for transition in behavior.transitions() {
        systems.extend(transition.atomic_steps().iter().map(op::AtomicStep::system));
    }
    systems.len()
}

fn render_transition_event_label(
    transition: &op::Transition,
    system_count: usize,
) -> Option<String> {
    let labels: Vec<String> = transition
        .atomic_steps()
        .iter()
        .map(|atomic_step| {
            if system_count == 1 {
                atomic_step.command().to_owned()
            } else {
                format!("{}::{}", atomic_step.system(), atomic_step.command())
            }
        })
        .collect();

    match labels.len() {
        0 => None,
        1 => labels.into_iter().next(),
        _ => Some(labels.join(" & ")),
    }
}

fn render_witness_value(value: &op::WitnessValue) -> String {
    match value {
        op::WitnessValue::Unknown => "?".to_owned(),
        op::WitnessValue::Int(v) => v.to_string(),
        op::WitnessValue::Bool(v) => v.to_string(),
        op::WitnessValue::Real(v)
        | op::WitnessValue::Float(v)
        | op::WitnessValue::String(v)
        | op::WitnessValue::Identity(v) => v.clone(),
        op::WitnessValue::EnumVariant { enum_name, variant } => format!("@{enum_name}::{variant}"),
        op::WitnessValue::SlotRef(slot) => format!("{}[{}]", slot.entity(), slot.slot()),
        op::WitnessValue::Tuple(values) => format!(
            "({})",
            values
                .iter()
                .map(render_witness_value)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        op::WitnessValue::Record(fields) => format!(
            "{{{}}}",
            fields
                .iter()
                .map(|(name, value)| format!("{name}: {}", render_witness_value(value)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        op::WitnessValue::Set(values) => format!(
            "{{{}}}",
            values
                .iter()
                .map(render_witness_value)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        op::WitnessValue::Seq(values) => format!(
            "[{}]",
            values
                .iter()
                .map(render_witness_value)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        op::WitnessValue::Map(entries) => format!(
            "{{{}}}",
            entries
                .iter()
                .map(|(key, value)| {
                    format!(
                        "{} -> {}",
                        render_witness_value(key),
                        render_witness_value(value)
                    )
                })
                .collect::<Vec<_>>()
                .join(", ")
        ),
        op::WitnessValue::Opaque { display, .. } => display.clone(),
    }
}

fn terminal_text_art() -> TextArt {
    for key in ["LC_ALL", "LC_CTYPE", "LANG"] {
        if let Ok(value) = std::env::var(key) {
            let normalized = value.to_ascii_lowercase();
            if normalized.contains("utf-8") || normalized.contains("utf8") {
                return TextArt::Utf8;
            }
        }
    }
    TextArt::Ascii
}

pub(crate) fn parse_verify_report_request(
    report_args: Option<Vec<String>>,
) -> miette::Result<Option<VerifyReportRequest>> {
    let Some(args) = report_args else {
        return Ok(None);
    };
    let format = args
        .first()
        .expect("clap enforces at least one arg for --report")
        .parse::<VerifyReportFormat>()
        .map_err(|err| miette::miette!("{err}"))?;
    let output_dir = args
        .get(1)
        .map_or_else(|| PathBuf::from("reports"), PathBuf::from);
    Ok(Some(VerifyReportRequest { format, output_dir }))
}

pub(crate) fn report_verification_result(
    result: &verify::VerificationResult,
    sources: &[(String, String)],
    verbose: bool,
    debug_evidence: bool,
) {
    use verify::VerificationResult;

    if result.is_failure() {
        if let Some(span) = result.span() {
            let matching_source = if let Some(file) = result.file() {
                sources.iter().find(|(name, _)| name == file)
            } else if sources.len() == 1 {
                sources.first()
            } else {
                None
            };

            if let Some((name, src)) = matching_source {
                if span.end <= src.len() {
                    let label = match result {
                        VerificationResult::Counterexample { name, .. } => {
                            crate::messages::label_counterexample(name)
                        }
                        VerificationResult::SceneFail { name, reason, .. } => {
                            crate::messages::label_scene_fail(name, reason)
                        }
                        VerificationResult::Unprovable { name, hint, .. } => {
                            crate::messages::label_unprovable(name, hint)
                        }
                        VerificationResult::FnContractFailed { name, .. } => {
                            crate::messages::label_fn_contract_failed(name)
                        }
                        VerificationResult::LivenessViolation { name, .. } => {
                            crate::messages::label_liveness_violation(name)
                        }
                        VerificationResult::Deadlock { name, step, .. } => {
                            crate::messages::label_deadlock(name, *step)
                        }
                        _ => String::new(),
                    };
                    let named = NamedSource::new(display_path(name), src.clone());
                    let diag = miette::miette!(
                        labels = vec![miette::LabeledSpan::at(span.start..span.end, &label)],
                        "{}",
                        render_terminal_summary(result)
                    )
                    .with_source_code(named);
                    eprintln!("{diag:?}");
                    if verbose {
                        report_result_verbose_details(result, true);
                    } else {
                        eprintln!("{}", render_terminal_summary(result));
                        if let Some(human_text) =
                            render_result_human_text(result, terminal_text_art())
                        {
                            eprintln!("{human_text}");
                        }
                    }
                    if debug_evidence {
                        report_result_debug_evidence(result, true);
                    }
                    return;
                }
            }
        }
        if verbose {
            report_result_verbose_details(result, true);
        } else {
            eprintln!("{}", render_terminal_summary(result));
        }
        if debug_evidence {
            report_result_debug_evidence(result, true);
        }
    } else {
        if verbose {
            report_result_verbose_details(result, false);
        } else {
            println!("{}", render_terminal_summary(result));
        }
        if debug_evidence {
            report_result_debug_evidence(result, false);
        }
    }
}

#[allow(clippy::too_many_arguments, clippy::fn_params_excessive_bools)]
pub(crate) fn write_verification_report(
    request: &VerifyReportRequest,
    files: &[PathBuf],
    solver_name: &str,
    chc_solver_name: &str,
    bounded_only: bool,
    unbounded_only: bool,
    induction_timeout: u64,
    bmc_timeout: u64,
    ic3_timeout: u64,
    no_ic3: bool,
    no_prop_verify: bool,
    no_fn_verify: bool,
    progress: bool,
    witness_semantics_name: &str,
    target: Option<&str>,
    diagnostics: &[Diagnostic],
    results: &[verify::VerificationResult],
) -> miette::Result<PathBuf> {
    let report_json = build_verification_report_json(
        files,
        solver_name,
        chc_solver_name,
        bounded_only,
        unbounded_only,
        induction_timeout,
        bmc_timeout,
        ic3_timeout,
        no_ic3,
        no_prop_verify,
        no_fn_verify,
        progress,
        witness_semantics_name,
        target,
        diagnostics,
        results,
    );
    fs::create_dir_all(&request.output_dir)
        .into_diagnostic()
        .wrap_err_with(|| {
            format!(
                "failed to create report directory {}",
                request.output_dir.display()
            )
        })?;
    let report_path = derive_verify_report_path(&request.output_dir, files, request.format);
    let report_body =
        render_verification_report(request.format, &report_json, diagnostics, results)
            .wrap_err("failed to render verification report")?;
    fs::write(&report_path, report_body)
        .into_diagnostic()
        .wrap_err_with(|| {
            format!(
                "failed to write verification report to {}",
                report_path.display()
            )
        })?;
    Ok(report_path)
}

fn derive_verify_report_path(
    output_dir: &Path,
    files: &[PathBuf],
    format: VerifyReportFormat,
) -> PathBuf {
    let basename = if files.len() == 1 {
        files[0]
            .file_stem()
            .and_then(|stem| stem.to_str())
            .filter(|stem| !stem.is_empty())
            .map_or_else(
                || "verification-report".to_owned(),
                |stem| format!("{stem}.report"),
            )
    } else {
        "verification-report".to_owned()
    };
    output_dir.join(format!("{basename}.{}", format.extension()))
}

#[allow(clippy::too_many_arguments, clippy::fn_params_excessive_bools)]
fn build_verification_report_json(
    files: &[PathBuf],
    solver_name: &str,
    chc_solver_name: &str,
    bounded_only: bool,
    unbounded_only: bool,
    induction_timeout: u64,
    bmc_timeout: u64,
    ic3_timeout: u64,
    no_ic3: bool,
    no_prop_verify: bool,
    no_fn_verify: bool,
    progress: bool,
    witness_semantics_name: &str,
    target: Option<&str>,
    diagnostics: &[Diagnostic],
    results: &[verify::VerificationResult],
) -> serde_json::Value {
    let failure_count = results.iter().filter(|result| result.is_failure()).count();
    serde_json::json!({
        "kind": "verification_report",
        "version": 1,
        "files": files.iter().map(|path| path.display().to_string()).collect::<Vec<_>>(),
        "summary": {
            "result_count": results.len(),
            "failure_count": failure_count,
            "diagnostic_count": diagnostics.len(),
        },
        "config": {
            "solver": solver_name,
            "chc_solver": chc_solver_name,
            "bounded_only": bounded_only,
            "unbounded_only": unbounded_only,
            "induction_timeout_ms": induction_timeout.saturating_mul(1000),
            "bmc_timeout_ms": bmc_timeout.saturating_mul(1000),
            "ic3_timeout_ms": ic3_timeout.saturating_mul(1000),
            "no_ic3": no_ic3,
            "no_prop_verify": no_prop_verify,
            "no_fn_verify": no_fn_verify,
            "progress": progress,
            "witness_semantics": witness_semantics_name,
            "target": target,
        },
        "diagnostics": diagnostics,
        "results": results,
    })
}

fn render_verification_report(
    format: VerifyReportFormat,
    report_json: &serde_json::Value,
    diagnostics: &[Diagnostic],
    results: &[verify::VerificationResult],
) -> miette::Result<String> {
    match format {
        VerifyReportFormat::Json => serde_json::to_string_pretty(report_json)
            .into_diagnostic()
            .wrap_err("failed to serialize verification report to JSON"),
        VerifyReportFormat::Markdown => Ok(render_verification_report_markdown(
            report_json,
            diagnostics,
            results,
        )),
        VerifyReportFormat::Html => Ok(render_verification_report_html(
            report_json,
            diagnostics,
            results,
        )),
    }
}

fn render_verification_report_markdown(
    report_json: &serde_json::Value,
    diagnostics: &[Diagnostic],
    results: &[verify::VerificationResult],
) -> String {
    let mut out = String::new();
    out.push_str("# Verification Report\n\n");
    if let Some(files) = report_json
        .get("files")
        .and_then(serde_json::Value::as_array)
    {
        out.push_str("## Files\n\n");
        for file in files.iter().filter_map(serde_json::Value::as_str) {
            out.push_str("- `");
            out.push_str(&display_path(file));
            out.push_str("`\n");
        }
        out.push('\n');
    }
    out.push_str("## Summary\n\n");
    if let Some(summary) = report_json.get("summary") {
        for (label, key) in [
            ("Result count", "result_count"),
            ("Failure count", "failure_count"),
            ("Diagnostic count", "diagnostic_count"),
        ] {
            if let Some(value) = summary.get(key).and_then(serde_json::Value::as_u64) {
                out.push_str("- ");
                out.push_str(label);
                out.push_str(": ");
                out.push_str(&value.to_string());
                out.push('\n');
            }
        }
        out.push('\n');
    }
    let failing_results = results
        .iter()
        .filter(|result| result.is_failure())
        .collect::<Vec<_>>();
    let passing_results = results
        .iter()
        .filter(|result| !result.is_failure())
        .collect::<Vec<_>>();

    out.push_str("## Results\n\n");
    if results.is_empty() {
        out.push_str("_No verification results._\n\n");
    } else {
        if !failing_results.is_empty() {
            out.push_str("### Failing Results\n\n");
            for result in &failing_results {
                render_markdown_result(&mut out, result);
            }
        }
        if !passing_results.is_empty() {
            out.push_str("### Passing Results\n\n");
            for result in &passing_results {
                render_markdown_result(&mut out, result);
            }
        }
    }
    out.push_str("## Diagnostics\n\n");
    if diagnostics.is_empty() {
        out.push_str("_No diagnostics._\n");
    } else {
        for diagnostic in diagnostics {
            out.push_str("- ");
            out.push_str(&diagnostic.to_string());
            out.push('\n');
        }
    }
    out
}

fn render_markdown_result(out: &mut String, result: &verify::VerificationResult) {
    out.push_str("#### ");
    out.push_str(&escape_markdown_heading(&render_result_heading(result)));
    out.push_str("\n\n");
    out.push_str(&render_markdown_summary_paragraph(result));
    out.push_str("\n\n");
    if let Some((title, explanation)) = render_markdown_failure_explanation(result) {
        out.push_str("##### ");
        out.push_str(title);
        out.push_str("\n\n");
        out.push_str(&explanation);
        out.push_str("\n\n");
    }
    if let Some(evidence_block) = render_markdown_evidence(result) {
        out.push_str(&evidence_block);
        out.push('\n');
    }
    let details = render_report_context_details(result);
    if !details.is_empty() {
        out.push_str("##### Context\n\n");
        for line in details.lines() {
            out.push_str("- ");
            out.push_str(line);
            out.push('\n');
        }
        out.push('\n');
    }
}

fn render_markdown_evidence(result: &verify::VerificationResult) -> Option<String> {
    if let Some(trace_text) = operational_trace_view(result)
        .map(|trace| render_operational_trace_text(result, &trace, TextArt::Utf8))
    {
        return Some(format!("##### Evidence\n\n```text\n{trace_text}\n```\n"));
    }
    let evidence = result.evidence()?;
    match evidence.payload() {
        EvidencePayload::Witness(witness) => match witness.payload() {
            abide_witness::WitnessPayload::Relational(witness) => {
                Some(render_markdown_relational_evidence(witness))
            }
            abide_witness::WitnessPayload::Operational(_) => None,
            _ => None,
        },
        EvidencePayload::Countermodel(countermodel) => (!countermodel.bindings().is_empty())
            .then(|| render_markdown_countermodel_evidence(countermodel)),
        EvidencePayload::ProofArtifactRef(proof_artifact) => {
            Some(render_markdown_proof_artifact_evidence(proof_artifact))
        }
        _ => None,
    }
}

fn render_verification_report_html(
    report_json: &serde_json::Value,
    diagnostics: &[Diagnostic],
    results: &[verify::VerificationResult],
) -> String {
    let failure_indices = results
        .iter()
        .enumerate()
        .filter_map(|(idx, result)| result.is_failure().then_some(idx))
        .collect::<Vec<_>>();
    let success_indices = results
        .iter()
        .enumerate()
        .filter_map(|(idx, result)| (!result.is_failure()).then_some(idx))
        .collect::<Vec<_>>();
    let proved_count = results
        .iter()
        .filter(|result| matches!(result, verify::VerificationResult::Proved { .. }))
        .count();
    let checked_count = results
        .iter()
        .filter(|result| matches!(result, verify::VerificationResult::Checked { .. }))
        .count();
    let admitted_count = results
        .iter()
        .filter(|result| matches!(result, verify::VerificationResult::Admitted { .. }))
        .count();

    let mut out = String::new();
    out.push_str(
        "<!doctype html><html><head><meta charset=\"utf-8\"><title>Verification Report</title>",
    );
    out.push_str("<style>body{font-family:ui-sans-serif,system-ui,sans-serif;max-width:1120px;margin:0 auto;padding:2.75rem 1.25rem 4rem;line-height:1.55;background:#f7f3eb;color:#1f1b17}h1,h2,h3,h4{line-height:1.1;letter-spacing:-.02em}h1,h2{font-family:Iowan Old Style,Palatino Linotype,Book Antiqua,Georgia,serif}h1{font-size:2.65rem;margin:0 0 .4rem}h2{font-size:1.05rem;text-transform:uppercase;letter-spacing:.08em;color:#6a6257;margin:2rem 0 .8rem}h3{font-size:1.35rem;margin:0}h4{font-size:1rem;margin:0}.lede{color:#5a5146;max-width:56rem;margin:0 0 1.5rem}.report-shell{display:flex;flex-direction:column;gap:1.6rem}.summary-grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:.7rem;margin:1.15rem 0 1rem}.summary-card{background:rgba(255,255,255,.72);border:1px solid #e4ddd2;border-radius:14px;padding:.95rem 1rem .9rem;backdrop-filter:blur(4px)}.summary-card .label{display:block;color:#756b5e;font-size:.76rem;text-transform:uppercase;letter-spacing:.08em;margin-bottom:.32rem}.summary-card .value{font-size:1.7rem;font-weight:700}.file-list{display:flex;flex-wrap:wrap;gap:.5rem}.file-chip,.chip{display:inline-flex;align-items:center;gap:.3rem;border-radius:999px;padding:.28rem .62rem;font-size:.87rem}.file-chip{background:#e8e1d5;color:#433b33}.chip{background:#ece7ff;color:#3f3683}.chip-muted{background:#efe9e0;color:#5a5146}.chip-cycle{background:#f7e2b8;color:#7b5410}.chip-location{background:#ede6db;color:#4a4239}.result-stack{display:flex;flex-direction:column;gap:1rem}.result-brief{display:flex;align-items:flex-start;gap:.9rem;background:rgba(255,255,255,.86);border:1px solid #e7dfd3;border-radius:18px;padding:1.15rem 1.2rem}.result-failure{border-left:5px solid #b44b38;background:linear-gradient(180deg,rgba(255,255,255,.96) 0%,rgba(255,246,243,.94) 100%)}.verdict-pill{display:inline-flex;align-items:center;border-radius:999px;padding:.28rem .62rem;font-size:.77rem;font-weight:700;letter-spacing:.04em;text-transform:uppercase;white-space:nowrap}.verdict-failure{background:#fae2db;color:#8f2f1d}.verdict-success{background:#dbefe0;color:#1e6a3a}.verdict-neutral{background:#ece6de;color:#4e463c}.result-body{flex:1;min-width:0}.result-summary{margin:.38rem 0 .75rem;color:#4f473d}.meta-row{display:flex;flex-wrap:wrap;gap:.42rem .48rem;margin:.15rem 0 .35rem}.failure-context{margin:.75rem 0 0;color:#5b5248;font-size:.94rem}.failure-context code{font-size:.94em}.explanation-block{margin-top:1rem;padding:1rem 1.05rem;border-radius:14px;background:#fffaf4;border:1px solid #e7ddcf}.explanation-block p{margin:.38rem 0 0;color:#383128}.explanation-block code{font-size:.92em}.sticky-facts{margin:.72rem 0 0;padding-left:1.15rem}.sticky-facts li{margin:.24rem 0}.success-list{display:grid;grid-template-columns:repeat(auto-fit,minmax(300px,1fr));gap:.9rem}.success-item{display:flex;align-items:flex-start;gap:.8rem;background:rgba(255,255,255,.82);border:1px solid #e5ddd1;border-radius:16px;padding:1rem 1.05rem}.success-item p{margin:.15rem 0 0;color:#5f5649}.success-summary{margin:.24rem 0 .55rem;color:#5b5248}.success-context{display:flex;flex-wrap:wrap;gap:.42rem .48rem}.success-context .chip{background:#eef4e8;color:#31593a}.trace-shell{margin-top:1rem;padding-top:1rem;border-top:1px solid #e6ddd1}.trace-overview{display:flex;flex-wrap:wrap;gap:.45rem;margin:.1rem 0 .95rem}.trace-frame{display:grid;grid-template-columns:minmax(210px,240px) 1fr;gap:1rem;align-items:start}.trace-nav{display:flex;flex-direction:column;gap:.45rem}.trace-nav button{appearance:none;border:1px solid #e7dfd4;background:rgba(255,255,255,.75);border-radius:12px;padding:.58rem .72rem;text-align:left;cursor:pointer;color:#3c352d;transition:background .12s,border-color .12s}.trace-nav button:hover{background:#fff;border-color:#d6cabc}.trace-nav button.active{background:#f5ede1;border-color:#c9b39c;color:#2b251f}.trace-nav button.loop-step{border-left:4px solid #d9b15c}.trace-nav button.loop-entry{background:#fff5dd;border-color:#d9b15c}.trace-nav .section-label{font-size:.76rem;text-transform:uppercase;letter-spacing:.08em;color:#7b7062;margin:.3rem 0 .12rem}.trace-step-label{font-weight:650}.trace-step-subtitle{display:block;font-size:.86rem;color:#74695d;margin-top:.12rem}.trace-step-badge{display:inline-flex;margin-top:.34rem;background:#f4e0b7;color:#815b11;border-radius:999px;padding:.14rem .42rem;font-size:.74rem}.trace-stage{background:rgba(255,255,255,.88);border:1px solid #e7dfd3;border-radius:16px;padding:1rem 1.05rem}.trace-stage-header{display:flex;justify-content:space-between;align-items:flex-start;gap:1rem;margin-bottom:.8rem}.trace-stage-summary{color:#655b4f;font-size:.92rem;margin-top:.24rem}.trace-controls{display:flex;gap:.45rem}.trace-controls button{appearance:none;border:1px solid #d8ccbe;background:#fff;border-radius:10px;padding:.35rem .65rem;cursor:pointer;color:#3f372f}.trace-controls button:hover{background:#faf7f2}.trace-panel{display:none}.trace-panel.active{display:block}.trace-panel.loop-panel{border-left:4px solid #e3be73;padding-left:.9rem}.trace-eyebrow{font-size:.76rem;text-transform:uppercase;letter-spacing:.08em;color:#756a5e;margin-bottom:.22rem}.trace-event{font-size:1.08rem;font-weight:650}.trace-note{margin:.35rem 0 0;color:#5f5649}.trace-meta{display:flex;flex-wrap:wrap;gap:.4rem;margin:.55rem 0 .35rem}.assignment-section-title{font-size:.82rem;text-transform:uppercase;letter-spacing:.06em;color:#756a5e;margin-top:.8rem}.assignment-list{margin:.55rem 0 0;padding-left:1.2rem}.assignment-list li{margin:.28rem 0}.evidence-card{margin-top:1rem;padding:1rem 1.05rem;border-radius:14px;background:#fffaf4;border:1px solid #e7ddcf}.evidence-card ul{margin:.55rem 0 0;padding-left:1.2rem}.evidence-card li{margin:.24rem 0}.evidence-card pre{margin:.65rem 0 0;white-space:pre-wrap;font:inherit}.relation-states{display:grid;grid-template-columns:repeat(auto-fit,minmax(260px,1fr));gap:.8rem;margin-top:.9rem}.relation-state-card{background:rgba(255,255,255,.7);border:1px solid #e5ddd1;border-radius:14px;padding:.9rem .95rem}.relation-grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(180px,1fr));gap:.65rem;margin-top:.65rem}.relation-card{background:#fff;border:1px solid #e8dfd3;border-radius:12px;padding:.7rem .75rem}.relation-card h5{margin:0 0 .24rem;font-size:.92rem;line-height:1.3}.relation-card p{margin:.18rem 0;color:#5d5448;font-size:.9rem}.relation-card code{font-size:.92em}.relation-evals{margin:.65rem 0 0;padding-left:1.1rem;color:#5d5448}.relation-evals li{margin:.18rem 0}.trace-footer{margin-top:1rem;padding-top:.85rem;border-top:1px solid #e5ddd1}.trace-footer ul{margin:.48rem 0 0;padding-left:1.2rem}.diag-list{margin:0;padding-left:1.2rem}.empty{color:#756a5e;font-style:italic}@media (max-width: 860px){body{padding:1.5rem .9rem 3rem}.trace-frame{grid-template-columns:1fr}.trace-nav{flex-direction:row;overflow:auto;padding-bottom:.25rem}.trace-nav button{min-width:190px}.success-list{grid-template-columns:1fr}.relation-states,.relation-grid{grid-template-columns:1fr}}</style>");
    out.push_str("<script>function jumpToResult(id){const el=document.getElementById(id);if(!el)return;el.scrollIntoView({behavior:'smooth',block:'start'});}function showTraceStep(containerId,panelId){const container=document.getElementById(containerId);if(!container)return;container.querySelectorAll('.trace-panel').forEach((el)=>el.classList.remove('active'));container.querySelectorAll('.trace-nav button').forEach((el)=>el.classList.remove('active'));const panel=container.querySelector('[data-panel=\"'+panelId+'\"]');if(panel)panel.classList.add('active');const button=container.querySelector('[data-target=\"'+panelId+'\"]');if(button)button.classList.add('active');}function stepButtons(container){return Array.from(container.querySelectorAll('.trace-nav button'));}function showAdjacentTraceStep(containerId,delta){const container=document.getElementById(containerId);if(!container)return;const buttons=stepButtons(container);const activeIndex=buttons.findIndex((button)=>button.classList.contains('active'));const start=activeIndex>=0?activeIndex:0;const next=Math.max(0,Math.min(buttons.length-1,start+delta));const target=buttons[next]?.dataset.target;if(target)showTraceStep(containerId,target);}</script>");
    out.push_str("</head><body><main class=\"report-shell\"><header><h1>Verification Report</h1>");
    if failure_indices.is_empty() {
        out.push_str("<p class=\"lede\">All reported verification results completed without a failing witness.</p>");
    } else {
        out.push_str("<p class=\"lede\">");
        out.push_str(&escape_html(&render_html_failure_lede(
            &failure_indices
                .iter()
                .map(|idx| &results[*idx])
                .collect::<Vec<_>>(),
        )));
        out.push_str("</p>");
    }
    out.push_str("<section class=\"summary-grid\">");
    let mut summary_items = vec![
        ("Results", results.len()),
        ("Failures", failure_indices.len()),
    ];
    if proved_count > 0 {
        summary_items.push(("Proved", proved_count));
    }
    if checked_count > 0 {
        summary_items.push(("Checked", checked_count));
    }
    if admitted_count > 0 {
        summary_items.push(("Admitted", admitted_count));
    }
    if !diagnostics.is_empty() {
        summary_items.push(("Diagnostics", diagnostics.len()));
    }
    for (label, value) in summary_items {
        out.push_str("<div class=\"summary-card\"><span class=\"label\">");
        out.push_str(label);
        out.push_str("</span><span class=\"value\">");
        out.push_str(&value.to_string());
        out.push_str("</span></div>");
    }
    out.push_str("</section><div class=\"file-list\">");
    if let Some(files) = report_json
        .get("files")
        .and_then(serde_json::Value::as_array)
    {
        for file in files.iter().filter_map(serde_json::Value::as_str) {
            out.push_str("<span class=\"file-chip\"><code>");
            out.push_str(&escape_html(&display_path(file)));
            out.push_str("</code></span>");
        }
    }
    out.push_str("</div></header>");
    if !failure_indices.is_empty() {
        out.push_str("<section><h2>Failing Results</h2><div class=\"result-stack\">");
        for idx in failure_indices {
            let result = &results[idx];
            out.push_str("<article class=\"result-brief result-failure\" id=\"result-");
            out.push_str(&idx.to_string());
            out.push_str("\"><div>");
            out.push_str(&render_result_verdict_pill(result));
            out.push_str("</div><div class=\"result-body\"><h3>");
            out.push_str(&escape_html(&result_primary_name(result)));
            out.push_str("</h3><p class=\"result-summary\">");
            out.push_str(&escape_html(&result_secondary_summary(result)));
            out.push_str("</p>");
            let metadata = render_result_html_metadata(result);
            if !metadata.is_empty() {
                out.push_str(&metadata);
            }
            let explanation = render_result_html_explanation(result);
            if let Some(ref explanation_html) = explanation {
                out.push_str(explanation_html);
            }
            if explanation.is_none() {
                if let Some(source_note) = render_result_html_source_note(result) {
                    out.push_str(&source_note);
                }
            }
            if let Some(evidence_html) = render_html_evidence(idx, result) {
                out.push_str(&evidence_html);
            }
            out.push_str("</div></article>");
        }
        out.push_str("</div></section>");
    }
    if !success_indices.is_empty() {
        out.push_str("<section><h2>Passing Results</h2><div class=\"success-list\">");
        for idx in success_indices {
            let result = &results[idx];
            out.push_str("<article class=\"success-item\" id=\"result-");
            out.push_str(&idx.to_string());
            out.push_str("\"><div>");
            out.push_str(&render_result_verdict_pill(result));
            out.push_str("</div><div class=\"result-body\"><h3>");
            out.push_str(&escape_html(&result_primary_name(result)));
            out.push_str("</h3><p class=\"success-summary\">");
            out.push_str(&escape_html(&result_secondary_summary(result)));
            out.push_str("</p>");
            let metadata = render_result_html_metadata(result);
            if !metadata.is_empty() {
                out.push_str("<div class=\"success-context\">");
                let metadata = metadata
                    .replace("<div class=\"meta-row\">", "")
                    .replace("</div>", "");
                out.push_str(&metadata);
                out.push_str("</div>");
            } else if let Some(source_note) = render_result_html_source_note(result) {
                out.push_str(&source_note);
            }
            out.push_str("</div></article>");
        }
        out.push_str("</div></section>");
    }
    if !diagnostics.is_empty() {
        out.push_str("<section><h2>Diagnostics</h2>");
        out.push_str("<ul class=\"diag-list\">");
        for diagnostic in diagnostics {
            out.push_str("<li>");
            out.push_str(&escape_html(&diagnostic.to_string()));
            out.push_str("</li>");
        }
        out.push_str("</ul>");
        out.push_str("</section>");
    }
    out.push_str("</main></body></html>");
    out
}

fn render_html_evidence(result_idx: usize, result: &verify::VerificationResult) -> Option<String> {
    if let Some(trace_view) = operational_trace_view(result) {
        return Some(render_operational_trace_html(result_idx, &trace_view));
    }
    let evidence = result.evidence()?;
    match evidence.payload() {
        EvidencePayload::Witness(witness) => match witness.payload() {
            abide_witness::WitnessPayload::Relational(witness) => {
                Some(render_relational_witness_html(witness))
            }
            abide_witness::WitnessPayload::Operational(_) => None,
            _ => None,
        },
        EvidencePayload::Countermodel(countermodel) => {
            (!countermodel.bindings().is_empty()).then(|| render_countermodel_html(countermodel))
        }
        EvidencePayload::ProofArtifactRef(proof_artifact) => {
            Some(render_proof_artifact_html(proof_artifact))
        }
        _ => None,
    }
}

fn escape_html(value: &str) -> String {
    value
        .replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

fn escape_markdown_heading(value: &str) -> String {
    value.replace('\n', " ")
}

fn collapse_inline_whitespace(value: &str) -> String {
    value.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn display_path(path: &str) -> String {
    let path = Path::new(path);
    if path.is_relative() {
        return path.display().to_string();
    }
    if let Ok(cwd) = std::env::current_dir() {
        if let Ok(stripped) = path.strip_prefix(&cwd) {
            return stripped.display().to_string();
        }
    }
    path.display().to_string()
}

fn result_source_excerpt(result: &verify::VerificationResult) -> Option<String> {
    let file = result.file()?;
    let span = result.span()?;
    let source = std::fs::read_to_string(file).ok()?;
    let excerpt = source.get(span.start..span.end)?;
    let collapsed = collapse_inline_whitespace(excerpt.trim());
    (!collapsed.is_empty()).then_some(collapsed)
}

fn result_source_location(result: &verify::VerificationResult) -> Option<String> {
    let file = result.file()?;
    let span = result.span()?;
    let source = std::fs::read_to_string(file).ok()?;
    let start = span.start.min(source.len());
    let prefix = source.get(..start)?;
    let line = prefix.chars().filter(|&c| c == '\n').count() + 1;
    let column = prefix
        .rsplit('\n')
        .next()
        .map_or(1, |line_prefix| line_prefix.chars().count() + 1);
    Some(format!("{}:{}:{}", display_path(file), line, column))
}

fn stable_loop_assignments(loop_steps: &[RenderedTraceStep]) -> Vec<RenderedAssignment> {
    let mut stable = BTreeMap::<(String, String), String>::new();
    let Some(first) = loop_steps.first() else {
        return Vec::new();
    };

    for assignment in &first.assignments {
        stable.insert(
            (assignment.entity.clone(), assignment.field.clone()),
            assignment.value.clone(),
        );
    }

    for step in loop_steps.iter().skip(1) {
        stable.retain(|(entity, field), value| {
            step.assignments.iter().any(|assignment| {
                assignment.entity == *entity
                    && assignment.field == *field
                    && assignment.value == *value
            })
        });
    }

    stable
        .into_iter()
        .map(|((entity, field), value)| RenderedAssignment {
            entity,
            field,
            value,
        })
        .collect()
}

fn rendered_cycle_summary(loop_steps: &[RenderedTraceStep], loop_start: usize) -> Option<String> {
    if loop_steps.is_empty() {
        return None;
    }
    let mut steps = loop_steps
        .iter()
        .map(|step| step.step.to_string())
        .collect::<Vec<_>>();
    steps.push(loop_start.to_string());
    Some(steps.join(" -> "))
}

fn render_markdown_failure_explanation(
    result: &verify::VerificationResult,
) -> Option<(&'static str, String)> {
    match result {
        verify::VerificationResult::LivenessViolation { .. } => Some((
            "Why This Violates The Assertion",
            render_liveness_markdown_explanation(result)?,
        )),
        verify::VerificationResult::Deadlock {
            step,
            reason,
            event_diagnostics,
            ..
        } => {
            let mut out = String::new();
            out.push_str("- The execution reaches step ");
            out.push_str(&step.to_string());
            out.push_str(
                " with no enabled progress step, so it cannot advance beyond that state.\n",
            );
            out.push_str("- Deadlock reason: ");
            out.push_str(reason);
            out.push('\n');
            if !event_diagnostics.is_empty() {
                out.push_str("- Blocked events:\n");
                for diag in event_diagnostics.iter().take(6) {
                    out.push_str("  - `");
                    out.push_str(&diag.system);
                    out.push_str("::");
                    out.push_str(&diag.event);
                    out.push('`');
                    out.push_str(": ");
                    out.push_str(&diag.reason);
                    out.push('\n');
                }
            }
            Some(("Why This Deadlocks", out))
        }
        verify::VerificationResult::Counterexample { .. } => {
            let mut out = String::new();
            if let Some(assertion) = result_source_excerpt(result) {
                out.push_str("- Claim checked: `");
                out.push_str(&assertion);
                out.push_str("`\n");
            }
            match result
                .evidence()
                .map(abide_witness::EvidenceEnvelope::payload)
            {
                Some(EvidencePayload::Countermodel(countermodel)) => {
                    out.push_str(
                        "- The solver produced a concrete assignment that makes this obligation false.\n",
                    );
                    if let Some(summary) = countermodel.summary_text() {
                        out.push_str("- Counterexample shape: ");
                        out.push_str(summary);
                        out.push('\n');
                    }
                    if let Some(backend) = countermodel.backend_name() {
                        out.push_str("- Solver backend: `");
                        out.push_str(backend);
                        out.push_str("`\n");
                    }
                }
                _ => {
                    out.push_str(
                        "- The solver found a concrete violating witness for this obligation.\n",
                    );
                }
            }
            Some(("Why This Fails", out))
        }
        verify::VerificationResult::Unprovable { hint, .. } => {
            let mut out = String::new();
            out.push_str("- The prover could not establish this obligation from the current invariants or reasoning strategy.\n");
            out.push_str("- Backend result: ");
            out.push_str(hint);
            out.push('\n');
            Some(("Why This Is Unprovable", out))
        }
        verify::VerificationResult::SceneFail { reason, .. } => {
            Some(("Why This Scene Fails", format!("- {reason}\n")))
        }
        verify::VerificationResult::FnContractFailed { .. } => {
            let mut out = String::new();
            if let Some(assertion) = result_source_excerpt(result) {
                out.push_str("- Violated contract obligation: `");
                out.push_str(&assertion);
                out.push_str("`\n");
            }
            out.push_str(
                "- The verifier found a violating function execution or proof obligation.\n",
            );
            Some(("Why This Contract Fails", out))
        }
        _ => None,
    }
}

fn render_liveness_markdown_explanation(result: &verify::VerificationResult) -> Option<String> {
    let verify::VerificationResult::LivenessViolation { .. } = result else {
        return None;
    };
    let OperationalTraceView::Lasso {
        loop_steps,
        loop_start,
        ..
    } = operational_trace_view(result)?
    else {
        return None;
    };

    let mut out = String::new();
    if let Some(assertion) = result_source_excerpt(result) {
        out.push_str("- Violated assertion: `");
        out.push_str(&assertion);
        out.push_str("`\n");
    }
    if let Some(cycle) = rendered_cycle_summary(&loop_steps, loop_start) {
        out.push_str("- Repeating cycle: `");
        out.push_str(&cycle);
        out.push_str("`\n");
        out.push_str("- Cycle length: ");
        out.push_str(&loop_steps.len().to_string());
        out.push_str(" steps\n");
    }
    out.push_str("- The execution enters a repeating loop at step ");
    out.push_str(&loop_start.to_string());
    out.push_str(
        ". Any eventual obligation still unmet when the loop begins stays unmet forever.\n",
    );
    let stable = stable_loop_assignments(&loop_steps);
    if !stable.is_empty() {
        out.push_str("- Facts that stay true on every loop iteration:\n");
        for assignment in stable.into_iter().take(6) {
            out.push_str("  - `");
            out.push_str(&assignment.entity);
            out.push('.');
            out.push_str(&assignment.field);
            out.push_str(" = ");
            out.push_str(&assignment.value);
            out.push_str("`\n");
        }
    }
    Some(out)
}

fn render_result_html_explanation(result: &verify::VerificationResult) -> Option<String> {
    match result {
        verify::VerificationResult::LivenessViolation { .. } => {
            Some(render_liveness_html_explanation(result)?)
        }
        verify::VerificationResult::Deadlock {
            step,
            reason,
            event_diagnostics,
            ..
        } => {
            let mut out = String::new();
            out.push_str("<section class=\"explanation-block\"><div class=\"trace-eyebrow\">Why this deadlocks</div>");
            out.push_str("<p>The execution reaches step <strong>");
            out.push_str(&step.to_string());
            out.push_str("</strong> with no enabled progress step, so the run cannot advance beyond this state.</p>");
            out.push_str("<p><strong>Deadlock reason:</strong> ");
            out.push_str(&escape_html(reason));
            out.push_str("</p>");
            if !event_diagnostics.is_empty() {
                out.push_str("<p><strong>Blocked events:</strong></p><ul class=\"sticky-facts\">");
                for diag in event_diagnostics.iter().take(6) {
                    out.push_str("<li><code>");
                    out.push_str(&escape_html(&diag.system));
                    out.push_str("::");
                    out.push_str(&escape_html(&diag.event));
                    out.push_str("</code>: ");
                    out.push_str(&escape_html(&diag.reason));
                    out.push_str("</li>");
                }
                out.push_str("</ul>");
            }
            out.push_str("</section>");
            Some(out)
        }
        verify::VerificationResult::Counterexample { .. } => {
            let mut out = String::new();
            out.push_str("<section class=\"explanation-block\">");
            if matches!(
                result
                    .evidence()
                    .map(abide_witness::EvidenceEnvelope::payload),
                Some(EvidencePayload::Countermodel(_))
            ) {
                out.push_str("<div class=\"trace-eyebrow\">Why this obligation is false</div>");
            } else {
                out.push_str("<div class=\"trace-eyebrow\">Why this fails</div>");
            }
            if let Some(assertion) = result_source_excerpt(result) {
                out.push_str("<p><strong>Claim checked:</strong> <code>");
                out.push_str(&escape_html(&assertion));
                out.push_str("</code></p>");
            }
            match result
                .evidence()
                .map(abide_witness::EvidenceEnvelope::payload)
            {
                Some(EvidencePayload::Countermodel(countermodel)) => {
                    out.push_str(
                        "<p>The solver produced a concrete assignment that makes this obligation false.</p>",
                    );
                    if let Some(summary) = countermodel.summary_text() {
                        out.push_str("<p><strong>Counterexample shape:</strong> ");
                        out.push_str(&escape_html(summary));
                        out.push_str("</p>");
                    }
                    if let Some(backend) = countermodel.backend_name() {
                        out.push_str("<p><strong>Solver backend:</strong> <code>");
                        out.push_str(&escape_html(backend));
                        out.push_str("</code></p>");
                    }
                }
                _ => {
                    out.push_str(
                        "<p>The solver found a concrete violating witness for this obligation.</p>",
                    );
                }
            }
            out.push_str("</section>");
            Some(out)
        }
        verify::VerificationResult::Unprovable { hint, .. } => {
            let mut out = String::new();
            out.push_str("<section class=\"explanation-block\"><div class=\"trace-eyebrow\">Why this is unprovable</div>");
            out.push_str("<p>The prover could not establish this obligation from the current invariants or reasoning strategy.</p>");
            out.push_str("<p><strong>Backend result:</strong> ");
            out.push_str(&escape_html(hint));
            out.push_str("</p></section>");
            Some(out)
        }
        verify::VerificationResult::SceneFail { reason, .. } => {
            let mut out = String::new();
            out.push_str("<section class=\"explanation-block\"><div class=\"trace-eyebrow\">Why this scene fails</div><p>");
            out.push_str(&escape_html(reason));
            out.push_str("</p></section>");
            Some(out)
        }
        verify::VerificationResult::FnContractFailed { .. } => {
            let mut out = String::new();
            out.push_str("<section class=\"explanation-block\"><div class=\"trace-eyebrow\">Why this contract fails</div>");
            if let Some(assertion) = result_source_excerpt(result) {
                out.push_str("<p><strong>Violated contract obligation:</strong> <code>");
                out.push_str(&escape_html(&assertion));
                out.push_str("</code></p>");
            }
            out.push_str("<p>The verifier found a violating function execution or proof obligation.</p></section>");
            Some(out)
        }
        _ => None,
    }
}

fn render_liveness_html_explanation(result: &verify::VerificationResult) -> Option<String> {
    let verify::VerificationResult::LivenessViolation { .. } = result else {
        return None;
    };
    let OperationalTraceView::Lasso {
        loop_steps,
        loop_start,
        ..
    } = operational_trace_view(result)?
    else {
        return None;
    };

    let mut out = String::new();
    out.push_str("<section class=\"explanation-block\"><div class=\"trace-eyebrow\">Why this violates the assertion</div>");
    if let Some(assertion) = result_source_excerpt(result) {
        out.push_str("<p><strong>Violated assertion:</strong> <code>");
        out.push_str(&escape_html(&assertion));
        out.push_str("</code></p>");
    }
    if let Some(cycle) = rendered_cycle_summary(&loop_steps, loop_start) {
        out.push_str("<p><strong>Repeating cycle:</strong> <code>");
        out.push_str(&escape_html(&cycle));
        out.push_str("</code> <span class=\"chip chip-muted\">");
        out.push_str(&loop_steps.len().to_string());
        out.push_str(" step");
        if loop_steps.len() != 1 {
            out.push('s');
        }
        out.push_str("</span></p>");
    }
    out.push_str("<p>The execution enters a repeating loop at step <strong>");
    out.push_str(&loop_start.to_string());
    out.push_str("</strong>. Any eventual obligation still unmet when the loop begins stays unmet forever.</p>");
    let stable = stable_loop_assignments(&loop_steps);
    if !stable.is_empty() {
        out.push_str("<p><strong>Facts that stay true on every loop iteration:</strong></p><ul class=\"sticky-facts\">");
        for assignment in stable.into_iter().take(6) {
            out.push_str("<li><code>");
            out.push_str(&escape_html(&assignment.entity));
            out.push('.');
            out.push_str(&escape_html(&assignment.field));
            out.push_str(" = ");
            out.push_str(&escape_html(&assignment.value));
            out.push_str("</code></li>");
        }
        out.push_str("</ul>");
    }
    out.push_str("</section>");
    Some(out)
}

fn render_markdown_summary_paragraph(result: &verify::VerificationResult) -> String {
    let summary = result_secondary_summary(result);
    let source = result.file().map(display_path);
    match source {
        Some(source) => format!("{summary}  \n_File:_ `{source}`"),
        None => summary,
    }
}

fn render_report_context_details(result: &verify::VerificationResult) -> String {
    let mut lines = Vec::new();
    if let Some(location) = result_source_location(result) {
        lines.push(format!("location: {location}"));
    } else if let Some(file) = result.file() {
        lines.push(format!("file: {}", display_path(file)));
    }
    let assumptions = result.assumptions();
    if !assumptions.is_empty() {
        lines.push(format!(
            "assumptions: {}",
            assumptions
                .iter()
                .map(render_trusted_assumption)
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }
    if let Some(error) = result.evidence_extraction_error() {
        lines.push(format!("evidence extraction: degraded ({error})"));
    }
    if lines.is_empty() {
        if let Some(source_excerpt) = result_source_excerpt(result) {
            lines.push(format!("source: {source_excerpt}"));
        }
    }
    lines.join("\n")
}

fn render_html_failure_lede(results: &[&verify::VerificationResult]) -> String {
    let count = results.len();
    let noun = if count == 1 { "result" } else { "results" };
    let all_operational = results
        .iter()
        .all(|result| operational_trace_view(result).is_some());
    let all_deadlocks = results
        .iter()
        .all(|result| matches!(result, verify::VerificationResult::Deadlock { .. }));
    let all_countermodels = results.iter().all(|result| {
        matches!(
            result
                .evidence()
                .map(abide_witness::EvidenceEnvelope::payload),
            Some(EvidencePayload::Countermodel(_))
        )
    });
    if all_deadlocks {
        return format!(
            "{count} {noun} produced {}. Start with the blocked-state explanation, then inspect the final state only if you need the exact event diagnostics.",
            if count == 1 { "a deadlock" } else { "deadlocks" }
        );
    }
    if all_operational {
        return format!(
            "{count} {noun} produced failing evidence. Start with the failure narrative, then inspect the execution path if you need the exact loop or state changes."
        );
    }
    if all_countermodels {
        return format!(
            "{count} {noun} produced failing evidence. Start with the failure narrative, then inspect the concrete assignment only if you need the exact values that falsify the obligation."
        );
    }
    format!(
        "{count} {noun} produced failing evidence. Start with the failure narrative, then inspect the supporting evidence only if you need the exact states, bindings, or backend details."
    )
}

fn render_result_html_metadata(result: &verify::VerificationResult) -> String {
    let mut out = String::new();
    let mut has_any = false;
    if let Some(location) = result_source_location(result) {
        if !has_any {
            out.push_str("<div class=\"meta-row\">");
            has_any = true;
        }
        out.push_str("<span class=\"chip chip-location\">");
        out.push_str(&escape_html(&location));
        out.push_str("</span>");
    } else if let Some(file) = result.file() {
        if !has_any {
            out.push_str("<div class=\"meta-row\">");
            has_any = true;
        }
        out.push_str("<span class=\"chip chip-location\">");
        out.push_str(&escape_html(&display_path(file)));
        out.push_str("</span>");
    }
    for assumption in result.assumptions() {
        if !has_any {
            out.push_str("<div class=\"meta-row\">");
            has_any = true;
        }
        out.push_str("<span class=\"chip\">");
        out.push_str(&escape_html(&render_trusted_assumption(assumption)));
        out.push_str("</span>");
    }
    if result.evidence_extraction_error().is_some() {
        if !has_any {
            out.push_str("<div class=\"meta-row\">");
            has_any = true;
        }
        out.push_str("<span class=\"chip chip-muted\">evidence degraded</span>");
    }
    if has_any {
        out.push_str("</div>");
    }
    out
}

fn render_result_html_source_note(result: &verify::VerificationResult) -> Option<String> {
    let source_excerpt = result_source_excerpt(result)?;
    let mut out = String::new();
    out.push_str("<p class=\"failure-context\"><strong>Source:</strong> <code>");
    out.push_str(&escape_html(&source_excerpt));
    out.push_str("</code></p>");
    Some(out)
}

fn render_terminal_summary(result: &verify::VerificationResult) -> String {
    format!(
        "{:<8}{} - {}",
        render_result_heading_kind(result),
        result_primary_name(result),
        result_secondary_summary(result)
    )
}

fn render_result_heading(result: &verify::VerificationResult) -> String {
    format!(
        "{} {}",
        render_result_heading_kind(result),
        result_primary_name(result)
    )
}

fn render_result_heading_kind(result: &verify::VerificationResult) -> &'static str {
    match result {
        verify::VerificationResult::Proved { .. } => "PROVED",
        verify::VerificationResult::Checked { .. } => "CHECKED",
        verify::VerificationResult::Admitted { .. } => "ADMITTED",
        verify::VerificationResult::Counterexample { .. } => "COUNTEREXAMPLE",
        verify::VerificationResult::ScenePass { .. } => "PASS",
        verify::VerificationResult::SceneFail { .. } => "SCENE FAIL",
        verify::VerificationResult::Unprovable { .. } => "UNPROVABLE",
        verify::VerificationResult::FnContractProved { .. } => "PROVED",
        verify::VerificationResult::FnContractAdmitted { .. } => "ADMITTED",
        verify::VerificationResult::FnContractFailed { .. } => "FAILED",
        verify::VerificationResult::LivenessViolation { .. } => "LIVENESS VIOLATION",
        verify::VerificationResult::Deadlock { .. } => "DEADLOCK",
    }
}

fn render_result_human_text(result: &verify::VerificationResult, art: TextArt) -> Option<String> {
    if let Some(trace) = operational_trace_view(result) {
        return Some(render_operational_trace_text(result, &trace, art));
    }
    let evidence = result.evidence()?;
    match evidence.payload() {
        EvidencePayload::Witness(witness) => match witness.payload() {
            abide_witness::WitnessPayload::Relational(witness) => {
                Some(render_relational_witness_text(witness))
            }
            abide_witness::WitnessPayload::Operational(_) => None,
            _ => None,
        },
        EvidencePayload::Countermodel(countermodel) => Some(render_countermodel_text(countermodel)),
        EvidencePayload::ProofArtifactRef(proof_artifact) => {
            Some(render_proof_artifact_text(proof_artifact))
        }
        _ => None,
    }
}

fn render_markdown_relational_evidence(witness: &rel::RelationalWitness) -> String {
    let mut out = String::new();
    out.push_str("##### Evidence\n\n");
    match witness {
        rel::RelationalWitness::Snapshot(state) => {
            out.push_str("- Kind: relational snapshot\n");
            out.push_str("- Relations: ");
            out.push_str(&state.relation_instances().len().to_string());
            out.push('\n');
            out.push_str("- Evaluations: ");
            out.push_str(&state.evaluations().len().to_string());
            out.push('\n');
            render_markdown_relational_state_preview(&mut out, state, "Snapshot");
        }
        rel::RelationalWitness::Temporal(temporal) => {
            out.push_str("- Kind: temporal relational witness\n");
            out.push_str("- States: ");
            out.push_str(&temporal.states().len().to_string());
            out.push('\n');
            if let Some(loop_start) = temporal.loop_start() {
                out.push_str("- Repeating cycle starts at state ");
                out.push_str(&loop_start.to_string());
                out.push('\n');
            }
            for (idx, state) in temporal.states().iter().enumerate().take(4) {
                render_markdown_relational_state_preview(&mut out, state, &format!("State {idx}"));
            }
        }
    }
    out.push('\n');
    out
}

fn render_markdown_relational_state_preview(
    out: &mut String,
    state: &rel::RelationalState,
    label: &str,
) {
    out.push_str("\n###### ");
    out.push_str(label);
    out.push_str("\n\n");
    out.push_str("| Relation | Tuples | Sample |\n");
    out.push_str("| --- | ---: | --- |\n");
    for relation in state.relation_instances().iter().take(4) {
        out.push_str("| `");
        out.push_str(&render_relation_id(relation.id()));
        out.push_str("` | ");
        out.push_str(&relation.relation().tuples().len().to_string());
        out.push_str(" | ");
        if let Some(first_tuple) = relation.relation().tuples().first() {
            out.push('`');
            out.push_str(&render_tuple_value(first_tuple));
            out.push('`');
        } else {
            out.push('—');
        }
        out.push_str(" |\n");
    }
    if !state.evaluations().is_empty() {
        out.push_str("\nEvaluations:\n");
        for (name, value) in state.evaluations().iter().take(4) {
            out.push_str("- `");
            out.push_str(name);
            out.push_str(" = ");
            out.push_str(&render_witness_value(value));
            out.push_str("`\n");
        }
    }
    out.push('\n');
}

fn render_markdown_countermodel_evidence(countermodel: &abide_witness::Countermodel) -> String {
    let mut out = String::new();
    out.push_str("##### Evidence\n\n- Kind: countermodel\n");
    if let Some(backend) = countermodel.backend_name() {
        out.push_str("- Backend: `");
        out.push_str(backend);
        out.push_str("`\n");
    }
    if let Some(summary) = countermodel.summary_text() {
        out.push_str("- Summary: ");
        out.push_str(summary);
        out.push('\n');
    }
    if countermodel.bindings().is_empty() {
        out.push_str("- Bindings: none\n\n");
        return out;
    }
    out.push_str("- Bindings:\n");
    for binding in countermodel.bindings().iter().take(8) {
        out.push_str("  - `");
        out.push_str(binding.name());
        out.push_str(" = ");
        out.push_str(&render_witness_value(binding.value()));
        out.push_str("`\n");
    }
    out.push('\n');
    out
}

fn render_markdown_proof_artifact_evidence(
    proof_artifact: &abide_witness::ProofArtifactRef,
) -> String {
    let mut out = String::new();
    out.push_str("##### Evidence\n\n- Kind: proof artifact\n");
    out.push_str("- Locator: `");
    out.push_str(proof_artifact.locator());
    out.push_str("`\n");
    if let Some(label) = proof_artifact.label_text() {
        out.push_str("- Label: ");
        out.push_str(label);
        out.push('\n');
    }
    if let Some(backend) = proof_artifact.backend_name() {
        out.push_str("- Backend: `");
        out.push_str(backend);
        out.push_str("`\n");
    }
    out.push_str("- Checked: ");
    out.push_str(if proof_artifact.is_checked() {
        "yes"
    } else {
        "no"
    });
    out.push_str("\n\n");
    out
}

fn render_operational_trace_text(
    result: &verify::VerificationResult,
    trace: &OperationalTraceView,
    art: TextArt,
) -> String {
    let mut lines = Vec::new();
    lines.push("Execution witness".to_owned());

    match trace {
        OperationalTraceView::Linear { steps } => {
            lines.push(format!("{} Behavior", art.elbow()));
            lines.push(format!(
                "{} {} {} step{}",
                indent_with_art(2, art),
                art.elbow(),
                steps.len(),
                if steps.len() == 1 { "" } else { "s" }
            ));
            lines.extend(render_trace_section_lines(steps, 2, art));
        }
        OperationalTraceView::Deadlock {
            steps,
            deadlock_step,
            reason,
            event_diagnostics,
        } => {
            lines.push(format!("{} Behavior", art.branch()));
            lines.push(format!(
                "{} {} {} step{} before deadlock",
                indent_with_art(2, art),
                art.branch(),
                steps.len(),
                if steps.len() == 1 { "" } else { "s" }
            ));
            lines.extend(render_trace_section_lines(steps, 2, art));
            lines.push(format!(
                "{} Deadlock at step {}: {}",
                art.branch(),
                deadlock_step,
                reason
            ));
            if !event_diagnostics.is_empty() {
                lines.push(format!("{} Blocked events", art.elbow()));
                for (idx, diag) in event_diagnostics.iter().enumerate() {
                    let branch = if idx + 1 == event_diagnostics.len() {
                        art.elbow()
                    } else {
                        art.branch()
                    };
                    lines.push(format!(
                        "  {branch} {}::{}: {}",
                        diag.system, diag.event, diag.reason
                    ));
                }
            }
        }
        OperationalTraceView::Lasso {
            prefix,
            loop_steps,
            loop_start,
            fairness,
        } => {
            let mut root_items = 1usize;
            if !prefix.is_empty() {
                root_items += 1;
            }
            if !fairness.is_empty() {
                root_items += 1;
            }
            let mut root_index = 0usize;
            if !prefix.is_empty() {
                root_index += 1;
                let branch = if root_index == root_items {
                    art.elbow()
                } else {
                    art.branch()
                };
                lines.push(format!("{branch} Lead-in"));
                lines.extend(render_trace_section_lines(prefix, 2, art));
            }
            root_index += 1;
            let cycle_branch = if root_index == root_items {
                art.elbow()
            } else {
                art.branch()
            };
            lines.push(format!("{cycle_branch} Repeating cycle"));
            if let Some(cycle) = rendered_cycle_summary(loop_steps, *loop_start) {
                lines.push(format!(
                    "{} {} {}",
                    indent_with_art(2, art),
                    art.branch(),
                    cycle
                ));
            }
            lines.push(format!(
                "{} {} {} step{}",
                indent_with_art(2, art),
                if loop_steps.is_empty() {
                    art.elbow()
                } else {
                    art.branch()
                },
                loop_steps.len(),
                if loop_steps.len() == 1 { "" } else { "s" }
            ));
            if let verify::VerificationResult::LivenessViolation { .. } = result {
                lines.push(format!(
                    "{} {} execution becomes permanently cyclic at step {}",
                    indent_with_art(2, art),
                    art.branch(),
                    loop_start
                ));
            }
            let stable = stable_loop_assignments(loop_steps);
            if !stable.is_empty() {
                lines.push(format!(
                    "{} {} persistent loop facts",
                    indent_with_art(2, art),
                    if loop_steps.is_empty() {
                        art.elbow()
                    } else {
                        art.branch()
                    }
                ));
                for (idx, assignment) in stable.iter().take(6).enumerate() {
                    let branch = if idx + 1 == stable.len().min(6) {
                        art.elbow()
                    } else {
                        art.branch()
                    };
                    lines.push(format!(
                        "{}{} {}.{} = {}",
                        indent_with_art(4, art),
                        branch,
                        assignment.entity,
                        assignment.field,
                        assignment.value
                    ));
                }
            }
            lines.push(format!("{} {}", indent_with_art(2, art), art.elbow()));
            let last_index = lines.len() - 1;
            lines[last_index].push_str(" cycle steps");
            lines.extend(render_trace_section_lines(loop_steps, 4, art));
            if !fairness.is_empty() {
                root_index += 1;
                let fairness_branch = if root_index == root_items {
                    art.elbow()
                } else {
                    art.branch()
                };
                lines.push(format!("{fairness_branch} Fairness"));
                for (idx, entry) in fairness.iter().enumerate() {
                    let branch = if idx + 1 == fairness.len() {
                        art.elbow()
                    } else {
                        art.branch()
                    };
                    lines.push(format!(
                        "  {branch} {} {}::{}: {}",
                        entry.kind, entry.system, entry.event, entry.status
                    ));
                }
            }
        }
    }

    lines.join("\n")
}

fn render_trace_section_lines(
    steps: &[RenderedTraceStep],
    indent: usize,
    art: TextArt,
) -> Vec<String> {
    let mut lines = Vec::new();
    for (step_idx, step) in steps.iter().enumerate() {
        let is_last_step = step_idx + 1 == steps.len();
        let branch = if is_last_step {
            art.elbow()
        } else {
            art.branch()
        };
        lines.push(format!(
            "{}{} step {}: {}",
            indent_spaces(indent),
            branch,
            step.step,
            render_trace_step_label(step)
        ));
        if step.assignments.is_empty() && step.changes.is_empty() && step.observations.is_empty() {
            continue;
        }
        let child_indent = format!(
            "{}{}  ",
            indent_spaces(indent),
            if is_last_step { " " } else { art.vertical() }
        );
        if !step.changes.is_empty() {
            for (change_idx, change) in step.changes.iter().enumerate() {
                let change_branch =
                    if change_idx + 1 == step.changes.len() && step.observations.is_empty() {
                        art.elbow()
                    } else {
                        art.branch()
                    };
                lines.push(format!(
                    "{child_indent}{change_branch} {}",
                    render_trace_change_text(change)
                ));
            }
        }
        if step.changes.is_empty() && !step.assignments.is_empty() {
            for (assignment_idx, assignment) in step.assignments.iter().enumerate() {
                let assign_branch = if assignment_idx + 1 == step.assignments.len()
                    && step.observations.is_empty()
                {
                    art.elbow()
                } else {
                    art.branch()
                };
                lines.push(format!(
                    "{child_indent}{assign_branch} {}.{} = {}",
                    assignment.entity, assignment.field, assignment.value
                ));
            }
        }
        if !step.observations.is_empty() {
            for (obs_idx, observation) in step.observations.iter().enumerate() {
                let obs_branch = if obs_idx + 1 == step.observations.len() {
                    art.elbow()
                } else {
                    art.branch()
                };
                lines.push(format!(
                    "{child_indent}{obs_branch} {}",
                    render_trace_observation_text(observation)
                ));
            }
        }
    }
    lines
}

fn render_trace_change_text(change: &RenderedTraceChange) -> String {
    let target = format!("{}.{}", change.entity, change.field);
    match (&change.before, &change.after) {
        (Some(before), Some(after)) => format!("{target}: {before} -> {after}"),
        (None, Some(after)) => format!("{target}: <absent> -> {after}"),
        (Some(before), None) => format!("{target}: {before} -> <absent>"),
        (None, None) => format!("{target}: <absent> -> <absent>"),
    }
}

fn render_trace_observation_text(observation: &RenderedTraceObservation) -> String {
    if observation.name == "saw" {
        format!("observed {}", observation.value)
    } else if observation.value == "true" {
        observation.name.clone()
    } else {
        format!("{} = {}", observation.name, observation.value)
    }
}

fn render_trace_step_label(step: &RenderedTraceStep) -> String {
    match (&step.event, step.step) {
        (Some(event), _) => format!("event {event}"),
        (None, 0) => "initial".to_owned(),
        (None, _) => "stutter".to_owned(),
    }
}

fn indent_spaces(indent: usize) -> String {
    " ".repeat(indent)
}

fn indent_with_art(indent: usize, art: TextArt) -> String {
    let unit = format!("{} ", art.vertical());
    unit.repeat(indent / 2)
}

fn render_relational_witness_text(witness: &rel::RelationalWitness) -> String {
    match witness {
        rel::RelationalWitness::Snapshot(state) => {
            let mut lines = Vec::new();
            lines.push("Relational witness".to_owned());
            lines.push("├─ Snapshot".to_owned());
            lines.push(format!(
                "├─ {} relation{}, {} evaluation{}",
                state.relation_instances().len(),
                if state.relation_instances().len() == 1 {
                    ""
                } else {
                    "s"
                },
                state.evaluations().len(),
                if state.evaluations().len() == 1 {
                    ""
                } else {
                    "s"
                }
            ));
            lines.extend(render_relational_state_preview_lines(state, 0, true));
            lines.join("\n")
        }
        rel::RelationalWitness::Temporal(temporal) => {
            let mut lines = Vec::new();
            lines.push("Relational witness".to_owned());
            lines.push(format!(
                "├─ {} state{}",
                temporal.states().len(),
                if temporal.states().len() == 1 {
                    ""
                } else {
                    "s"
                }
            ));
            if let Some(loop_start) = temporal.loop_start() {
                lines.push(format!("├─ repeating cycle starts at state {loop_start}"));
            }
            for (idx, state) in temporal.states().iter().enumerate().take(6) {
                let branch = if idx + 1 == temporal.states().len().min(6) {
                    "└─"
                } else {
                    "├─"
                };
                lines.push(format!(
                    "{branch} state {}: {} relation{}, {} evaluation{}",
                    idx,
                    state.relation_instances().len(),
                    if state.relation_instances().len() == 1 {
                        ""
                    } else {
                        "s"
                    },
                    state.evaluations().len(),
                    if state.evaluations().len() == 1 {
                        ""
                    } else {
                        "s"
                    }
                ));
                lines.extend(
                    render_relational_state_preview_lines(
                        state,
                        2,
                        idx + 1 == temporal.states().len().min(6),
                    )
                    .into_iter()
                    .take(5),
                );
            }
            if temporal.states().len() > 6 {
                lines.push(format!("└─ +{} more states", temporal.states().len() - 6));
            }
            lines.join("\n")
        }
    }
}

fn render_relational_witness_html(witness: &rel::RelationalWitness) -> String {
    let mut out = String::new();
    out.push_str("<section class=\"evidence-card\"><div class=\"trace-eyebrow\">Evidence</div><h4>Relational witness</h4>");
    match witness {
        rel::RelationalWitness::Snapshot(state) => {
            out.push_str("<p class=\"trace-note\">Snapshot witness with <strong>");
            out.push_str(&state.relation_instances().len().to_string());
            out.push_str("</strong> relations and <strong>");
            out.push_str(&state.evaluations().len().to_string());
            out.push_str("</strong> evaluations.</p>");
            out.push_str("<div class=\"relation-states\">");
            out.push_str(&render_relational_state_html(state, Some("Snapshot")));
            out.push_str("</div>");
        }
        rel::RelationalWitness::Temporal(temporal) => {
            out.push_str("<div class=\"trace-overview\"><span class=\"chip chip-muted\">");
            out.push_str(&temporal.states().len().to_string());
            out.push_str(" state");
            if temporal.states().len() != 1 {
                out.push('s');
            }
            out.push_str("</span>");
            if let Some(loop_start) = temporal.loop_start() {
                out.push_str("<span class=\"chip chip-cycle\">cycle starts at state ");
                out.push_str(&loop_start.to_string());
                out.push_str("</span>");
            }
            out.push_str("</div><div class=\"relation-states\">");
            for (idx, state) in temporal.states().iter().enumerate().take(4) {
                out.push_str(&render_relational_state_html(
                    state,
                    Some(&format!("State {idx}")),
                ));
            }
            out.push_str("</div>");
        }
    }
    out.push_str("</section>");
    out
}

fn render_relational_state_html(state: &rel::RelationalState, heading: Option<&str>) -> String {
    let mut out = String::new();
    out.push_str("<section class=\"relation-state-card\">");
    if let Some(heading) = heading {
        out.push_str("<div class=\"trace-eyebrow\">");
        out.push_str(&escape_html(heading));
        out.push_str("</div>");
    }
    out.push_str("<div class=\"relation-grid\">");
    for relation in state.relation_instances().iter().take(4) {
        out.push_str("<article class=\"relation-card\"><h5><code>");
        out.push_str(&escape_html(&render_relation_id(relation.id())));
        out.push_str("</code></h5><p>");
        out.push_str(&relation.relation().tuples().len().to_string());
        out.push_str(" tuple");
        if relation.relation().tuples().len() != 1 {
            out.push('s');
        }
        out.push_str("</p>");
        if let Some(first_tuple) = relation.relation().tuples().first() {
            out.push_str("<p>sample <code>");
            out.push_str(&escape_html(&render_tuple_value(first_tuple)));
            out.push_str("</code>");
        } else {
            out.push_str("<p class=\"empty\">no tuples recorded");
        }
        out.push_str("</p></article>");
    }
    out.push_str("</div>");
    if !state.evaluations().is_empty() {
        out.push_str("<ul class=\"relation-evals\">");
        for (name, value) in state.evaluations().iter().take(4) {
            out.push_str("<li><code>");
            out.push_str(&escape_html(name));
            out.push_str(" = ");
            out.push_str(&escape_html(&render_witness_value(value)));
            out.push_str("</code></li>");
        }
        out.push_str("</ul>");
    }
    out.push_str("</section>");
    out
}

fn render_relational_state_preview_lines(
    state: &rel::RelationalState,
    indent: usize,
    terminal_branch_only: bool,
) -> Vec<String> {
    let mut lines = Vec::new();
    let relation_limit = 4usize;
    for (idx, relation) in state
        .relation_instances()
        .iter()
        .take(relation_limit)
        .enumerate()
    {
        let branch = if idx + 1 == state.relation_instances().len().min(relation_limit)
            && state.evaluations().is_empty()
            && terminal_branch_only
        {
            "└─"
        } else {
            "├─"
        };
        lines.push(format!(
            "{}{} {} (arity {}, {} tuple{})",
            indent_spaces(indent),
            branch,
            render_relation_id(relation.id()),
            relation.relation().arity(),
            relation.relation().tuples().len(),
            if relation.relation().tuples().len() == 1 {
                ""
            } else {
                "s"
            }
        ));
        if let Some(first_tuple) = relation.relation().tuples().first() {
            lines.push(format!(
                "{}  └─ sample: {}",
                indent_spaces(indent),
                render_tuple_value(first_tuple)
            ));
        }
    }
    if state.relation_instances().len() > relation_limit {
        lines.push(format!(
            "{}├─ +{} more relation{}",
            indent_spaces(indent),
            state.relation_instances().len() - relation_limit,
            if state.relation_instances().len() - relation_limit == 1 {
                ""
            } else {
                "s"
            }
        ));
    }
    if !state.evaluations().is_empty() {
        lines.push(format!(
            "{}└─ evaluations: {}",
            indent_spaces(indent),
            state
                .evaluations()
                .iter()
                .take(4)
                .map(|(name, value)| format!("{name} = {}", render_witness_value(value)))
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }
    lines
}

fn render_relation_id(id: &rel::RelationId) -> String {
    match id {
        rel::RelationId::StoreExtent { store } => format!("store {store}"),
        rel::RelationId::Field { owner, field } => format!("{owner}.{field}"),
        rel::RelationId::Named { name } => name.clone(),
        rel::RelationId::Derived { name } => format!("derived {name}"),
    }
}

fn render_tuple_value(tuple: &rel::TupleValue) -> String {
    tuple
        .values()
        .iter()
        .map(render_witness_value)
        .collect::<Vec<_>>()
        .join(", ")
}

fn render_countermodel_text(countermodel: &abide_witness::Countermodel) -> String {
    let mut lines = Vec::new();
    lines.push("Countermodel".to_owned());
    if let Some(backend) = countermodel.backend_name() {
        lines.push(format!("├─ backend: {backend}"));
    }
    if let Some(summary) = countermodel.summary_text() {
        lines.push(format!("├─ summary: {summary}"));
    }
    if countermodel.bindings().is_empty() {
        lines.push("└─ no explicit bindings".to_owned());
    } else {
        lines.push("├─ bindings".to_owned());
        for (idx, binding) in countermodel.bindings().iter().take(8).enumerate() {
            let branch = if idx + 1 == countermodel.bindings().len() {
                "└─"
            } else {
                "├─"
            };
            lines.push(format!(
                "  {branch} {} = {}",
                binding.name(),
                render_witness_value(binding.value())
            ));
        }
        if countermodel.bindings().len() > 8 {
            lines.push(format!(
                "  └─ +{} more bindings",
                countermodel.bindings().len() - 8
            ));
        }
    }
    lines.join("\n")
}

fn render_countermodel_html(countermodel: &abide_witness::Countermodel) -> String {
    let mut out = String::new();
    out.push_str("<section class=\"evidence-card\"><div class=\"trace-eyebrow\">Countermodel</div><h4>Concrete failing assignment</h4>");
    if let Some(summary) = countermodel.summary_text() {
        out.push_str("<p class=\"trace-note\">");
        out.push_str(&escape_html(summary));
        out.push_str("</p>");
    }
    if let Some(backend) = countermodel.backend_name() {
        out.push_str("<div class=\"meta-row\"><span class=\"chip chip-muted\">backend ");
        out.push_str(&escape_html(backend));
        out.push_str("</span></div>");
    }
    out.push_str("<ul>");
    if countermodel.bindings().is_empty() {
        out.push_str(
            "<li class=\"empty\">No concrete bindings were recorded for this countermodel.</li>",
        );
    }
    for binding in countermodel.bindings().iter().take(8) {
        out.push_str("<li><code>");
        out.push_str(&escape_html(binding.name()));
        out.push_str(" = ");
        out.push_str(&escape_html(&render_witness_value(binding.value())));
        out.push_str("</code></li>");
    }
    out.push_str("</ul></section>");
    out
}

fn render_proof_artifact_text(proof_artifact: &abide_witness::ProofArtifactRef) -> String {
    let mut lines = Vec::new();
    lines.push("Proof artifact".to_owned());
    lines.push(format!("├─ locator: {}", proof_artifact.locator()));
    if let Some(label) = proof_artifact.label_text() {
        lines.push(format!("├─ label: {label}"));
    }
    if let Some(backend) = proof_artifact.backend_name() {
        lines.push(format!("├─ backend: {backend}"));
    }
    lines.push(format!(
        "└─ checked: {}",
        if proof_artifact.is_checked() {
            "yes"
        } else {
            "no"
        }
    ));
    lines.join("\n")
}

fn render_proof_artifact_html(proof_artifact: &abide_witness::ProofArtifactRef) -> String {
    let mut out = String::new();
    out.push_str("<section class=\"evidence-card\"><div class=\"trace-eyebrow\">Proof artifact</div><h4>External proof reference</h4><p class=\"trace-note\">This result is backed by an external proof artifact rather than a native execution witness.</p><ul>");
    out.push_str("<li>locator: <code>");
    out.push_str(&escape_html(proof_artifact.locator()));
    out.push_str("</code></li>");
    if let Some(label) = proof_artifact.label_text() {
        out.push_str("<li>label: ");
        out.push_str(&escape_html(label));
        out.push_str("</li>");
    }
    if let Some(backend) = proof_artifact.backend_name() {
        out.push_str("<li>backend: <code>");
        out.push_str(&escape_html(backend));
        out.push_str("</code></li>");
    }
    out.push_str("<li>checked: ");
    out.push_str(if proof_artifact.is_checked() {
        "yes"
    } else {
        "no"
    });
    out.push_str("</li></ul></section>");
    out
}

fn render_result_verbose_details(
    result: &verify::VerificationResult,
    include_human_view: bool,
) -> String {
    let mut lines = Vec::new();
    if let Some(location) = result_source_location(result) {
        lines.push(format!("location: {location}"));
    } else if let Some(file) = result.file() {
        lines.push(format!("file: {}", display_path(file)));
    }
    if let Some(source_excerpt) = result_source_excerpt(result) {
        lines.push(format!("source: {source_excerpt}"));
    }
    let assumptions = result.assumptions();
    if !assumptions.is_empty() {
        lines.push(format!(
            "assumptions: {}",
            assumptions
                .iter()
                .map(render_trusted_assumption)
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }
    if let Some(evidence) = result.evidence() {
        let kind = match evidence.payload() {
            abide_witness::EvidencePayload::Witness(witness) => match witness.payload() {
                abide_witness::WitnessPayload::Operational(_) => "operational witness",
                abide_witness::WitnessPayload::Relational(_) => "relational witness",
                _ => "unknown witness",
            },
            abide_witness::EvidencePayload::Countermodel(_) => "countermodel",
            abide_witness::EvidencePayload::ProofArtifactRef(_) => "proof artifact",
            _ => "unknown evidence",
        };
        lines.push(format!("evidence: {kind}"));
    }
    if include_human_view {
        if let Some(human_text) = render_result_human_text(result, terminal_text_art()) {
            lines.push("evidence view:".to_owned());
            lines.extend(human_text.lines().map(|line| format!("  {line}")));
        }
    }
    lines.join("\n")
}

fn report_result_verbose_details(result: &verify::VerificationResult, failure_stream: bool) {
    let heading = render_result_heading(result);
    let summary = result_secondary_summary(result);
    let details = render_result_verbose_details(result, false);
    let human_evidence = render_result_human_text(result, terminal_text_art());
    let mut lines = vec![heading, format!("summary: {summary}")];
    if !details.is_empty() {
        lines.push("context:".to_owned());
        lines.extend(details.lines().map(|line| format!("  - {line}")));
    }
    if let Some(human_evidence) = human_evidence {
        lines.push("evidence:".to_owned());
        lines.extend(human_evidence.lines().map(|line| format!("  {line}")));
    }
    let output = lines.join("\n");
    if failure_stream {
        for line in output.lines() {
            eprintln!("  {line}");
        }
    } else {
        for line in output.lines() {
            println!("  {line}");
        }
    }
}

fn render_trusted_assumption(assumption: &verify::TrustedAssumption) -> String {
    match assumption {
        verify::TrustedAssumption::Stutter => "stutter".to_owned(),
        verify::TrustedAssumption::WeakFairness { system, command } => {
            format!("WF {system}::{command}")
        }
        verify::TrustedAssumption::StrongFairness { system, command } => {
            format!("SF {system}::{command}")
        }
        verify::TrustedAssumption::Lemma { name } => format!("lemma {name}"),
        verify::TrustedAssumption::Axiom {
            name,
            proof_artifact,
        } => {
            if let Some(proof_artifact) = proof_artifact {
                format!("axiom {name} (artifact: {})", proof_artifact.locator())
            } else {
                format!("axiom {name}")
            }
        }
        verify::TrustedAssumption::ExternAssume { external, detail } => {
            format!("extern {external} {detail}")
        }
    }
}

fn render_operational_trace_html(result_idx: usize, trace: &OperationalTraceView) -> String {
    let mut out = String::new();
    let trace_id = format!("trace-{result_idx}");
    let (trace_heading, trace_summary) = match trace {
        OperationalTraceView::Deadlock { .. } => (
            "Blocked state",
            "Inspect the blocked state and the event diagnostics that keep this run from advancing.",
        ),
        _ => (
            "Execution path",
            "Select a step to inspect the state facts recorded at that point in the witness.",
        ),
    };
    out.push_str("<section class=\"trace-shell\" id=\"");
    out.push_str(&trace_id);
    out.push_str("\">");
    out.push_str(&render_trace_overview_html(trace));
    if let Some(step) = single_step_operational_trace(trace) {
        out.push_str(
            "<div class=\"trace-stage-header\"><div><div class=\"trace-eyebrow\">Execution witness</div><h4>",
        );
        out.push_str(trace_heading);
        out.push_str("</h4><div class=\"trace-stage-summary\">");
        out.push_str(trace_summary);
        out.push_str("</div></div></div><div class=\"trace-stage\">");
        render_trace_panel_html(&mut out, step, true, false);
        render_trace_footer_html(&mut out, trace);
        out.push_str("</div></section>");
        return out;
    }
    let initial_panel_id = match trace {
        OperationalTraceView::Lasso { loop_start, .. } => format!("step-{loop_start}"),
        _ => "step-0".to_owned(),
    };
    out.push_str(
        "<div class=\"trace-stage-header\"><div><div class=\"trace-eyebrow\">Execution witness</div><h4>",
    );
    out.push_str(trace_heading);
    out.push_str("</h4><div class=\"trace-stage-summary\">");
    out.push_str(trace_summary);
    out.push_str(
        "</div></div><div class=\"trace-controls\"><button type=\"button\" onclick=\"showAdjacentTraceStep('",
    );
    out.push_str(&trace_id);
    out.push_str(
        "', -1)\">Previous</button><button type=\"button\" onclick=\"showAdjacentTraceStep('",
    );
    out.push_str(&trace_id);
    out.push_str(
        "', 1)\">Next</button></div></div><div class=\"trace-frame\"><nav class=\"trace-nav\">",
    );
    match trace {
        OperationalTraceView::Linear { steps } | OperationalTraceView::Deadlock { steps, .. } => {
            out.push_str("<div class=\"section-label\">Behavior</div>");
            for step in steps {
                let panel_id = format!("step-{}", step.step);
                let badge = match trace {
                    OperationalTraceView::Deadlock { deadlock_step, .. }
                        if step.step == *deadlock_step =>
                    {
                        Some("blocked")
                    }
                    _ => None,
                };
                render_trace_step_button(&mut out, &trace_id, &panel_id, step, badge, false, false);
            }
        }
        OperationalTraceView::Lasso {
            prefix,
            loop_steps,
            loop_start,
            ..
        } => {
            if !prefix.is_empty() {
                out.push_str("<div class=\"section-label\">Lead-in</div>");
            }
            for step in prefix {
                let panel_id = format!("step-{}", step.step);
                render_trace_step_button(&mut out, &trace_id, &panel_id, step, None, false, false);
            }
            if !loop_steps.is_empty() {
                out.push_str("<div class=\"section-label\">Cycle</div>");
            }
            for step in loop_steps {
                let panel_id = format!("step-{}", step.step);
                let badge = if step.step == *loop_start {
                    Some("loop start")
                } else {
                    Some("loop")
                };
                render_trace_step_button(
                    &mut out,
                    &trace_id,
                    &panel_id,
                    step,
                    badge,
                    step.step >= *loop_start,
                    step.step == *loop_start,
                );
            }
        }
    }
    out.push_str("</nav><div class=\"trace-stage\">");
    match trace {
        OperationalTraceView::Linear { steps } | OperationalTraceView::Deadlock { steps, .. } => {
            for (idx, step) in steps.iter().enumerate() {
                render_trace_panel_html(&mut out, step, idx == 0, false);
            }
        }
        OperationalTraceView::Lasso {
            prefix,
            loop_steps,
            loop_start,
            ..
        } => {
            for (idx, step) in prefix.iter().enumerate() {
                render_trace_panel_html(&mut out, step, idx == 0, false);
            }
            let start_index = prefix.len();
            for (offset, step) in loop_steps.iter().enumerate() {
                render_trace_panel_html(
                    &mut out,
                    step,
                    start_index + offset == 0,
                    step.step >= *loop_start,
                );
            }
        }
    }
    render_trace_footer_html(&mut out, trace);
    out.push_str("</div></div></section><script>showTraceStep('");
    out.push_str(&trace_id);
    out.push_str("','");
    out.push_str(&initial_panel_id);
    out.push_str("');</script>");
    out
}

fn single_step_operational_trace(trace: &OperationalTraceView) -> Option<&RenderedTraceStep> {
    match trace {
        OperationalTraceView::Linear { steps } | OperationalTraceView::Deadlock { steps, .. }
            if steps.len() == 1 =>
        {
            steps.first()
        }
        _ => None,
    }
}

fn render_trace_footer_html(out: &mut String, trace: &OperationalTraceView) {
    match trace {
        OperationalTraceView::Lasso { fairness, .. } if !fairness.is_empty() => {
            out.push_str(
                "<div class=\"trace-footer\"><div class=\"trace-eyebrow\">Fairness</div><ul>",
            );
            for entry in fairness {
                out.push_str("<li>");
                out.push_str(&escape_html(&format!(
                    "{} {}::{}: {}",
                    entry.kind, entry.system, entry.event, entry.status
                )));
                out.push_str("</li>");
            }
            out.push_str("</ul></div>");
        }
        OperationalTraceView::Deadlock {
            deadlock_step,
            reason,
            event_diagnostics,
            ..
        } => {
            out.push_str("<div class=\"trace-footer\"><div class=\"trace-eyebrow\">Deadlock</div><p class=\"trace-note\">");
            out.push_str(&escape_html(&format!(
                "No events enabled at step {deadlock_step}: {reason}"
            )));
            out.push_str("</p>");
            if !event_diagnostics.is_empty() {
                out.push_str("<ul>");
                for diag in event_diagnostics {
                    out.push_str("<li>");
                    out.push_str(&escape_html(&format!(
                        "{}::{}: {}",
                        diag.system, diag.event, diag.reason
                    )));
                    out.push_str("</li>");
                }
                out.push_str("</ul>");
            }
            out.push_str("</div>");
        }
        _ => {}
    }
}

fn render_trace_overview_html(trace: &OperationalTraceView) -> String {
    let mut out = String::new();
    out.push_str("<div class=\"trace-overview\">");
    match trace {
        OperationalTraceView::Linear { steps } => {
            out.push_str("<span class=\"chip chip-muted\">Linear witness</span>");
            out.push_str("<span class=\"chip chip-muted\">");
            out.push_str(&steps.len().to_string());
            out.push_str(" step");
            if steps.len() != 1 {
                out.push('s');
            }
            out.push_str("</span>");
        }
        OperationalTraceView::Deadlock {
            steps,
            deadlock_step,
            ..
        } => {
            out.push_str("<span class=\"chip chip-muted\">Deadlock witness</span>");
            out.push_str("<span class=\"chip chip-muted\">");
            out.push_str(&steps.len().to_string());
            out.push_str(" step");
            if steps.len() != 1 {
                out.push('s');
            }
            out.push_str("</span><span class=\"chip chip-cycle\">blocked at step ");
            out.push_str(&deadlock_step.to_string());
            out.push_str("</span>");
        }
        OperationalTraceView::Lasso {
            prefix,
            loop_steps,
            loop_start,
            ..
        } => {
            out.push_str("<span class=\"chip chip-muted\">Infinite witness</span>");
            out.push_str("<span class=\"chip chip-cycle\">cycle starts at step ");
            out.push_str(&loop_start.to_string());
            out.push_str("</span>");
            if let Some(cycle) = rendered_cycle_summary(loop_steps, *loop_start) {
                out.push_str("<span class=\"chip chip-muted\">");
                out.push_str(&escape_html(&cycle));
                out.push_str("</span>");
            }
            out.push_str("<span class=\"chip chip-muted\">lead-in ");
            out.push_str(&prefix.len().to_string());
            out.push_str(" step");
            if prefix.len() != 1 {
                out.push('s');
            }
            out.push_str("</span><span class=\"chip chip-muted\">cycle ");
            out.push_str(&loop_steps.len().to_string());
            out.push_str(" step");
            if loop_steps.len() != 1 {
                out.push('s');
            }
            out.push_str("</span>");
        }
    }
    out.push_str("</div>");
    out
}

fn render_trace_step_button(
    out: &mut String,
    trace_id: &str,
    panel_id: &str,
    step: &RenderedTraceStep,
    badge: Option<&str>,
    is_loop_step: bool,
    is_loop_entry: bool,
) {
    out.push_str("<button type=\"button\" class=\"");
    if is_loop_entry {
        out.push_str("loop-step loop-entry");
    } else if is_loop_step {
        out.push_str("loop-step");
    }
    out.push_str("\" data-target=\"");
    out.push_str(panel_id);
    out.push_str("\" onclick=\"showTraceStep('");
    out.push_str(trace_id);
    out.push_str("','");
    out.push_str(panel_id);
    out.push_str("')\"><span class=\"trace-step-label\">Step ");
    out.push_str(&step.step.to_string());
    out.push_str("</span>");
    if let Some(event) = &step.event {
        out.push_str("<span class=\"trace-step-subtitle\">");
        out.push_str(&escape_html(event));
        out.push_str("</span>");
    } else if step.step == 0 {
        out.push_str("<span class=\"trace-step-subtitle\">initial</span>");
    } else {
        out.push_str("<span class=\"trace-step-subtitle\">stutter</span>");
    }
    if let Some(badge) = badge {
        out.push_str("<span class=\"trace-step-badge\">");
        out.push_str(&escape_html(badge));
        out.push_str("</span>");
    }
    out.push_str("<span class=\"trace-step-subtitle\">");
    out.push_str(&step.changes.len().to_string());
    out.push_str(" change");
    if step.changes.len() != 1 {
        out.push('s');
    }
    out.push_str("</span>");
    if !step.observations.is_empty() {
        out.push_str("<span class=\"trace-step-subtitle\">");
        out.push_str(&step.observations.len().to_string());
        out.push_str(" observation");
        if step.observations.len() != 1 {
            out.push('s');
        }
        out.push_str("</span>");
    }
    out.push_str("</button>");
}

fn render_trace_panel_html(
    out: &mut String,
    step: &RenderedTraceStep,
    active: bool,
    loop_panel: bool,
) {
    out.push_str("<section class=\"trace-panel");
    if active {
        out.push_str(" active");
    }
    if loop_panel {
        out.push_str(" loop-panel");
    }
    out.push_str("\" data-panel=\"step-");
    out.push_str(&step.step.to_string());
    out.push_str("\"><div class=\"trace-eyebrow\">Step ");
    out.push_str(&step.step.to_string());
    out.push_str("</div>");
    if let Some(event) = &step.event {
        out.push_str("<div class=\"trace-event\">");
        out.push_str(&escape_html(event));
        out.push_str("</div>");
    } else if step.step == 0 {
        out.push_str("<div class=\"trace-event\">Initial state</div>");
    } else {
        out.push_str("<div class=\"trace-event\">Stutter step</div>");
    }
    out.push_str("<div class=\"trace-meta\"><span class=\"chip chip-muted\">");
    out.push_str(&step.changes.len().to_string());
    out.push_str(" change");
    if step.changes.len() != 1 {
        out.push('s');
    }
    out.push_str("</span>");
    if !step.assignments.is_empty() {
        out.push_str("<span class=\"chip chip-muted\">");
        out.push_str(&step.assignments.len().to_string());
        out.push_str(" recorded fact");
        if step.assignments.len() != 1 {
            out.push('s');
        }
        out.push_str("</span>");
    }
    if !step.observations.is_empty() {
        out.push_str("<span class=\"chip chip-muted\">");
        out.push_str(&step.observations.len().to_string());
        out.push_str(" observation");
        if step.observations.len() != 1 {
            out.push('s');
        }
        out.push_str("</span>");
    }
    out.push_str("</div>");
    if step.changes.is_empty() {
        out.push_str(
            "<p class=\"trace-note muted\">No state changes recorded for this transition.</p>",
        );
    } else {
        out.push_str("<div class=\"assignment-section-title\">State changes</div>");
        out.push_str("<ul class=\"assignment-list\">");
        for change in &step.changes {
            out.push_str("<li><code>");
            out.push_str(&escape_html(&change.entity));
            out.push('.');
            out.push_str(&escape_html(&change.field));
            out.push_str("</code>: <code>");
            out.push_str(&escape_html(change.before.as_deref().unwrap_or("<absent>")));
            out.push_str("</code> → <code>");
            out.push_str(&escape_html(change.after.as_deref().unwrap_or("<absent>")));
            out.push_str("</code></li>");
        }
        out.push_str("</ul>");
    }
    if !step.assignments.is_empty() {
        out.push_str("<div class=\"assignment-section-title\">State facts</div>");
        out.push_str("<ul class=\"assignment-list\">");
        for assignment in &step.assignments {
            out.push_str("<li><code>");
            out.push_str(&escape_html(&assignment.entity));
            out.push('.');
            out.push_str(&escape_html(&assignment.field));
            out.push_str("</code> = <code>");
            out.push_str(&escape_html(&assignment.value));
            out.push_str("</code></li>");
        }
        out.push_str("</ul>");
    }
    if !step.observations.is_empty() {
        out.push_str("<div class=\"assignment-section-title\">Observations</div>");
        out.push_str("<ul class=\"assignment-list\">");
        for observation in &step.observations {
            out.push_str("<li><code>");
            out.push_str(&escape_html(&render_trace_observation_text(observation)));
            out.push_str("</code></li>");
        }
        out.push_str("</ul>");
    }
    out.push_str("</section>");
}

fn result_primary_name(result: &verify::VerificationResult) -> String {
    match result {
        verify::VerificationResult::Proved { name, .. }
        | verify::VerificationResult::Admitted { name, .. }
        | verify::VerificationResult::Checked { name, .. }
        | verify::VerificationResult::Counterexample { name, .. }
        | verify::VerificationResult::ScenePass { name, .. }
        | verify::VerificationResult::SceneFail { name, .. }
        | verify::VerificationResult::Unprovable { name, .. }
        | verify::VerificationResult::LivenessViolation { name, .. }
        | verify::VerificationResult::Deadlock { name, .. } => name.clone(),
        verify::VerificationResult::FnContractProved { name, .. }
        | verify::VerificationResult::FnContractAdmitted { name, .. }
        | verify::VerificationResult::FnContractFailed { name, .. } => format!("fn {name}"),
    }
}

fn result_secondary_summary(result: &verify::VerificationResult) -> String {
    match result {
        verify::VerificationResult::Proved {
            method,
            time_ms,
            assumptions,
            ..
        } => format!(
            "proved by {method} in {time_ms}ms{}",
            render_assumption_suffix(assumptions)
        ),
        verify::VerificationResult::Admitted {
            reason,
            time_ms,
            assumptions,
            ..
        } => format!(
            "admitted: {reason} ({time_ms}ms{})",
            render_assumption_suffix(assumptions)
        ),
        verify::VerificationResult::Checked {
            depth,
            time_ms,
            assumptions,
            ..
        } => format!(
            "checked to depth {depth} in {time_ms}ms{}",
            render_assumption_suffix(assumptions)
        ),
        verify::VerificationResult::Counterexample { assumptions, .. } => {
            format!(
                "counterexample witness{}",
                render_assumption_suffix(assumptions)
            )
        }
        verify::VerificationResult::ScenePass { time_ms, .. } => {
            format!("scene satisfied in {time_ms}ms")
        }
        verify::VerificationResult::SceneFail { reason, .. } => reason.clone(),
        verify::VerificationResult::Unprovable { hint, .. } => hint.clone(),
        verify::VerificationResult::FnContractProved { time_ms, .. } => {
            format!("function contract proved in {time_ms}ms")
        }
        verify::VerificationResult::FnContractAdmitted {
            reason, time_ms, ..
        } => format!("function contract admitted: {reason} ({time_ms}ms)"),
        verify::VerificationResult::FnContractFailed { .. } => {
            "function contract violation".to_owned()
        }
        verify::VerificationResult::LivenessViolation { assumptions, .. } => {
            format!(
                "infinite counterexample{}",
                render_assumption_suffix(assumptions)
            )
        }
        verify::VerificationResult::Deadlock {
            step,
            reason,
            assumptions,
            ..
        } => format!(
            "deadlock at step {step}: {reason}{}",
            render_assumption_suffix(assumptions)
        ),
    }
}

fn render_result_verdict_pill(result: &verify::VerificationResult) -> String {
    let (label, class) = match result {
        verify::VerificationResult::Proved { .. } => ("Proved", "verdict-success"),
        verify::VerificationResult::Checked { .. } => ("Checked", "verdict-neutral"),
        verify::VerificationResult::ScenePass { .. } => ("Pass", "verdict-success"),
        verify::VerificationResult::Admitted { .. }
        | verify::VerificationResult::FnContractAdmitted { .. } => ("Admitted", "verdict-neutral"),
        verify::VerificationResult::Counterexample { .. } => ("Counterexample", "verdict-failure"),
        verify::VerificationResult::SceneFail { .. } => ("Scene Fail", "verdict-failure"),
        verify::VerificationResult::Unprovable { .. } => ("Unprovable", "verdict-failure"),
        verify::VerificationResult::FnContractProved { .. } => ("Proved", "verdict-success"),
        verify::VerificationResult::FnContractFailed { .. } => ("Failed", "verdict-failure"),
        verify::VerificationResult::LivenessViolation { .. } => {
            ("Liveness Violation", "verdict-failure")
        }
        verify::VerificationResult::Deadlock { .. } => ("Deadlock", "verdict-failure"),
    };
    format!("<span class=\"verdict-pill {class}\">{label}</span>")
}

fn render_assumption_suffix(assumptions: &[verify::TrustedAssumption]) -> String {
    if assumptions.is_empty() {
        String::new()
    } else {
        format!(" under {}", render_assumption_context(assumptions))
    }
}

fn render_assumption_context(assumptions: &[verify::TrustedAssumption]) -> String {
    let labels = assumptions
        .iter()
        .map(render_trusted_assumption)
        .collect::<Vec<_>>();
    match labels.len() {
        0 => String::new(),
        1 => labels[0].clone(),
        2 => format!("{}, {}", labels[0], labels[1]),
        3 => format!("{}, {}, {}", labels[0], labels[1], labels[2]),
        len => format!("{}, {}, +{} more", labels[0], labels[1], len - 2),
    }
}

fn report_result_debug_evidence(result: &verify::VerificationResult, failure_stream: bool) {
    let Some(evidence) = result.evidence() else {
        return;
    };
    let rendered = match serde_json::to_string_pretty(evidence) {
        Ok(json) => json,
        Err(err) => {
            let msg = format!("  [failed to serialize evidence: {err}]");
            if failure_stream {
                eprintln!("{msg}");
            } else {
                println!("{msg}");
            }
            return;
        }
    };
    if failure_stream {
        eprintln!("  debug evidence:");
        eprintln!("{rendered}");
    } else {
        println!("  debug evidence:");
        println!("{rendered}");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use abide_witness::{EvidenceEnvelope, WitnessEnvelope};

    #[test]
    fn operational_trace_text_includes_saw_observation() {
        let behavior = op::Behavior::builder()
            .state(op::State::default())
            .transition(
                op::Transition::builder()
                    .observation(
                        op::TransitionObservation::new(
                            "saw",
                            op::WitnessValue::String("Stripe::charge(1)".to_owned()),
                        )
                        .expect("valid saw observation"),
                    )
                    .build()
                    .expect("valid transition"),
            )
            .state(op::State::default())
            .build()
            .expect("valid behavior");
        let evidence = EvidenceEnvelope::witness(
            WitnessEnvelope::operational(
                op::OperationalWitness::counterexample(behavior).expect("valid witness"),
            )
            .expect("valid witness envelope"),
        )
        .expect("valid evidence envelope");
        let result = verify::VerificationResult::Counterexample {
            name: "v".to_owned(),
            evidence: Some(evidence),
            evidence_extraction_error: None,
            assumptions: Vec::new(),
            span: None,
            file: None,
        };

        let rendered =
            render_result_human_text(&result, TextArt::Ascii).expect("operational trace text");
        assert!(
            rendered.contains("observed Stripe::charge(1)"),
            "expected saw observation in rendered text, got: {rendered}"
        );
    }
}
