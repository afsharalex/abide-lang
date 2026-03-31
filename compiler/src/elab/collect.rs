//! Pass 1: Collect all top-level declarations into the environment.
//!
//! Walks the parsed AST and registers every type, entity, system,
//! pred, prop, verify, scene, theorem, axiom, lemma, const, and fn declaration.

use crate::ast::{self, Visibility};

use super::env::{DeclKind, Env};
use super::error::{ElabError, ErrorKind};
use super::types::{
    BinOp, BuiltinTy, EAction, EAxiom, EConst, EContract, EEntity, EEvent, EEventAction, EExpr,
    EField, EFn, ELemma, ENextItem, EPattern, EPred, EProp, EScene, ESceneGiven, ESceneWhen,
    ESystem, ETheorem, EVerify, Literal, Quantifier, Ty, UnOp,
};

/// Collect all declarations from a parsed program into a new `Env`.
pub fn collect(program: &ast::Program) -> Env {
    let mut env = Env::new();
    collect_into(&mut env, program);
    env
}

/// Collect declarations from a parsed program into an existing `Env`.
///
/// Used by the multi-file loader to merge declarations from multiple files
/// into a shared environment.
pub fn collect_into(env: &mut Env, program: &ast::Program) {
    // Track how many use_decls exist before this file's declarations
    let use_decls_before = env.use_decls.len();

    for decl in &program.decls {
        collect_top_decl(env, decl);
    }

    // Retroactively fix use-before-module: if this file's `use` declarations
    // were recorded with source_module=None (because `use` appeared before
    // `module` in the file), patch them now that module_name is set.
    if let Some(ref module) = env.module_name {
        for entry in &mut env.use_decls[use_decls_before..] {
            if entry.source_module.is_none() {
                entry.source_module = Some(module.clone());
            }
        }
    }
}

fn collect_top_decl(env: &mut Env, decl: &ast::TopDecl) {
    match decl {
        ast::TopDecl::Module(d) => {
            env.known_modules.insert(d.name.clone());
            match &env.module_name {
                Some(existing) if existing != &d.name => {
                    env.errors.push(ElabError::with_span(
                        ErrorKind::DuplicateDecl,
                        format!(
                            "conflicting module declaration: '{}' (already declared as '{}')",
                            d.name, existing
                        ),
                        String::new(),
                        d.span,
                    ));
                    // Keep first module name — don't overwrite on conflict
                }
                None => {
                    env.module_name = Some(d.name.clone());
                }
                _ => {} // Same name repeated — idempotent
            }
        }
        ast::TopDecl::Include(d) => {
            env.includes.push(d.path.clone());
        }
        ast::TopDecl::Use(ud) => {
            // Pair with current module so resolve knows which module is importing.
            // If module_name is None (use before module decl, or no module decl),
            // the use still gets recorded — resolve handles None source gracefully
            // by skipping same-module visibility shortcuts.
            let source_module = env.module_name.clone();
            let source_file = env.current_file.clone();
            env.use_decls.push(crate::elab::env::UseDeclEntry {
                decl: ud.clone(),
                source_module,
                source_file,
            });
        }
        ast::TopDecl::Const(d) => collect_const(env, d),
        ast::TopDecl::Fn(d) => collect_fn(env, d),
        ast::TopDecl::Type(d) => collect_type(env, d),
        ast::TopDecl::Record(d) => collect_record(env, d),
        ast::TopDecl::Entity(d) => collect_entity(env, d),
        ast::TopDecl::System(d) => collect_system(env, d),
        ast::TopDecl::Pred(d) => collect_pred(env, d),
        ast::TopDecl::Prop(d) => collect_prop(env, d),
        ast::TopDecl::Verify(d) => collect_verify(env, d),
        ast::TopDecl::Scene(d) => collect_scene(env, d),
        ast::TopDecl::Theorem(d) => collect_theorem(env, d),
        ast::TopDecl::Axiom(d) => collect_axiom(env, d),
        ast::TopDecl::Lemma(d) => collect_lemma(env, d),
        ast::TopDecl::Alias(d) => collect_alias(env, d),
    }
}

// ── Type declarations ────────────────────────────────────────────────

fn collect_type(env: &mut Env, td: &ast::TypeDecl) {
    let name = &td.name;
    // TypeDecl always represents an enum (sum type with constructors).
    // Type aliases are handled separately via TopDecl::Alias → collect_alias.
    let variant_names: Vec<String> = td
        .variants
        .iter()
        .map(|v| match v {
            ast::TypeVariant::Simple { name, .. }
            | ast::TypeVariant::Record { name, .. }
            | ast::TypeVariant::Param { name, .. } => name.clone(),
        })
        .collect();

    let ty = Ty::Enum(name.clone(), variant_names);
    let info = env.make_decl_info(
        DeclKind::Type,
        name.clone(),
        Some(ty.clone()),
        td.visibility,
        td.span,
    );
    env.add_decl(name, info);
    env.insert_type(name, ty);
}

fn collect_record(env: &mut Env, rd: &ast::RecordDecl) {
    let name = &rd.name;
    let fields: Vec<(String, Ty)> = rd
        .fields
        .iter()
        .map(|f| (f.name.clone(), resolve_type_ref(&f.ty)))
        .collect();
    let ty = Ty::Record(name.clone(), fields);
    let info = env.make_decl_info(
        DeclKind::Type,
        name.clone(),
        Some(ty.clone()),
        rd.visibility,
        rd.span,
    );
    env.add_decl(name, info);
    env.insert_type(name, ty);
}

fn collect_alias(env: &mut Env, ad: &ast::AliasDecl) {
    let name = &ad.name;
    let resolved = resolve_type_ref(&ad.target);
    let ty = Ty::Alias(name.clone(), Box::new(resolved));
    let info = env.make_decl_info(
        DeclKind::Type,
        name.clone(),
        Some(ty.clone()),
        ad.visibility,
        ad.span,
    );
    env.add_decl(name, info);
    env.insert_type(name, ty);
}

/// Convert a parse-level `TypeRef` to a semantic `Ty`.
/// Resolves builtins and marks others as unresolved.
pub fn resolve_type_ref(tr: &ast::TypeRef) -> Ty {
    match &tr.kind {
        ast::TypeRefKind::Simple(n) => match resolve_builtin(n) {
            Some(b) => Ty::Builtin(b),
            None => Ty::Unresolved(n.clone()),
        },
        ast::TypeRefKind::Param(n, args) => {
            let resolved_args: Vec<Ty> = args.iter().map(resolve_type_ref).collect();
            match (n.as_str(), resolved_args.as_slice()) {
                ("Set", [a]) => Ty::Set(Box::new(a.clone())),
                ("Seq", [a]) => Ty::Seq(Box::new(a.clone())),
                ("Map", [k, v]) => Ty::Map(Box::new(k.clone()), Box::new(v.clone())),
                _ => Ty::Param(n.clone(), resolved_args),
            }
        }
        ast::TypeRefKind::Tuple(ts) => Ty::Tuple(ts.iter().map(resolve_type_ref).collect()),
        ast::TypeRefKind::Fn(a, b) => {
            Ty::Fn(Box::new(resolve_type_ref(a)), Box::new(resolve_type_ref(b)))
        }
        ast::TypeRefKind::Paren(inner) => resolve_type_ref(inner),
        ast::TypeRefKind::Refine(base, pred) | ast::TypeRefKind::RefineParam(base, pred) => {
            let base_ty = resolve_type_ref(base);
            let pred_expr = collect_expr(pred);
            Ty::Refinement(Box::new(base_ty), Box::new(pred_expr))
        }
    }
}

fn resolve_builtin(name: &str) -> Option<BuiltinTy> {
    match name {
        "Int" => Some(BuiltinTy::Int),
        "Bool" => Some(BuiltinTy::Bool),
        "String" => Some(BuiltinTy::String),
        "Id" => Some(BuiltinTy::Id),
        "Real" => Some(BuiltinTy::Real),
        "Float" => Some(BuiltinTy::Float),
        _ => None,
    }
}

// ── Entity declarations ──────────────────────────────────────────────

fn collect_entity(env: &mut Env, ed: &ast::EntityDecl) {
    let name = &ed.name;
    let mut fields = Vec::new();
    let mut actions = Vec::new();
    for item in &ed.items {
        match item {
            ast::EntityItem::Field(f) => fields.push(collect_field(f)),
            ast::EntityItem::Action(a) => actions.push(collect_action(a)),
        }
    }
    let ee = EEntity {
        name: name.clone(),
        fields,
        actions,
        span: Some(ed.span),
    };
    let info = env.make_decl_info(DeclKind::Entity, name.clone(), None, ed.visibility, ed.span);
    env.add_decl(name, info);
    env.insert_entity(name, ee);
}

fn collect_field(f: &ast::FieldDecl) -> EField {
    EField {
        name: f.name.clone(),
        ty: resolve_type_ref(&f.ty),
        default: f.default.as_ref().map(collect_expr),
        span: Some(f.span),
    }
}

fn collect_action(a: &ast::EntityAction) -> EAction {
    let refs: Vec<(String, Ty)> = a
        .ref_params
        .iter()
        .map(|p| (p.name.clone(), resolve_param_ty(p)))
        .collect();
    let params: Vec<(String, Ty)> = a
        .params
        .iter()
        .map(|p| (p.name.clone(), resolve_param_ty(p)))
        .collect();
    let requires: Vec<EExpr> = a
        .contracts
        .iter()
        .filter_map(|c| match c {
            ast::Contract::Requires { expr, .. } => Some(collect_expr(expr)),
            _ => None,
        })
        .collect();
    let body: Vec<EExpr> = a.body.iter().map(collect_expr).collect();
    EAction {
        name: a.name.clone(),
        refs,
        params,
        requires,
        body,
        span: Some(a.span),
    }
}

fn resolve_param_ty(p: &ast::Param) -> Ty {
    resolve_type_ref(&ast::TypeRef {
        kind: ast::TypeRefKind::Simple(p.ty.clone()),
        span: p.span,
    })
}

// ── System declarations ──────────────────────────────────────────────

fn collect_system(env: &mut Env, sd: &ast::SystemDecl) {
    let name = &sd.name;
    let mut uses = Vec::new();
    let mut events = Vec::new();
    let mut next_items = Vec::new();

    for item in &sd.items {
        match item {
            ast::SystemItem::Uses(entity_name, _) => uses.push(entity_name.clone()),
            ast::SystemItem::Event(ev) => events.push(collect_event(ev)),
            ast::SystemItem::Next(nb) => {
                for ni in &nb.items {
                    next_items.push(collect_next_item(ni));
                }
            }
        }
    }

    let es = ESystem {
        name: name.clone(),
        uses,
        scopes: Vec::new(),
        events,
        next_items,
        span: Some(sd.span),
    };
    let info = env.make_decl_info(
        DeclKind::System,
        name.clone(),
        None,
        Visibility::Public,
        sd.span,
    );
    env.add_decl(name, info);
    env.insert_system(name, es);
}

fn collect_event(ev: &ast::EventDecl) -> EEvent {
    let params: Vec<(String, Ty)> = ev
        .params
        .iter()
        .map(|p| (p.name.clone(), resolve_param_ty(p)))
        .collect();
    let requires: Vec<EExpr> = ev
        .contracts
        .iter()
        .filter_map(|c| match c {
            ast::Contract::Requires { expr, .. } => Some(collect_expr(expr)),
            _ => None,
        })
        .collect();
    let ensures: Vec<EExpr> = ev
        .contracts
        .iter()
        .filter_map(|c| match c {
            ast::Contract::Ensures { expr, .. } => Some(collect_expr(expr)),
            _ => None,
        })
        .collect();
    let body: Vec<EEventAction> = ev.items.iter().map(collect_event_item).collect();
    EEvent {
        name: ev.name.clone(),
        params,
        requires,
        ensures,
        body,
        span: Some(ev.span),
    }
}

fn collect_event_item(item: &ast::EventItem) -> EEventAction {
    match item {
        ast::EventItem::Choose(cb) => EEventAction::Choose(
            cb.var.clone(),
            Ty::Unresolved(cb.ty.clone()),
            collect_expr(&cb.condition),
            cb.body
                .iter()
                .map(|e| classify_expr(&collect_expr(e)))
                .collect(),
        ),
        ast::EventItem::For(fb) => EEventAction::ForAll(
            fb.var.clone(),
            Ty::Unresolved(fb.ty.clone()),
            fb.body
                .iter()
                .map(|e| classify_expr(&collect_expr(e)))
                .collect(),
        ),
        ast::EventItem::Create(cb) => EEventAction::Create(
            cb.ty.clone(),
            cb.fields
                .iter()
                .map(|f| (f.name.clone(), collect_expr(&f.value)))
                .collect(),
        ),
        ast::EventItem::Expr(e) => classify_expr(&collect_expr(e)),
    }
}

/// Classify a collected expression as a structured action when possible.
/// Detects cross-system calls (`Sys::event(args)`) and action applies (`o.action(args)`).
fn classify_expr(expr: &EExpr) -> EEventAction {
    match expr {
        // Cross-system call: Sys::event(args)
        EExpr::Call(_, callee, args, _) => {
            if let EExpr::Qual(_, sys, ev, _) = callee.as_ref() {
                return EEventAction::CrossCall(sys.clone(), ev.clone(), extract_named_args(args));
            }
            // Action apply: o.action(args)
            if let EExpr::Field(_, target, action, _) = callee.as_ref() {
                return EEventAction::Apply(
                    *target.clone(),
                    action.clone(),
                    Vec::new(),
                    extract_named_args(args),
                );
            }
            EEventAction::Expr(expr.clone())
        }
        // Action apply with refs: o.action[refs](args)
        EExpr::CallR(_, callee, refs, args, _) => {
            if let EExpr::Field(_, target, action, _) = callee.as_ref() {
                return EEventAction::Apply(
                    *target.clone(),
                    action.clone(),
                    extract_named_args(refs),
                    extract_named_args(args),
                );
            }
            EEventAction::Expr(expr.clone())
        }
        _ => EEventAction::Expr(expr.clone()),
    }
}

fn extract_named_args(args: &[EExpr]) -> Vec<EExpr> {
    args.iter()
        .map(|e| match e {
            EExpr::NamedPair(_, _, inner, _) => *inner.clone(),
            other => other.clone(),
        })
        .collect()
}

fn collect_next_item(ni: &ast::NextItem) -> ENextItem {
    match ni {
        ast::NextItem::When {
            condition, event, ..
        } => ENextItem::When(Box::new(collect_expr(condition)), expr_to_text(&event.kind)),
        ast::NextItem::Else(_) => ENextItem::Else,
    }
}

fn expr_to_text(kind: &ast::ExprKind) -> String {
    match kind {
        ast::ExprKind::Qual2(s, n) => format!("{s}::{n}"),
        ast::ExprKind::Var(n) => n.clone(),
        _ => "_unknown".to_owned(),
    }
}

// ── Predicates, properties, verify, scene, theorem, axiom, lemma ─────

fn collect_pred(env: &mut Env, pd: &ast::PredDecl) {
    let name = &pd.name;
    let params: Vec<(String, Ty)> = pd
        .params
        .iter()
        .map(|p| (p.name.clone(), resolve_param_ty(p)))
        .collect();
    let ep = EPred {
        name: name.clone(),
        params,
        body: collect_expr(&pd.body),
        span: Some(pd.span),
        file: env.current_file.clone(),
    };
    let info = env.make_decl_info(DeclKind::Pred, name.clone(), None, pd.visibility, pd.span);
    env.add_decl(name, info);
    env.insert_pred(name, ep);
}

fn collect_prop(env: &mut Env, pd: &ast::PropDecl) {
    let name = &pd.name;
    let target = if pd.systems.is_empty() {
        None
    } else {
        Some(pd.systems.join(","))
    };
    let ep = EProp {
        name: name.clone(),
        target,
        body: collect_expr(&pd.body),
        span: Some(pd.span),
        file: env.current_file.clone(),
    };
    let info = env.make_decl_info(DeclKind::Prop, name.clone(), None, pd.visibility, pd.span);
    env.add_decl(name, info);
    env.insert_prop(name, ep);
}

fn collect_verify(env: &mut Env, vd: &ast::VerifyDecl) {
    let name = &vd.name;
    let targets: Vec<(String, i64, i64)> = vd
        .targets
        .iter()
        .map(|t| (t.system.clone(), t.min, t.max))
        .collect();
    let asserts: Vec<EExpr> = vd.asserts.iter().map(collect_expr).collect();
    let ev = EVerify {
        name: name.clone(),
        targets,
        asserts,
        span: Some(vd.span),
        file: env.current_file.clone(),
    };
    let key = format!("verify:{name}");
    let info = env.make_decl_info(
        DeclKind::Verify,
        key.clone(),
        None,
        Visibility::Public,
        vd.span,
    );
    env.add_decl(&key, info);
    env.verifies.push(ev);
}

fn collect_scene(env: &mut Env, sd: &ast::SceneDecl) {
    let name = &sd.name;
    let targets = sd.systems.clone();
    let mut givens = Vec::new();
    let mut whens = Vec::new();
    let mut thens = Vec::new();

    for item in &sd.items {
        match item {
            ast::SceneItem::Given {
                name,
                qual_type,
                condition,
                ..
            } => givens.push(ESceneGiven {
                var: name.clone(),
                entity_type: qual_type_name(qual_type),
                condition: condition.as_ref().map(collect_expr),
            }),
            ast::SceneItem::WhenAction {
                name, invoc, card, ..
            } => whens.push(collect_when_action(name, invoc, card.as_ref())),
            ast::SceneItem::WhenAssume { expr, .. } => {
                whens.push(ESceneWhen::Assume(collect_expr(expr)));
            }
            ast::SceneItem::ThenAssert { expr, .. } => {
                thens.push(collect_expr(expr));
            }
            ast::SceneItem::GivenBlock { items, .. } => {
                for gi in items {
                    givens.push(ESceneGiven {
                        var: gi.name.clone(),
                        entity_type: qual_type_name(&gi.qual_type),
                        condition: gi.condition.as_ref().map(collect_expr),
                    });
                }
            }
            ast::SceneItem::WhenBlock { items, .. } => {
                for wi in items {
                    match wi {
                        ast::WhenItem::Action {
                            name, invoc, card, ..
                        } => whens.push(collect_when_action(name, invoc, card.as_ref())),
                        ast::WhenItem::Assume { expr, .. } => {
                            whens.push(ESceneWhen::Assume(collect_expr(expr)));
                        }
                    }
                }
            }
            ast::SceneItem::ThenBlock { items, .. } => {
                for ti in items {
                    thens.push(collect_expr(&ti.expr));
                }
            }
        }
    }

    let es = EScene {
        name: name.clone(),
        targets,
        givens,
        whens,
        thens,
        span: Some(sd.span),
        file: env.current_file.clone(),
    };
    let key = format!("scene:{name}");
    let info = env.make_decl_info(
        DeclKind::Scene,
        key.clone(),
        None,
        Visibility::Public,
        sd.span,
    );
    env.add_decl(&key, info);
    env.scenes.push(es);
}

fn collect_when_action(
    var: &str,
    invoc: &ast::ActionInvoc,
    card: Option<&ast::CardValue>,
) -> ESceneWhen {
    let (sys, ev, args) = collect_action_invoc(invoc);
    let card_text = card.map(|c| match c {
        ast::CardValue::One => "one".to_owned(),
        ast::CardValue::Lone => "lone".to_owned(),
        ast::CardValue::Some => "some".to_owned(),
        ast::CardValue::No => "no".to_owned(),
        ast::CardValue::Num(n) => n.to_string(),
    });
    ESceneWhen::Action {
        var: var.to_owned(),
        system: sys,
        event: ev,
        args,
        card: card_text,
    }
}

fn collect_action_invoc(ai: &ast::ActionInvoc) -> (String, String, Vec<EExpr>) {
    let args: Vec<EExpr> = ai.args.iter().map(collect_invoc_arg).collect();
    match &ai.qualifier {
        Some(q) => (q.clone(), ai.name.clone(), args),
        None => ("_self".to_owned(), ai.name.clone(), args),
    }
}

fn collect_invoc_arg(arg: &ast::InvocArg) -> EExpr {
    let unresolved = Ty::Unresolved("?".to_owned());
    match arg {
        ast::InvocArg::Field { obj, field, .. } => EExpr::Field(
            unresolved.clone(),
            Box::new(EExpr::Var(unresolved, obj.clone(), None)),
            field.clone(),
            None,
        ),
        ast::InvocArg::Simple { name, .. } | ast::InvocArg::State { name, .. } => {
            EExpr::Var(unresolved, name.clone(), None)
        }
        ast::InvocArg::Int { value, .. } => {
            EExpr::Lit(Ty::Builtin(BuiltinTy::Int), Literal::Int(*value), None)
        }
        ast::InvocArg::Real { value, .. } => {
            EExpr::Lit(Ty::Builtin(BuiltinTy::Real), Literal::Real(*value), None)
        }
        ast::InvocArg::Float { value, .. } => {
            let v = parse_float_text(value);
            EExpr::Lit(Ty::Builtin(BuiltinTy::Float), Literal::Float(v), None)
        }
        ast::InvocArg::Str { value, .. } => EExpr::Lit(
            Ty::Builtin(BuiltinTy::String),
            Literal::Str(value.clone()),
            None,
        ),
    }
}

fn qual_type_name(qt: &ast::QualType) -> String {
    match qt {
        ast::QualType::Qualified { name, .. } | ast::QualType::Simple { name, .. } => name.clone(),
    }
}

fn collect_theorem(env: &mut Env, td: &ast::TheoremDecl) {
    let name = &td.name;
    let et = ETheorem {
        name: name.clone(),
        targets: td.systems.clone(),
        invariants: td.invariants.iter().map(collect_expr).collect(),
        shows: td.shows.iter().map(collect_expr).collect(),
        span: Some(td.span),
        file: env.current_file.clone(),
    };
    let info = env.make_decl_info(
        DeclKind::Theorem,
        name.clone(),
        None,
        Visibility::Public,
        td.span,
    );
    env.add_decl(name, info);
    env.theorems.push(et);
}

fn collect_axiom(env: &mut Env, ad: &ast::AxiomDecl) {
    let name = &ad.name;
    let ea = EAxiom {
        name: name.clone(),
        body: collect_expr(&ad.body),
        span: Some(ad.span),
        file: env.current_file.clone(),
    };
    let info = env.make_decl_info(
        DeclKind::Axiom,
        name.clone(),
        None,
        Visibility::Public,
        ad.span,
    );
    env.add_decl(name, info);
    env.axioms.push(ea);
}

fn collect_lemma(env: &mut Env, ld: &ast::LemmaDecl) {
    let name = &ld.name;
    let el = ELemma {
        name: name.clone(),
        body: ld.body.iter().map(collect_expr).collect(),
        span: Some(ld.span),
        file: env.current_file.clone(),
    };
    let info = env.make_decl_info(
        DeclKind::Lemma,
        name.clone(),
        None,
        Visibility::Public,
        ld.span,
    );
    env.add_decl(name, info);
    env.lemmas.push(el);
}

fn collect_const(env: &mut Env, cd: &ast::ConstDecl) {
    let name = &cd.name;
    let ec = EConst {
        name: name.clone(),
        body: collect_expr(&cd.value),
        span: Some(cd.span),
    };
    let info = env.make_decl_info(DeclKind::Const, name.clone(), None, cd.visibility, cd.span);
    env.add_decl(name, info);
    env.insert_const(name, ec);
}

fn collect_fn(env: &mut Env, fd: &ast::FnDecl) {
    let name = &fd.name;
    let params: Vec<(String, Ty)> = fd
        .params
        .iter()
        .map(|p| (p.name.clone(), resolve_type_ref(&p.ty)))
        .collect();
    let ret = resolve_type_ref(&fd.ret_type);
    let contracts = fd.contracts.iter().map(collect_contract).collect();
    let ef = EFn {
        name: name.clone(),
        params,
        ret_ty: ret,
        contracts,
        body: collect_expr(&fd.body),
        span: Some(fd.span),
        file: env.current_file.clone(),
    };
    let info = env.make_decl_info(DeclKind::Fn, name.clone(), None, fd.visibility, fd.span);
    env.add_decl(name, info);
    env.insert_fn(name, ef);
}

fn collect_contract(c: &ast::Contract) -> EContract {
    match c {
        ast::Contract::Requires { expr, .. } => EContract::Requires(collect_expr(expr)),
        ast::Contract::Ensures { expr, .. } => EContract::Ensures(collect_expr(expr)),
        ast::Contract::Decreases { measures, star, .. } => EContract::Decreases {
            measures: measures.iter().map(collect_expr).collect(),
            star: *star,
        },
        ast::Contract::Invariant { expr, .. } => EContract::Invariant(collect_expr(expr)),
    }
}

// ── Expression collection ────────────────────────────────────────────

#[allow(clippy::too_many_lines)]
fn collect_expr(expr: &ast::Expr) -> EExpr {
    let u = || Ty::Unresolved("?".to_owned());
    let bool_ty = || Ty::Builtin(BuiltinTy::Bool);
    let int_ty = || Ty::Builtin(BuiltinTy::Int);
    let sp = Some(expr.span);

    match &expr.kind {
        ast::ExprKind::Var(n) => EExpr::Var(u(), n.clone(), sp),
        ast::ExprKind::Int(i) => EExpr::Lit(int_ty(), Literal::Int(*i), sp),
        ast::ExprKind::Real(d) => EExpr::Lit(Ty::Builtin(BuiltinTy::Real), Literal::Real(*d), sp),
        ast::ExprKind::Float(s) => EExpr::Lit(
            Ty::Builtin(BuiltinTy::Float),
            Literal::Float(parse_float_text(s)),
            sp,
        ),
        ast::ExprKind::Str(s) => {
            EExpr::Lit(Ty::Builtin(BuiltinTy::String), Literal::Str(s.clone()), sp)
        }
        ast::ExprKind::True => EExpr::Lit(bool_ty(), Literal::Bool(true), sp),
        ast::ExprKind::False => EExpr::Lit(bool_ty(), Literal::Bool(false), sp),

        ast::ExprKind::Qual2(s, n) => EExpr::Qual(u(), s.clone(), n.clone(), sp),
        ast::ExprKind::Qual3(s, t, n) => EExpr::Qual(u(), format!("{s}::{t}"), n.clone(), sp),
        ast::ExprKind::State1(c) => EExpr::Var(u(), c.clone(), sp),
        ast::ExprKind::State2(t, c) => EExpr::Qual(u(), t.clone(), c.clone(), sp),
        ast::ExprKind::State3(s, t, c) => EExpr::Qual(u(), format!("{s}::{t}"), c.clone(), sp),

        ast::ExprKind::Field(e, f) => EExpr::Field(u(), Box::new(collect_expr(e)), f.clone(), sp),
        ast::ExprKind::Prime(e) => EExpr::Prime(u(), Box::new(collect_expr(e)), sp),
        ast::ExprKind::Call(callee, args) => {
            // Recognize collection literals: Set(1, 2, 3), Seq(1, 2), Map(k1, v1, k2, v2)
            if let ast::ExprKind::Var(name) = &callee.kind {
                match name.as_str() {
                    "Set" => {
                        return EExpr::SetLit(u(), args.iter().map(collect_expr).collect(), sp);
                    }
                    "Seq" => {
                        return EExpr::SeqLit(u(), args.iter().map(collect_expr).collect(), sp);
                    }
                    "Map" => {
                        // Map literal: pairs of (key, value) args
                        let collected: Vec<EExpr> = args.iter().map(collect_expr).collect();
                        let entries: Vec<(EExpr, EExpr)> = collected
                            .chunks(2)
                            .filter_map(|pair| {
                                if pair.len() == 2 {
                                    Some((pair[0].clone(), pair[1].clone()))
                                } else {
                                    None
                                }
                            })
                            .collect();
                        return EExpr::MapLit(u(), entries, sp);
                    }
                    _ => {}
                }
            }
            EExpr::Call(
                u(),
                Box::new(collect_expr(callee)),
                args.iter().map(collect_expr).collect(),
                sp,
            )
        }
        ast::ExprKind::CallR(callee, refs, args) => EExpr::CallR(
            u(),
            Box::new(collect_expr(callee)),
            refs.iter().map(collect_expr).collect(),
            args.iter().map(collect_expr).collect(),
            sp,
        ),

        // Unary ops
        ast::ExprKind::Neg(e) => EExpr::UnOp(int_ty(), UnOp::Neg, Box::new(collect_expr(e)), sp),
        ast::ExprKind::Not(e) => EExpr::UnOp(bool_ty(), UnOp::Not, Box::new(collect_expr(e)), sp),
        ast::ExprKind::Card(e) => EExpr::Card(u(), Box::new(collect_expr(e)), sp),

        // Binary ops: arithmetic
        ast::ExprKind::Add(a, b) => bin_op(u(), BinOp::Add, a, b, sp),
        ast::ExprKind::Sub(a, b) => bin_op(u(), BinOp::Sub, a, b, sp),
        ast::ExprKind::Mul(a, b) => bin_op(u(), BinOp::Mul, a, b, sp),
        ast::ExprKind::Div(a, b) => bin_op(u(), BinOp::Div, a, b, sp),
        ast::ExprKind::Mod(a, b) => bin_op(u(), BinOp::Mod, a, b, sp),

        // Binary ops: comparison (result is Bool)
        ast::ExprKind::Eq(a, b) => bin_op(bool_ty(), BinOp::Eq, a, b, sp),
        ast::ExprKind::NEq(a, b) => bin_op(bool_ty(), BinOp::NEq, a, b, sp),
        ast::ExprKind::Lt(a, b) => bin_op(bool_ty(), BinOp::Lt, a, b, sp),
        ast::ExprKind::Gt(a, b) => bin_op(bool_ty(), BinOp::Gt, a, b, sp),
        ast::ExprKind::Le(a, b) => bin_op(bool_ty(), BinOp::Le, a, b, sp),
        ast::ExprKind::Ge(a, b) => bin_op(bool_ty(), BinOp::Ge, a, b, sp),

        // Binary ops: logical (result is Bool)
        ast::ExprKind::And(a, b) => bin_op(bool_ty(), BinOp::And, a, b, sp),
        ast::ExprKind::Or(a, b) => bin_op(bool_ty(), BinOp::Or, a, b, sp),
        ast::ExprKind::Impl(a, b) => bin_op(bool_ty(), BinOp::Implies, a, b, sp),

        // Binary ops: composition
        ast::ExprKind::Unord(a, b) => bin_op(u(), BinOp::Unord, a, b, sp),
        ast::ExprKind::Conc(a, b) => bin_op(u(), BinOp::Conc, a, b, sp),
        ast::ExprKind::Xor(a, b) => bin_op(u(), BinOp::Xor, a, b, sp),

        // Membership
        ast::ExprKind::In(a, b) => EExpr::In(
            bool_ty(),
            Box::new(collect_expr(a)),
            Box::new(collect_expr(b)),
            sp,
        ),

        // Temporal
        ast::ExprKind::Always(e) => EExpr::Always(u(), Box::new(collect_expr(e)), sp),
        ast::ExprKind::Eventually(e) => EExpr::Eventually(u(), Box::new(collect_expr(e)), sp),
        ast::ExprKind::AssertExpr(e) => EExpr::Assert(u(), Box::new(collect_expr(e)), sp),

        // Assignment
        ast::ExprKind::Assign(a, b) => EExpr::Assign(
            u(),
            Box::new(collect_expr(a)),
            Box::new(collect_expr(b)),
            sp,
        ),
        ast::ExprKind::NamedPair(n, e) => {
            EExpr::NamedPair(u(), n.clone(), Box::new(collect_expr(e)), sp)
        }
        ast::ExprKind::Seq(a, b) => EExpr::Seq(
            u(),
            Box::new(collect_expr(a)),
            Box::new(collect_expr(b)),
            sp,
        ),
        ast::ExprKind::SameStep(a, b) => EExpr::SameStep(
            u(),
            Box::new(collect_expr(a)),
            Box::new(collect_expr(b)),
            sp,
        ),
        ast::ExprKind::Pipe(a, b) => EExpr::Pipe(
            u(),
            Box::new(collect_expr(a)),
            Box::new(collect_expr(b)),
            sp,
        ),

        // Quantifiers
        ast::ExprKind::All(v, tr, body) => EExpr::Quant(
            bool_ty(),
            Quantifier::All,
            v.clone(),
            resolve_type_ref(tr),
            Box::new(collect_expr(body)),
            sp,
        ),
        ast::ExprKind::Exists(v, tr, body) => EExpr::Quant(
            bool_ty(),
            Quantifier::Exists,
            v.clone(),
            resolve_type_ref(tr),
            Box::new(collect_expr(body)),
            sp,
        ),
        ast::ExprKind::SomeQ(v, tr, body) => EExpr::Quant(
            bool_ty(),
            Quantifier::Some,
            v.clone(),
            resolve_type_ref(tr),
            Box::new(collect_expr(body)),
            sp,
        ),
        ast::ExprKind::NoQ(v, tr, body) => EExpr::Quant(
            bool_ty(),
            Quantifier::No,
            v.clone(),
            resolve_type_ref(tr),
            Box::new(collect_expr(body)),
            sp,
        ),
        ast::ExprKind::OneQ(v, tr, body) => EExpr::Quant(
            bool_ty(),
            Quantifier::One,
            v.clone(),
            resolve_type_ref(tr),
            Box::new(collect_expr(body)),
            sp,
        ),
        ast::ExprKind::LoneQ(v, tr, body) => EExpr::Quant(
            bool_ty(),
            Quantifier::Lone,
            v.clone(),
            resolve_type_ref(tr),
            Box::new(collect_expr(body)),
            sp,
        ),

        // Let bindings
        ast::ExprKind::Let(binds, body) => {
            let bs: Vec<(String, Option<Ty>, EExpr)> = binds
                .iter()
                .map(|lb| {
                    (
                        lb.name.clone(),
                        lb.ty.as_ref().map(resolve_type_ref),
                        collect_expr(&lb.value),
                    )
                })
                .collect();
            EExpr::Let(bs, Box::new(collect_expr(body)), sp)
        }

        // Lambda
        ast::ExprKind::Lambda(params, body) => {
            let ps: Vec<(String, Ty)> = params
                .iter()
                .map(|p| (p.name.clone(), resolve_type_ref(&p.ty)))
                .collect();
            EExpr::Lam(ps, None, Box::new(collect_expr(body)), sp)
        }
        ast::ExprKind::LambdaT(params, ret_ty, body) => {
            let ps: Vec<(String, Ty)> = params
                .iter()
                .map(|p| (p.name.clone(), resolve_type_ref(&p.ty)))
                .collect();
            EExpr::Lam(
                ps,
                Some(resolve_type_ref(ret_ty)),
                Box::new(collect_expr(body)),
                sp,
            )
        }

        // Tuple literal
        ast::ExprKind::TupleLit(es) => {
            EExpr::TupleLit(u(), es.iter().map(collect_expr).collect(), sp)
        }

        // Match expression
        ast::ExprKind::Match(scrutinee, arms) => {
            let scrut = collect_expr(scrutinee);
            let earms = arms
                .iter()
                .map(|arm| {
                    let pat = collect_pattern(&arm.pattern);
                    let guard = arm.guard.as_ref().map(|g| collect_expr(g));
                    let body = collect_expr(&arm.body);
                    (pat, guard, body)
                })
                .collect();
            EExpr::Match(Box::new(scrut), earms, sp)
        }

        // Map/collection operations
        ast::ExprKind::MapUpdate(m, k, v) => EExpr::MapUpdate(
            u(),
            Box::new(collect_expr(m)),
            Box::new(collect_expr(k)),
            Box::new(collect_expr(v)),
            sp,
        ),
        ast::ExprKind::Index(m, k) => EExpr::Index(
            u(),
            Box::new(collect_expr(m)),
            Box::new(collect_expr(k)),
            sp,
        ),
        ast::ExprKind::SetComp {
            projection,
            var,
            domain,
            filter,
        } => {
            let dom = resolve_type_ref(domain);
            let proj = projection.as_ref().map(|p| Box::new(collect_expr(p)));
            EExpr::SetComp(
                u(),
                proj,
                var.clone(),
                dom,
                Box::new(collect_expr(filter)),
                sp,
            )
        }

        // Imperative constructs
        ast::ExprKind::Block(items) => collect_block_items(items),
        ast::ExprKind::VarDecl { name, ty, init } => {
            // Standalone VarDecl outside a block (shouldn't happen in practice,
            // but handle gracefully by wrapping with a Sorry continuation).
            let ty_e = ty.as_ref().map(resolve_type_ref);
            EExpr::VarDecl(
                name.clone(),
                ty_e,
                Box::new(collect_expr(init)),
                Box::new(EExpr::Sorry(sp)),
                sp,
            )
        }
        ast::ExprKind::While {
            cond,
            contracts,
            body,
        } => {
            let contracts_e = contracts.iter().map(collect_contract).collect();
            EExpr::While(
                Box::new(collect_expr(cond)),
                contracts_e,
                Box::new(collect_expr(body)),
                sp,
            )
        }
        ast::ExprKind::IfElse {
            cond,
            then_body,
            else_body,
        } => EExpr::IfElse(
            Box::new(collect_expr(cond)),
            Box::new(collect_expr(then_body)),
            else_body.as_ref().map(|e| Box::new(collect_expr(e))),
            sp,
        ),

        // Stubs
        ast::ExprKind::Sorry => EExpr::Sorry(sp),
        ast::ExprKind::Todo => EExpr::Todo(sp),
    }
}

/// Build nested `VarDecl` continuations from a flat block item list.
///
/// When a `VarDecl` appears in a block, its continuation is the remaining items.
/// Non-VarDecl items are sequenced into a Block.
fn collect_block_items(items: &[ast::Expr]) -> EExpr {
    match items {
        [] => EExpr::Sorry(None),
        [single] => collect_expr(single),
        [first, rest @ ..] => {
            if let ast::ExprKind::VarDecl { name, ty, init } = &first.kind {
                let init_e = collect_expr(init);
                let rest_e = collect_block_items(rest);
                let ty_e = ty.as_ref().map(resolve_type_ref);
                EExpr::VarDecl(
                    name.clone(),
                    ty_e,
                    Box::new(init_e),
                    Box::new(rest_e),
                    Some(first.span),
                )
            } else {
                let first_e = collect_expr(first);
                let rest_e = collect_block_items(rest);
                EExpr::Block(vec![first_e, rest_e], Some(first.span))
            }
        }
    }
}

fn collect_pattern(pat: &ast::Pattern) -> EPattern {
    match pat {
        ast::Pattern::Var(name, _) => EPattern::Var(name.clone()),
        ast::Pattern::Wild(_) => EPattern::Wild,
        ast::Pattern::Ctor(name, fields, _has_rest, _) => {
            let fps = fields
                .iter()
                .map(|fp| (fp.name.clone(), collect_pattern(&fp.pattern)))
                .collect();
            EPattern::Ctor(name.clone(), fps)
        }
        ast::Pattern::Or(left, right, _) => EPattern::Or(
            Box::new(collect_pattern(left)),
            Box::new(collect_pattern(right)),
        ),
    }
}

fn bin_op(ty: Ty, op: BinOp, a: &ast::Expr, b: &ast::Expr, sp: Option<crate::span::Span>) -> EExpr {
    EExpr::BinOp(
        ty,
        op,
        Box::new(collect_expr(a)),
        Box::new(collect_expr(b)),
        sp,
    )
}

fn parse_float_text(s: &str) -> f64 {
    let stripped = s.strip_suffix('f').unwrap_or(s);
    stripped.parse().unwrap_or(0.0)
}

// ── Tests ───────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Visibility;
    use crate::lex;
    use crate::parse::Parser;

    fn collect_src(src: &str) -> Env {
        let tokens = lex::lex(src).expect("lex error");
        let mut parser = Parser::new(tokens);
        let prog = parser.parse_program().expect("parse error");
        collect(&prog)
    }

    #[test]
    fn module_name_tracked() {
        let env = collect_src("module Commerce");
        assert_eq!(env.module_name.as_deref(), Some("Commerce"));
    }

    #[test]
    fn duplicate_module_errors_and_keeps_first() {
        let env = collect_src("module Commerce\nmodule Billing");
        // First module name wins — not overwritten on conflict
        assert_eq!(env.module_name.as_deref(), Some("Commerce"));
        assert!(
            env.errors
                .iter()
                .any(|e| format!("{:?}", e).contains("conflicting module")),
            "expected conflicting module error, got: {:?}",
            env.errors
        );
    }

    #[test]
    fn same_module_twice_no_error() {
        let env = collect_src("module Commerce\nmodule Commerce");
        assert_eq!(env.module_name.as_deref(), Some("Commerce"));
        assert!(
            env.errors.is_empty(),
            "duplicate same-name module should not error"
        );
    }

    #[test]
    fn include_paths_tracked() {
        let env = collect_src(r#"include "billing.abide""#);
        assert_eq!(env.includes, vec!["billing.abide"]);
    }

    #[test]
    fn include_preserves_order() {
        let env = collect_src(
            r#"include "first.abide"
include "second.abide""#,
        );
        assert_eq!(env.includes, vec!["first.abide", "second.abide"]);
    }

    #[test]
    fn use_decls_tracked() {
        let env = collect_src("use Commerce::Order\nuse Billing::*\nuse Fulfillment::Ship as S");
        assert_eq!(env.use_decls.len(), 3);
    }

    #[test]
    fn use_decls_preserve_order() {
        let env = collect_src("use A::X\nuse B::Y\nuse C::Z");
        assert_eq!(env.use_decls.len(), 3);
        // First should be A::X
        if let ast::UseDecl::Single { module, name, .. } = &env.use_decls[0].decl {
            assert_eq!(module, "A");
            assert_eq!(name, "X");
        } else {
            panic!("expected Single");
        }
        // Third should be C::Z
        if let ast::UseDecl::Single { module, name, .. } = &env.use_decls[2].decl {
            assert_eq!(module, "C");
            assert_eq!(name, "Z");
        } else {
            panic!("expected Single");
        }
    }

    #[test]
    fn type_visibility_private_by_default() {
        let env = collect_src("enum Status = Active | Inactive");
        let info = env.decls.get("Status").expect("Status decl");
        assert_eq!(info.visibility, Visibility::Private);
    }

    #[test]
    fn type_visibility_public() {
        let env = collect_src("pub enum Status = Active | Inactive");
        let info = env.decls.get("Status").expect("Status decl");
        assert_eq!(info.visibility, Visibility::Public);
    }

    #[test]
    fn entity_visibility_private_by_default() {
        let env = collect_src("entity Order { id: Id }");
        let info = env.decls.get("Order").expect("Order decl");
        assert_eq!(info.visibility, Visibility::Private);
    }

    #[test]
    fn entity_visibility_public() {
        let env = collect_src("pub entity Order { id: Id }");
        let info = env.decls.get("Order").expect("Order decl");
        assert_eq!(info.visibility, Visibility::Public);
    }

    #[test]
    fn system_always_public() {
        let env = collect_src("system S { }");
        let info = env.decls.get("S").expect("S decl");
        assert_eq!(info.visibility, Visibility::Public);
    }

    #[test]
    fn fn_visibility() {
        let env = collect_src("fn total(x: Int): Int = x\npub fn calc(x: Int): Int = x");
        let priv_info = env.decls.get("total").expect("total");
        assert_eq!(priv_info.visibility, Visibility::Private);
        let pub_info = env.decls.get("calc").expect("calc");
        assert_eq!(pub_info.visibility, Visibility::Public);
    }

    #[test]
    fn const_visibility() {
        let env = collect_src("const A = 1\npub const B = 2");
        assert_eq!(env.decls.get("A").unwrap().visibility, Visibility::Private);
        assert_eq!(env.decls.get("B").unwrap().visibility, Visibility::Public);
    }

    #[test]
    fn decl_module_tagged() {
        let env = collect_src("module Commerce\nenum Status = Active | Inactive");
        let info = env
            .lookup_decl_qualified("Commerce", "Status")
            .expect("Commerce::Status decl");
        assert_eq!(info.module.as_deref(), Some("Commerce"));
    }

    #[test]
    fn decl_module_none_without_module_decl() {
        let env = collect_src("enum Status = Active | Inactive");
        let info = env.lookup_decl("Status").expect("Status decl");
        assert_eq!(info.module, None);
    }

    #[test]
    fn multi_file_collect_into() {
        let mut env = Env::new();
        let prog1 = {
            let tokens = lex::lex("module Commerce\npub enum Status = Active").unwrap();
            let mut p = Parser::new(tokens);
            p.parse_program().unwrap()
        };
        let prog2 = {
            let tokens = lex::lex("module Commerce\npub enum Payment = Pending | Done").unwrap();
            let mut p = Parser::new(tokens);
            p.parse_program().unwrap()
        };
        collect_into(&mut env, &prog1);
        collect_into(&mut env, &prog2);
        assert_eq!(env.module_name.as_deref(), Some("Commerce"));
        // Types are stored with qualified keys during collection
        assert!(env.types.contains_key("Commerce::Status"));
        assert!(env.types.contains_key("Commerce::Payment"));
        // After building working namespace, bare names are available
        env.build_working_namespace();
        assert!(env.types.contains_key("Status"));
        assert!(env.types.contains_key("Payment"));
        assert!(env.errors.is_empty());
    }

    #[test]
    fn visibility_error_on_private_import() {
        // Simulate: module A defines private type, module B imports it.
        // In a single file, we test the resolve pass catches it.
        let env = collect_src("module TestMod\nenum Secret = X | Y\nuse TestMod::Secret");
        // Collector doesn't enforce visibility — that's resolve's job.
        // But we can verify the declaration is tagged private.
        let info = env
            .lookup_decl_qualified("TestMod", "Secret")
            .expect("TestMod::Secret decl");
        assert_eq!(info.visibility, Visibility::Private);
        assert_eq!(info.module.as_deref(), Some("TestMod"));
    }

    // ── DDR-043: Alias elaboration tests ─────────────────────────

    #[test]
    fn alias_to_builtin() {
        let env = collect_src("type Money = Real");
        let ty = env.types.get("Money").expect("Money type");
        assert!(
            matches!(ty, Ty::Alias(n, inner) if n == "Money" && matches!(inner.as_ref(), Ty::Builtin(BuiltinTy::Real))),
            "expected Alias(Money, Builtin(Real)), got {ty:?}"
        );
    }

    #[test]
    fn alias_to_tuple() {
        let env = collect_src("type Coord = (Int, Int)");
        let ty = env.types.get("Coord").expect("Coord type");
        assert!(
            matches!(ty, Ty::Alias(n, inner) if n == "Coord" && matches!(inner.as_ref(), Ty::Tuple(_))),
            "expected Alias(Coord, Tuple(...)), got {ty:?}"
        );
        if let Ty::Alias(_, inner) = ty {
            if let Ty::Tuple(ts) = inner.as_ref() {
                assert_eq!(ts.len(), 2);
            }
        }
    }

    #[test]
    fn alias_to_collection() {
        let env = collect_src("type Users = Set<Id>");
        let ty = env.types.get("Users").expect("Users type");
        assert!(
            matches!(ty, Ty::Alias(n, inner) if n == "Users" && matches!(inner.as_ref(), Ty::Set(_))),
            "expected Alias(Users, Set(...)), got {ty:?}"
        );
    }

    #[test]
    fn alias_to_map() {
        let env = collect_src("type Ledger = Map<Id, Real>");
        let ty = env.types.get("Ledger").expect("Ledger type");
        assert!(
            matches!(ty, Ty::Alias(n, inner) if n == "Ledger" && matches!(inner.as_ref(), Ty::Map(_, _))),
            "expected Alias(Ledger, Map(...)), got {ty:?}"
        );
    }

    #[test]
    fn alias_to_function_type() {
        let env = collect_src("type Handler = Int -> Bool");
        let ty = env.types.get("Handler").expect("Handler type");
        assert!(
            matches!(ty, Ty::Alias(n, inner) if n == "Handler" && matches!(inner.as_ref(), Ty::Fn(_, _))),
            "expected Alias(Handler, Fn(...)), got {ty:?}"
        );
    }

    #[test]
    fn enum_single_variant() {
        // `enum Status = Pending` → single-variant enum
        let env = collect_src("enum Status = Pending");
        let ty = env.types.get("Status").expect("Status type");
        assert!(
            matches!(ty, Ty::Enum(n, ctors) if n == "Status" && ctors == &["Pending"]),
            "expected Enum(Status, [Pending]), got {ty:?}"
        );
    }

    #[test]
    fn enum_via_enum_keyword() {
        let env = collect_src("enum Color = Red | Green | Blue");
        let ty = env.types.get("Color").expect("Color type");
        assert!(
            matches!(ty, Ty::Enum(n, ctors) if n == "Color" && ctors.len() == 3),
            "expected Enum(Color, [Red, Green, Blue]), got {ty:?}"
        );
    }

    #[test]
    fn struct_via_struct_keyword() {
        let env = collect_src("struct Point { x: Int, y: Int }");
        let ty = env.types.get("Point").expect("Point type");
        assert!(
            matches!(ty, Ty::Record(n, fields) if n == "Point" && fields.len() == 2),
            "expected Record(Point, [x, y]), got {ty:?}"
        );
    }
}
