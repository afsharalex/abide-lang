//! Pass 1: Collect all top-level declarations into the environment.
//!
//! Walks the parsed AST and registers every type, entity, system,
//! pred, prop, verify, scene, proof, lemma, const, and fn declaration.

use crate::ast;

use super::env::{DeclInfo, DeclKind, Env};
use super::types::{
    BinOp, BuiltinTy, EAction, EAxiom, EConst, EEntity, EEvent, EEventAction, EExpr, EField, EFn,
    ELemma, ENextItem, EPattern, EPred, EProp, EScene, ESceneGiven, ESceneWhen, ESystem, ETheorem,
    EVerify, Literal, Quantifier, Ty, UnOp,
};

/// Collect all declarations from a parsed program into an `Env`.
pub fn collect(program: &ast::Program) -> Env {
    let mut env = Env::new();
    for decl in &program.decls {
        collect_top_decl(&mut env, decl);
    }
    env
}

fn collect_top_decl(env: &mut Env, decl: &ast::TopDecl) {
    match decl {
        ast::TopDecl::Module(d) => {
            env.module_name = Some(d.name.clone());
        }
        ast::TopDecl::Include(d) => {
            env.includes.push(d.path.clone());
        }
        ast::TopDecl::Use(_) => {} // future
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
    }
}

// ── Type declarations ────────────────────────────────────────────────

fn collect_type(env: &mut Env, td: &ast::TypeDecl) {
    let name = &td.name;
    // Check for single-variant alias to builtin
    if td.variants.len() == 1 {
        if let ast::TypeVariant::Simple {
            name: ref target, ..
        } = td.variants[0]
        {
            if let Some(builtin) = resolve_builtin(target) {
                let ty = Ty::Alias(name.clone(), Box::new(Ty::Builtin(builtin)));
                let info = DeclInfo {
                    kind: DeclKind::Type,
                    name: name.clone(),
                    ty: Some(ty.clone()),
                };
                env.add_decl(name, info);
                env.types.insert(name.clone(), ty);
                return;
            }
        }
    }

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
    let info = DeclInfo {
        kind: DeclKind::Type,
        name: name.clone(),
        ty: Some(ty.clone()),
    };
    env.add_decl(name, info);
    env.types.insert(name.clone(), ty);
}

fn collect_record(env: &mut Env, rd: &ast::RecordDecl) {
    let name = &rd.name;
    let fields: Vec<(String, Ty)> = rd
        .fields
        .iter()
        .map(|f| (f.name.clone(), resolve_type_ref(&f.ty)))
        .collect();
    let ty = Ty::Record(name.clone(), fields);
    let info = DeclInfo {
        kind: DeclKind::Type,
        name: name.clone(),
        ty: Some(ty.clone()),
    };
    env.add_decl(name, info);
    env.types.insert(name.clone(), ty);
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
    };
    let info = DeclInfo {
        kind: DeclKind::Entity,
        name: name.clone(),
        ty: None,
    };
    env.add_decl(name, info);
    env.entities.insert(name.clone(), ee);
}

fn collect_field(f: &ast::FieldDecl) -> EField {
    EField {
        name: f.name.clone(),
        ty: resolve_type_ref(&f.ty),
        default: f.default.as_ref().map(collect_expr),
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
            ast::Contract::Ensures { .. } => None,
        })
        .collect();
    let body: Vec<EExpr> = a.body.iter().map(collect_expr).collect();
    EAction {
        name: a.name.clone(),
        refs,
        params,
        requires,
        body,
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
    };
    let info = DeclInfo {
        kind: DeclKind::System,
        name: name.clone(),
        ty: None,
    };
    env.add_decl(name, info);
    env.systems.insert(name.clone(), es);
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
            ast::Contract::Ensures { .. } => None,
        })
        .collect();
    let ensures: Vec<EExpr> = ev
        .contracts
        .iter()
        .filter_map(|c| match c {
            ast::Contract::Ensures { expr, .. } => Some(collect_expr(expr)),
            ast::Contract::Requires { .. } => None,
        })
        .collect();
    let body: Vec<EEventAction> = ev.items.iter().map(collect_event_item).collect();
    EEvent {
        name: ev.name.clone(),
        params,
        requires,
        ensures,
        body,
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
        EExpr::Call(_, callee, args) => {
            if let EExpr::Qual(_, sys, ev) = callee.as_ref() {
                return EEventAction::CrossCall(sys.clone(), ev.clone(), extract_named_args(args));
            }
            // Action apply: o.action(args)
            if let EExpr::Field(_, target, action) = callee.as_ref() {
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
        EExpr::CallR(_, callee, refs, args) => {
            if let EExpr::Field(_, target, action) = callee.as_ref() {
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
            EExpr::NamedPair(_, _, inner) => *inner.clone(),
            other => other.clone(),
        })
        .collect()
}

fn collect_next_item(ni: &ast::NextItem) -> ENextItem {
    match ni {
        ast::NextItem::When {
            condition, event, ..
        } => ENextItem::When(collect_expr(condition), expr_to_text(&event.kind)),
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

// ── Predicates, properties, verify, scene, proof, lemma ──────────────

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
    };
    let info = DeclInfo {
        kind: DeclKind::Pred,
        name: name.clone(),
        ty: None,
    };
    env.add_decl(name, info);
    env.preds.insert(name.clone(), ep);
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
    };
    let info = DeclInfo {
        kind: DeclKind::Prop,
        name: name.clone(),
        ty: None,
    };
    env.add_decl(name, info);
    env.props.insert(name.clone(), ep);
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
    };
    let key = format!("verify:{name}");
    let info = DeclInfo {
        kind: DeclKind::Verify,
        name: key.clone(),
        ty: None,
    };
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
    };
    let key = format!("scene:{name}");
    let info = DeclInfo {
        kind: DeclKind::Scene,
        name: key.clone(),
        ty: None,
    };
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
            Box::new(EExpr::Var(unresolved, obj.clone())),
            field.clone(),
        ),
        ast::InvocArg::Simple { name, .. } | ast::InvocArg::State { name, .. } => {
            EExpr::Var(unresolved, name.clone())
        }
        ast::InvocArg::Int { value, .. } => {
            EExpr::Lit(Ty::Builtin(BuiltinTy::Int), Literal::Int(*value))
        }
        ast::InvocArg::Real { value, .. } => {
            EExpr::Lit(Ty::Builtin(BuiltinTy::Real), Literal::Real(*value))
        }
        ast::InvocArg::Float { value, .. } => {
            let v = parse_float_text(value);
            EExpr::Lit(Ty::Builtin(BuiltinTy::Float), Literal::Float(v))
        }
        ast::InvocArg::Str { value, .. } => {
            EExpr::Lit(Ty::Builtin(BuiltinTy::String), Literal::Str(value.clone()))
        }
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
    };
    let info = DeclInfo {
        kind: DeclKind::Theorem,
        name: name.clone(),
        ty: None,
    };
    env.add_decl(name, info);
    env.theorems.push(et);
}

fn collect_axiom(env: &mut Env, ad: &ast::AxiomDecl) {
    let name = &ad.name;
    let ea = EAxiom {
        name: name.clone(),
        body: collect_expr(&ad.body),
    };
    let info = DeclInfo {
        kind: DeclKind::Axiom,
        name: name.clone(),
        ty: None,
    };
    env.add_decl(name, info);
    env.axioms.push(ea);
}

fn collect_lemma(env: &mut Env, ld: &ast::LemmaDecl) {
    let name = &ld.name;
    let el = ELemma {
        name: name.clone(),
        body: ld.body.iter().map(collect_expr).collect(),
    };
    let info = DeclInfo {
        kind: DeclKind::Lemma,
        name: name.clone(),
        ty: None,
    };
    env.add_decl(name, info);
    env.lemmas.push(el);
}

fn collect_const(env: &mut Env, cd: &ast::ConstDecl) {
    let name = &cd.name;
    let ec = EConst {
        name: name.clone(),
        body: collect_expr(&cd.value),
    };
    let info = DeclInfo {
        kind: DeclKind::Const,
        name: name.clone(),
        ty: None,
    };
    env.add_decl(name, info);
    env.consts.push(ec);
}

fn collect_fn(env: &mut Env, fd: &ast::FnDecl) {
    let name = &fd.name;
    let params: Vec<(String, Ty)> = fd
        .params
        .iter()
        .map(|p| (p.name.clone(), resolve_type_ref(&p.ty)))
        .collect();
    let ret = resolve_type_ref(&fd.ret_type);
    let ef = EFn {
        name: name.clone(),
        params,
        ret_ty: ret,
        body: collect_expr(&fd.body),
    };
    let info = DeclInfo {
        kind: DeclKind::Fn,
        name: name.clone(),
        ty: None,
    };
    env.add_decl(name, info);
    env.fns.push(ef);
}

// ── Expression collection ────────────────────────────────────────────

#[allow(clippy::too_many_lines)]
fn collect_expr(expr: &ast::Expr) -> EExpr {
    let u = || Ty::Unresolved("?".to_owned());
    let bool_ty = || Ty::Builtin(BuiltinTy::Bool);
    let int_ty = || Ty::Builtin(BuiltinTy::Int);

    match &expr.kind {
        ast::ExprKind::Var(n) => EExpr::Var(u(), n.clone()),
        ast::ExprKind::Int(i) => EExpr::Lit(int_ty(), Literal::Int(*i)),
        ast::ExprKind::Real(d) => EExpr::Lit(Ty::Builtin(BuiltinTy::Real), Literal::Real(*d)),
        ast::ExprKind::Float(s) => EExpr::Lit(
            Ty::Builtin(BuiltinTy::Float),
            Literal::Float(parse_float_text(s)),
        ),
        ast::ExprKind::Str(s) => {
            EExpr::Lit(Ty::Builtin(BuiltinTy::String), Literal::Str(s.clone()))
        }
        ast::ExprKind::True => EExpr::Lit(bool_ty(), Literal::Bool(true)),
        ast::ExprKind::False => EExpr::Lit(bool_ty(), Literal::Bool(false)),

        ast::ExprKind::Qual2(s, n) => EExpr::Qual(u(), s.clone(), n.clone()),
        ast::ExprKind::Qual3(s, t, n) => EExpr::Qual(u(), format!("{s}::{t}"), n.clone()),
        ast::ExprKind::State1(c) => EExpr::Var(u(), c.clone()),
        ast::ExprKind::State2(t, c) => EExpr::Qual(u(), t.clone(), c.clone()),
        ast::ExprKind::State3(s, t, c) => EExpr::Qual(u(), format!("{s}::{t}"), c.clone()),

        ast::ExprKind::Field(e, f) => EExpr::Field(u(), Box::new(collect_expr(e)), f.clone()),
        ast::ExprKind::Prime(e) => EExpr::Prime(u(), Box::new(collect_expr(e))),
        ast::ExprKind::Call(callee, args) => EExpr::Call(
            u(),
            Box::new(collect_expr(callee)),
            args.iter().map(collect_expr).collect(),
        ),
        ast::ExprKind::CallR(callee, refs, args) => EExpr::CallR(
            u(),
            Box::new(collect_expr(callee)),
            refs.iter().map(collect_expr).collect(),
            args.iter().map(collect_expr).collect(),
        ),

        // Unary ops
        ast::ExprKind::Neg(e) => EExpr::UnOp(int_ty(), UnOp::Neg, Box::new(collect_expr(e))),
        ast::ExprKind::Not(e) => EExpr::UnOp(bool_ty(), UnOp::Not, Box::new(collect_expr(e))),
        ast::ExprKind::Card(e) => EExpr::Card(u(), Box::new(collect_expr(e))),

        // Binary ops: arithmetic
        ast::ExprKind::Add(a, b) => bin_op(u(), BinOp::Add, a, b),
        ast::ExprKind::Sub(a, b) => bin_op(u(), BinOp::Sub, a, b),
        ast::ExprKind::Mul(a, b) => bin_op(u(), BinOp::Mul, a, b),
        ast::ExprKind::Div(a, b) => bin_op(u(), BinOp::Div, a, b),
        ast::ExprKind::Mod(a, b) => bin_op(u(), BinOp::Mod, a, b),

        // Binary ops: comparison (result is Bool)
        ast::ExprKind::Eq(a, b) => bin_op(bool_ty(), BinOp::Eq, a, b),
        ast::ExprKind::NEq(a, b) => bin_op(bool_ty(), BinOp::NEq, a, b),
        ast::ExprKind::Lt(a, b) => bin_op(bool_ty(), BinOp::Lt, a, b),
        ast::ExprKind::Gt(a, b) => bin_op(bool_ty(), BinOp::Gt, a, b),
        ast::ExprKind::Le(a, b) => bin_op(bool_ty(), BinOp::Le, a, b),
        ast::ExprKind::Ge(a, b) => bin_op(bool_ty(), BinOp::Ge, a, b),

        // Binary ops: logical (result is Bool)
        ast::ExprKind::And(a, b) => bin_op(bool_ty(), BinOp::And, a, b),
        ast::ExprKind::Or(a, b) => bin_op(bool_ty(), BinOp::Or, a, b),
        ast::ExprKind::Impl(a, b) => bin_op(bool_ty(), BinOp::Implies, a, b),

        // Binary ops: composition
        ast::ExprKind::Unord(a, b) => bin_op(u(), BinOp::Unord, a, b),
        ast::ExprKind::Conc(a, b) => bin_op(u(), BinOp::Conc, a, b),
        ast::ExprKind::Xor(a, b) => bin_op(u(), BinOp::Xor, a, b),

        // Membership
        ast::ExprKind::In(a, b) => EExpr::In(
            bool_ty(),
            Box::new(collect_expr(a)),
            Box::new(collect_expr(b)),
        ),

        // Temporal
        ast::ExprKind::Always(e) => EExpr::Always(u(), Box::new(collect_expr(e))),
        ast::ExprKind::Eventually(e) => EExpr::Eventually(u(), Box::new(collect_expr(e))),
        ast::ExprKind::AssertExpr(e) => EExpr::Assert(u(), Box::new(collect_expr(e))),

        // Assignment
        ast::ExprKind::Assign(a, b) => {
            EExpr::Assign(u(), Box::new(collect_expr(a)), Box::new(collect_expr(b)))
        }
        ast::ExprKind::NamedPair(n, e) => {
            EExpr::NamedPair(u(), n.clone(), Box::new(collect_expr(e)))
        }
        ast::ExprKind::Seq(a, b) => {
            EExpr::Seq(u(), Box::new(collect_expr(a)), Box::new(collect_expr(b)))
        }
        ast::ExprKind::SameStep(a, b) => {
            EExpr::SameStep(u(), Box::new(collect_expr(a)), Box::new(collect_expr(b)))
        }
        ast::ExprKind::Pipe(a, b) => {
            EExpr::Pipe(u(), Box::new(collect_expr(a)), Box::new(collect_expr(b)))
        }

        // Quantifiers
        ast::ExprKind::All(v, tr, body) => EExpr::Quant(
            bool_ty(),
            Quantifier::All,
            v.clone(),
            resolve_type_ref(tr),
            Box::new(collect_expr(body)),
        ),
        ast::ExprKind::Exists(v, tr, body) => EExpr::Quant(
            bool_ty(),
            Quantifier::Exists,
            v.clone(),
            resolve_type_ref(tr),
            Box::new(collect_expr(body)),
        ),
        ast::ExprKind::SomeQ(v, tr, body) => EExpr::Quant(
            bool_ty(),
            Quantifier::Some,
            v.clone(),
            resolve_type_ref(tr),
            Box::new(collect_expr(body)),
        ),
        ast::ExprKind::NoQ(v, tr, body) => EExpr::Quant(
            bool_ty(),
            Quantifier::No,
            v.clone(),
            resolve_type_ref(tr),
            Box::new(collect_expr(body)),
        ),
        ast::ExprKind::OneQ(v, tr, body) => EExpr::Quant(
            bool_ty(),
            Quantifier::One,
            v.clone(),
            resolve_type_ref(tr),
            Box::new(collect_expr(body)),
        ),
        ast::ExprKind::LoneQ(v, tr, body) => EExpr::Quant(
            bool_ty(),
            Quantifier::Lone,
            v.clone(),
            resolve_type_ref(tr),
            Box::new(collect_expr(body)),
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
            EExpr::Let(bs, Box::new(collect_expr(body)))
        }

        // Lambda
        ast::ExprKind::Lambda(params, body) => {
            let ps: Vec<(String, Ty)> = params
                .iter()
                .map(|p| (p.name.clone(), resolve_type_ref(&p.ty)))
                .collect();
            EExpr::Lam(ps, None, Box::new(collect_expr(body)))
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
            )
        }

        // Tuple literal
        ast::ExprKind::TupleLit(es) => EExpr::TupleLit(u(), es.iter().map(collect_expr).collect()),

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
            EExpr::Match(Box::new(scrut), earms)
        }

        // Stubs
        ast::ExprKind::Sorry => EExpr::Sorry,
        ast::ExprKind::Todo => EExpr::Todo,
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

fn bin_op(ty: Ty, op: BinOp, a: &ast::Expr, b: &ast::Expr) -> EExpr {
    EExpr::BinOp(ty, op, Box::new(collect_expr(a)), Box::new(collect_expr(b)))
}

fn parse_float_text(s: &str) -> f64 {
    let stripped = s.strip_suffix('f').unwrap_or(s);
    stripped.parse().unwrap_or(0.0)
}
