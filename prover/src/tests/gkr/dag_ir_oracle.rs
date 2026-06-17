//! Task 6 — oracle-hook SPIKE (GATE before broad lowering).
//!
//! Proves that the new DAG-IR reference evaluator
//! (`cs::gkr_compiler::dag_ir::eval::eval_layer_root`) can reproduce the
//! **prover's authoritative per-relation values** on three representative
//! relation shapes, using a HAND-BUILT `DagCircuit` (one layer, four roots).
//!
//! The value oracle, binding context (`RefCtx`), and the resolvers fed to the
//! evaluator are the SHARED ones in [`super::dag_ir_reference`] — the same
//! ground truth the Task-13 differential harness uses (controller
//! ambiguity-resolution #1: DRY the reference, no verbatim duplication). This
//! spike additionally hand-lowers each relation's expression(s) into DAG roots
//! to confirm the evaluator + reference agree before any general `lower_dag`
//! is exercised; Task 13 replaces the hand lowering with `lower_dag`.

use std::collections::BTreeSet;

use cs::definitions::gkr::NoFieldLinearRelation;
use cs::definitions::GKRAddress;
use cs::gkr_compiler::dag_ir::{
    eval_layer_root, ArenaBuilder, BatchingOrder, ChallengeKey, ChallengePower, ChallengeRef,
    DagLayer, ExprId, Resolvers, Root, RootId, SinkId, SourceKind,
};
use cs::gkr_compiler::test_support::{build_add_sub_artifact, sample_relations};
use cs::gkr_compiler::{NoFieldGKRRelation, NoFieldMaxQuadraticGKRRelation};

use super::dag_ir_reference::{
    collect_addresses, read_place_to_address, reference_relation_values, RefChallengeResolver,
    RefCtx, RefLookupResolver, RefVirtualSetupResolver, StorageReadResolver,
};

// ── Hand lowering of each relation's expression(s) into DAG roots ──────────

/// `GKRAddress` → `ExprId` via the shared `ReadPlace` mapping. The hand lowering
/// reads exactly the same places the shared `StorageReadResolver` resolves.
fn read_expr(arena: &mut ArenaBuilder, addr: GKRAddress) -> ExprId {
    // mirror dag_ir::lower::map_address for the base places used here.
    let place = match addr {
        GKRAddress::BaseLayerWitness(o) => cs::gkr_compiler::dag_ir::ReadPlace::BaseLayerWitness {
            column: o,
        },
        GKRAddress::BaseLayerMemory(o) => cs::gkr_compiler::dag_ir::ReadPlace::BaseLayerMemory {
            column: o,
        },
        GKRAddress::Setup(o) => cs::gkr_compiler::dag_ir::ReadPlace::Setup { column: o },
        other => panic!("address {:?} cannot be lowered to a ReadPlace here", other),
    };
    // sanity: the resolver inverse must round-trip.
    debug_assert_eq!(read_place_to_address(&place), addr);
    let src = arena.intern_source(SourceKind::Read { place });
    arena.source_expr(src)
}

/// Intern a `Constant`.
fn const_expr(arena: &mut ArenaBuilder, value: u32) -> ExprId {
    let src = arena.intern_source(SourceKind::Constant { value });
    arena.source_expr(src)
}

/// Lower `NoFieldLinearRelation` to `constant + Σ c·addr`.
fn lower_linear(arena: &mut ArenaBuilder, lin: &NoFieldLinearRelation) -> ExprId {
    let mut terms = Vec::new();
    if lin.constant != 0 {
        terms.push(const_expr(arena, lin.constant));
    }
    for (c, addr) in lin.linear_terms.iter() {
        let a = read_expr(arena, *addr);
        if *c == 1 {
            terms.push(a);
        } else {
            let cc = const_expr(arena, *c);
            terms.push(arena.mul(vec![cc, a]));
        }
    }
    if terms.is_empty() {
        const_expr(arena, 0)
    } else if terms.len() == 1 {
        terms[0]
    } else {
        arena.add(terms)
    }
}

/// Lower the `MaxQuadratic` relation math: `constant + Σ_quad c·a·b + Σ_lin c·a`.
fn lower_constraint(arena: &mut ArenaBuilder, rel: &NoFieldMaxQuadraticGKRRelation) -> ExprId {
    let mut terms = Vec::new();
    if rel.constant != 0 {
        terms.push(const_expr(arena, rel.constant));
    }
    for (a, set) in rel.quadratic_terms.iter() {
        let a_expr = read_expr(arena, *a);
        for (c, b) in set.iter() {
            let b_expr = read_expr(arena, *b);
            let prod = arena.mul(vec![a_expr, b_expr]);
            if *c == 1 {
                terms.push(prod);
            } else {
                let cc = const_expr(arena, *c);
                terms.push(arena.mul(vec![cc, prod]));
            }
        }
    }
    for (c, a) in rel.linear_terms.iter() {
        let a_expr = read_expr(arena, *a);
        if *c == 1 {
            terms.push(a_expr);
        } else {
            let cc = const_expr(arena, *c);
            terms.push(arena.mul(vec![cc, a_expr]));
        }
    }
    if terms.is_empty() {
        const_expr(arena, 0)
    } else if terms.len() == 1 {
        terms[0]
    } else {
        arena.add(terms)
    }
}

/// Lower the materialized-base lookup pair to its two output expressions
/// `[num = b + d, den = b * d]` where `b = gamma + in0`, `d = gamma + in1`.
fn lower_lookup_pair(arena: &mut ArenaBuilder, input: [GKRAddress; 2]) -> [ExprId; 2] {
    let gamma_src = arena.intern_source(SourceKind::Challenge {
        reference: ChallengeRef {
            key: ChallengeKey::LookupAdditive,
            power: ChallengePower::One,
        },
    });
    let gamma = arena.source_expr(gamma_src);

    let in0 = read_expr(arena, input[0]);
    let in1 = read_expr(arena, input[1]);

    let b = arena.add(vec![gamma, in0]);
    let d = arena.add(vec![gamma, in1]);

    let num = arena.add(vec![b, d]);
    let den = arena.mul(vec![b, d]);
    [num, den]
}

// ── relation selection ──────────────────────────────────────────────────────

/// First `EnforceSingleMaxQuadraticConstraint` in layer 0 of the add_sub
/// artifact, plus the first `LookupPairFromMaterializedBaseInputs`. Returns
/// `(constraint, lookup_pair)`.
fn pick_from_add_sub() -> (NoFieldGKRRelation, NoFieldGKRRelation) {
    let artifact = build_add_sub_artifact();
    let layer = &artifact.layers[0];
    let mut constraint = None;
    let mut pair = None;
    for g in layer
        .gates
        .iter()
        .chain(layer.gates_with_external_connections.iter())
    {
        match &g.enforced_relation {
            NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint { .. }
                if constraint.is_none() =>
            {
                constraint = Some(g.enforced_relation.clone());
            }
            NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs { .. } if pair.is_none() => {
                pair = Some(g.enforced_relation.clone());
            }
            _ => {}
        }
    }
    (
        constraint.expect("add_sub layer 0 must contain an EnforceSingleMaxQuadraticConstraint"),
        pair.expect("add_sub layer 0 must contain a LookupPairFromMaterializedBaseInputs"),
    )
}

/// Canonical `LinearBaseFieldRelation` fixture. (`build_add_sub_artifact` does
/// not emit this variant — it is fully lowered into caches/constraints — so we
/// take the canonical single-output linear relation from the shared fixtures.)
fn pick_linear() -> NoFieldGKRRelation {
    sample_relations()
        .into_iter()
        .find(|(name, _)| *name == "LinearBaseFieldRelation")
        .expect("LinearBaseFieldRelation fixture must exist")
        .1
}

// ── the spike test ──────────────────────────────────────────────────────────

#[test]
fn dag_ir_oracle_matches_prover_reference_on_three_roots() {
    const TRACE_LEN: usize = 2;
    const ROW: usize = 0;

    let linear = pick_linear();
    let (constraint, lookup_pair) = pick_from_add_sub();

    // Collect every base address the three relations read, and bind a single
    // fixed random assignment for each (the shared witness/memory source).
    let mut addrs = BTreeSet::new();
    collect_addresses(&linear, &mut addrs);
    collect_addresses(&constraint, &mut addrs);
    collect_addresses(&lookup_pair, &mut addrs);

    let ctx = RefCtx::new(&addrs, TRACE_LEN);

    // ── Reference (authoritative) values ──
    let ref_linear = reference_relation_values(&linear, ROW, &ctx).expect("linear arm");
    let ref_pair = reference_relation_values(&lookup_pair, ROW, &ctx).expect("pair arm");
    let ref_constraint =
        reference_relation_values(&constraint, ROW, &ctx).expect("constraint arm");
    assert_eq!(ref_linear.len(), 1);
    assert_eq!(ref_pair.len(), 2, "lookup pair must produce (num, den)");
    assert_eq!(ref_constraint.len(), 1);

    // ── Hand-built DAG circuit: one layer, four roots ──
    //   root 0: linear           Output(slot 0)   — claim-bearing
    //   root 1: lookup pair num   Output(slot 0)   — claim-bearing
    //   root 2: lookup pair den   Output(slot 1)   — claim-bearing
    //   root 3: constraint        Constraint
    let mut arena = ArenaBuilder::new();

    let linear_input = match &linear {
        NoFieldGKRRelation::LinearBaseFieldRelation { input, .. } => input,
        _ => unreachable!(),
    };
    let linear_expr = lower_linear(&mut arena, linear_input);

    let pair_inputs = match &lookup_pair {
        NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs { input, .. } => *input,
        _ => unreachable!(),
    };
    let [num_expr, den_expr] = lower_lookup_pair(&mut arena, pair_inputs);

    let constraint_input = match &constraint {
        NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint { input, .. } => input,
        _ => unreachable!(),
    };
    let constraint_expr = lower_constraint(&mut arena, constraint_input);

    let roots = vec![
        Root::Output {
            expr: linear_expr,
            sink: SinkId(0),
        },
        Root::Output {
            expr: num_expr,
            sink: SinkId(1),
        },
        Root::Output {
            expr: den_expr,
            sink: SinkId(2),
        },
        Root::Constraint {
            expr: constraint_expr,
        },
    ];
    let batching = BatchingOrder {
        roots: vec![RootId(0), RootId(1), RootId(2), RootId(3)],
    };
    let layer = DagLayer {
        sources: arena.sources().to_vec(),
        exprs: arena.exprs().to_vec(),
        roots,
        sinks: Vec::new(),
        batching,
        origins: std::collections::BTreeMap::new(),
    };

    // ── Bind resolvers to the SAME RefCtx ──
    let read = StorageReadResolver { ctx: &ctx };
    let challenge = RefChallengeResolver { ctx: &ctx };
    let lookup = RefLookupResolver { ctx: &ctx };
    let virtual_setup = RefVirtualSetupResolver { ctx: &ctx };
    let resolvers = Resolvers {
        read: &read,
        lookup: &lookup,
        virtual_setup: &virtual_setup,
        challenge: &challenge,
    };

    // ── Evaluate each DAG root and compare to the matching reference value ──
    let eval_linear = eval_layer_root(&layer, RootId(0), ROW, &resolvers);
    let eval_num = eval_layer_root(&layer, RootId(1), ROW, &resolvers);
    let eval_den = eval_layer_root(&layer, RootId(2), ROW, &resolvers);
    let eval_constraint = eval_layer_root(&layer, RootId(3), ROW, &resolvers);

    assert_eq!(
        eval_linear, ref_linear[0],
        "LinearBaseFieldRelation: DAG-IR value diverged from prover reference"
    );
    assert_eq!(
        eval_num, ref_pair[0],
        "LookupPair num (slot 0): DAG-IR value diverged from prover reference"
    );
    assert_eq!(
        eval_den, ref_pair[1],
        "LookupPair den (slot 1): DAG-IR value diverged from prover reference"
    );
    assert_eq!(
        eval_constraint, ref_constraint[0],
        "EnforceSingleMaxQuadraticConstraint: DAG-IR value diverged from prover reference"
    );

    println!("DAG-IR oracle spike: all 3 shapes (4 roots) matched the prover reference.");
    println!("  linear      = {:?}", eval_linear);
    println!("  pair num    = {:?}", eval_num);
    println!("  pair den    = {:?}", eval_den);
    println!(
        "  constraint  = {:?} (must equal the kernel's vanishing value)",
        eval_constraint
    );
}
