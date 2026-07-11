//! Task 10: G2 — the backward-VM protocol-parity micro matrix.
//!
//! For 5 micro relation families x 3 `MaterializationPolicy` legs, the
//! backward-VM instrument (`gkr_eval_isa::bwd::interpret_bwd_row` driven per
//! round/role/row) must reproduce the production prover's per-round transcript
//! (`run_layer_oracle`, Task 9) EXACTLY: committed `[E; 4]` monomials,
//! folding challenges, claim/eq-prefactor chains, and the final folded source
//! evaluations. The oracle is production; any mismatch is a real signal.
//!
//! # The pairing mapping (production LOW/HIGH halves vs instrument (2x, 2x+1))
//!
//! The production loop folds the MOST-significant index bit first: at round
//! `r` the surviving representation `F_r` (size `2^(k-r)`) is paired as
//! `(F_r(x), F_r(x + half))` (`input_in_base.rs` splits at `half`), the pair
//! bit being bit `k-r-1` of the ORIGINAL index, and folds
//! `F_{r+1}(x) = F_r(x) + z_r·(F_r(x+half) − F_r(x))` with the round-`r`
//! transcript challenge `z_r`. The eq layer used at round `r`
//! (`eq_polys[k-r-1]`, built by `make_eq_poly_in_full`) is indexed by the
//! surviving LOW bits, with `prev_challenges[r+1]` at that index's MSB.
//!
//! The instrument folds the LEAST-significant bit first:
//! `f_{d+1}(y) = f_d(2y) + ch[d]·(f_d(2y+1) − f_d(2y))`, and pairs ADJACENT
//! entries `(2x, 2x+1)` of its depth-`r` representation.
//!
//! These reconcile under a pure re-indexing: give the instrument the
//! BIT-REVERSED view of every production column, `O(j) = P(rev_k(j))`, and
//! pass the drawn folding challenges in order (`ch = [z_0, z_1, ...]`). Then
//! instrument bit `d` is production bit `k-1-d`, so
//!   * the instrument's depth-`r` fold of `O` equals the production `F_r` up
//!     to index bit-reversal: `f_r(y) = F_r(rev_{k-r}(y))`;
//!   * the instrument pair bit (bit 0 of `f_r`'s index) IS the production pair
//!     bit `k-r-1`, with the pair's low element on the same side, so
//!     `Role::T0/T2` evaluate the same finite points of the same interpolant;
//!   * the surviving-row index maps by bit reversal, so the round-`r` eq
//!     weight for instrument row `y` is `eq[rev_{k-r-1}(y)]`.
//! With that, `q0 = Σ_y eq[rev(y)]·v_T0(y)` and `q2 = Σ_y eq[rev(y)]·v_T2(y)`
//! are exactly the production round polynomial's `g(0)` and `g(2)`.
//!
//! # Per-round assertions (brief steps (a)-(e), REV2 independent-direction)
//!
//! `per_round_reduced = [c0, c2]` are MONOMIAL coefficients (constant,
//! quadratic). `d_oracle` is derived FIRST from `(z, C, c0, c2)` via the
//! production sum-constraint identity, then:
//!   (a) `q0 == c0` and `q2 == c0 + 2·d_oracle + 4·c2`;
//!   (b) recovered `e == c0`, `c == c2`, `d == d_oracle`;
//!   (c) `recover_and_emit(z, claim, eq_prefactor, q0, q2)` == committed
//!       `round_coeffs[r]`;
//!   (d) replayed transcript (commit + draw) reproduces `folding_challenges`,
//!       and the claim/eq-prefactor chains match the capture round by round;
//!   (e) the instrument's full-depth fold of every input column equals the
//!       production `last_evaluations` line interpolated at `r_last`.
//!
//! # Synthetic columns
//!
//! Deterministic FNV-1a-mixed values generated LOCALLY (`mix(col, row)`), not
//! the `gkr_eval_isa` test-support generator (that one is an integration-test
//! `common` module, not importable from here). The constraint family's column
//! is boolean (constraint must hold pointwise — the production round-0
//! accumulator implicitly treats a satisfied constraint's `g(0)` contribution
//! as zero, and the combined claim gives it a zero output claim).

use std::alloc::Global;
use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;

use cs::definitions::{
    GKRAddress, VirtualSetupPoly, PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
    PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
};
use cs::gkr_compiler::dag_ir::{
    bwd_roots, lower_dag, validate, BatchingOrder, Bf, BwdRegime, ChallengeKey, ChallengePower,
    ChallengeRef, ChallengeResolver, ClaimInfo, DagLayer, Expr, ExprId, Ext, FieldKind,
    LookupResolver, LookupValueKind, PermutationSlot, ReadPlace, ReadResolver, Resolvers, Root,
    RootGroup, RootId, RootOrigin, RootSlot, SinkInfo, SinkKind, SourceId, SourceInfo, SourceKind,
    VirtualSetupKind, VirtualSetupResolver,
};
use cs::gkr_compiler::{
    GKRCircuitArtifact, GKRLayerDescription, GateArtifacts, NoFieldGKRRelation,
    NoFieldMaxQuadraticGKRRelation, NoFieldStructuredExpression,
};
use cs::tables::TableDriver;
use field::{Field, FieldExtension, FixedArrayConvertible, PrimeField};
use gkr_eval_isa::bwd::compile::{compile_distilled, BwdCompiledLayer};
use gkr_eval_isa::bwd::distill::{bind, distill, BwdBindings, DistilledLayer};
use gkr_eval_isa::bwd::interp::{interpret_bwd_row, sumcheck_fold_point, Role};
use gkr_eval_isa::bwd::source::{BwdSpecial, FoldState, MaterializationPolicy, OriginLeaf};
use gkr_eval_isa::fwd::compile::build_cross_layer_field_map;
use gkr_eval_isa::fwd::error::CompileError;
use riscv_transpiler::ir::FullUnsignedMachineDecoderConfig;
use riscv_transpiler::replayer::{ReplayerRam, ReplayerVM};
use riscv_transpiler::vm::{DelegationsAndFamiliesCounters, ReplayBuffer};
use riscv_transpiler::witness::{BigintDelegationDestinationHolder, DelegationWitness};
use transcript::Seed;
use worker::Worker;

use crate::gkr::prover::forward_loop;
use crate::gkr::prover::setup::GKRSetup;
use crate::gkr::prover::sumcheck_loop::test_harness::{
    recover_and_emit, run_layer_oracle, LayerOracleRun,
};
use crate::gkr::prover::transcript_utils::{commit_field_els, draw_random_field_els};
use crate::gkr::prover::GKRExternalChallenges;
use crate::gkr::sumcheck::access_and_fold::{
    BaseFieldPoly, ExtensionFieldPoly, GKRLayerSource, GKRStorage,
};
use crate::gkr::sumcheck::eq_poly::{
    evaluate_with_precomputed_eq, evaluate_with_precomputed_eq_ext, make_eq_poly_in_full,
};
use crate::gkr::sumcheck::{evaluate_eq_poly, evaluate_small_univariate_poly};
use crate::gkr::virtual_polys::range_check::materialize_virtual_range_check_setup_poly;
use crate::gkr::witness_gen::delegation_circuits::evaluate_gkr_witness_for_delegation_circuit;
use crate::gkr::witness_gen::family_circuits::GKRFullWitnessTrace;
use crate::tests::gkr::orchestration::common::{
    hardcoded_external_challenges, run_vm_and_capture, ProgramConfig,
};
use crate::tracers::oracles::transpiler_oracles::delegation::BigintDelegationOracle;

const FOLDING_STEPS: usize = 8;
const POLY_SIZE: usize = 1 << FOLDING_STEPS;
const BUDGET: usize = 16;
const POLICIES: [MaterializationPolicy; 3] = [
    MaterializationPolicy::AlwaysMaterialize,
    MaterializationPolicy::LazyUpTo(1),
    MaterializationPolicy::LazyUpTo(2),
];

// ── Field helpers ────────────────────────────────────────────────────────────

fn lift(b: Bf) -> Ext {
    <Ext as FieldExtension<Bf>>::from_base(b)
}

fn add(a: Ext, b: &Ext) -> Ext {
    let mut r = a;
    r.add_assign(b);
    r
}

fn sub(a: Ext, b: &Ext) -> Ext {
    let mut r = a;
    r.sub_assign(b);
    r
}

fn mul(a: Ext, b: &Ext) -> Ext {
    let mut r = a;
    r.mul_assign(b);
    r
}

fn inv(a: &Ext) -> Ext {
    a.inverse().expect("nonzero")
}

fn pow(base: Ext, n: u32) -> Ext {
    let mut acc = Ext::ONE;
    for _ in 0..n {
        acc.mul_assign(&base);
    }
    acc
}

fn interpolate(f0: Ext, f1: Ext, r: &Ext) -> Ext {
    add(mul(sub(f1, &f0), r), &f0)
}

fn minus_one_u32() -> u32 {
    let mut x = Bf::ZERO;
    x.sub_assign(&Bf::ONE);
    x.as_u32_reduced()
}

// ── Deterministic synthetic columns (local FNV-1a mix; choice noted above) ──

fn mix(a: u32, b: u32) -> u32 {
    let mut h: u32 = 0x811c9dc5;
    for byte in a.to_le_bytes().into_iter().chain(b.to_le_bytes()) {
        h ^= byte as u32;
        h = h.wrapping_mul(0x0100_0193);
    }
    h
}

fn ext_from(cs: [u32; 4]) -> Ext {
    let coeffs = cs.map(Bf::from_u32_with_reduction);
    <Ext as FieldExtension<Bf>>::from_coeffs(<Ext as FieldExtension<Bf>>::Coeffs::from_array(
        coeffs,
    ))
}

fn ext_scalar(tag: u32) -> Ext {
    ext_from([mix(tag, 0), mix(tag, 1), mix(tag, 2), mix(tag, 3)])
}

fn base_col(tag: u32, size: usize) -> Vec<Bf> {
    (0..size)
        .map(|row| Bf::from_u32_with_reduction(mix(tag, row as u32)))
        .collect()
}

/// Boolean column for the enforced constraint (must hold pointwise).
fn bool_col(tag: u32, size: usize) -> Vec<Bf> {
    (0..size)
        .map(|row| Bf::from_u32_with_reduction(mix(tag, row as u32) & 1))
        .collect()
}

fn ext_col(tag: u32, size: usize) -> Vec<Ext> {
    (0..size)
        .map(|row| {
            let r = row as u32;
            ext_from([
                mix(tag, 4 * r),
                mix(tag, 4 * r + 1),
                mix(tag, 4 * r + 2),
                mix(tag, 4 * r + 3),
            ])
        })
        .collect()
}

fn beta() -> Ext {
    ext_scalar(0xB577_0001)
}

fn gamma() -> Ext {
    ext_scalar(0x6AAA_0002)
}

fn lookup_mult() -> Ext {
    ext_scalar(0x3C3C_0003)
}

fn prev_challenges() -> Vec<Ext> {
    (0..FOLDING_STEPS)
        .map(|j| ext_scalar(0x5000_0000 + j as u32))
        .collect()
}

// ── Fixture (one relation family, both sides over the SAME column data) ─────

struct Family {
    name: &'static str,
    layer: GKRLayerDescription,
    dag: DagLayer,
    cross: HashMap<ReadPlace, FieldKind>,
    /// Input columns, production row order: (prover address, instrument place, data).
    base_inputs: Vec<(GKRAddress, ReadPlace, Vec<Bf>)>,
    ext_inputs: Vec<(GKRAddress, ReadPlace, Vec<Ext>)>,
    /// Output columns computed FROM the inputs (relation-consistent).
    base_outputs: Vec<(GKRAddress, Vec<Bf>)>,
    ext_outputs: Vec<(GKRAddress, Vec<Ext>)>,
    /// Batching slots in kernel-registration order: `Some(addr)` = output claim
    /// consuming that beta power; `None` = claim-only constraint slot.
    slot_claim_addrs: Vec<Option<GKRAddress>>,
}

fn build_storage(fam: &Family) -> GKRStorage<Bf, Ext> {
    let mut storage = GKRStorage::<Bf, Ext>::default();

    let mut layer_0 = GKRLayerSource::default();
    layer_0.layer_idx = 0;
    for (addr, _, vals) in &fam.base_inputs {
        layer_0
            .base_field_inputs
            .insert(*addr, BaseFieldPoly::new(vals.clone().into_boxed_slice()));
    }
    for (addr, _, vals) in &fam.ext_inputs {
        layer_0.extension_field_inputs.insert(
            *addr,
            ExtensionFieldPoly::new(vals.clone().into_boxed_slice()),
        );
    }
    storage.layers.push(layer_0);

    let mut layer_1 = GKRLayerSource::default();
    layer_1.layer_idx = 1;
    for (addr, vals) in &fam.base_outputs {
        layer_1
            .base_field_inputs
            .insert(*addr, BaseFieldPoly::new(vals.clone().into_boxed_slice()));
    }
    for (addr, vals) in &fam.ext_outputs {
        layer_1.extension_field_inputs.insert(
            *addr,
            ExtensionFieldPoly::new(vals.clone().into_boxed_slice()),
        );
    }
    storage.layers.push(layer_1);

    storage
}

// ── DagLayer builders ────────────────────────────────────────────────────────

fn rd(place: ReadPlace) -> SourceKind {
    SourceKind::Read { place }
}

fn dag_layer(sources: Vec<SourceKind>, exprs: Vec<Expr>, roots: Vec<Root>) -> DagLayer {
    let batching = BatchingOrder {
        roots: (0..roots.len()).map(|i| RootId(i as u32)).collect(),
    };
    DagLayer {
        sources: sources
            .into_iter()
            .map(|kind| SourceInfo { kind })
            .collect(),
        exprs,
        roots,
        batching,
        resolutions: BTreeMap::new(),
    }
}

fn out_root(
    expr: usize,
    relation_index: usize,
    offset: usize,
    field: FieldKind,
    output_slot: usize,
) -> Root {
    Root {
        expr: ExprId(expr as u32),
        materialize: Some(SinkInfo {
            kind: SinkKind::Inner { layer: 1, offset },
            field,
        }),
        claim: Some(ClaimInfo {
            origin: RootOrigin {
                group: RootGroup::Gates,
                relation_index,
                slot: RootSlot::Output(output_slot),
            },
        }),
    }
}

fn constraint_root(expr: usize, relation_index: usize) -> Root {
    Root {
        expr: ExprId(expr as u32),
        materialize: None,
        claim: Some(ClaimInfo {
            origin: RootOrigin {
                group: RootGroup::Gates,
                relation_index,
                slot: RootSlot::Constraint(0),
            },
        }),
    }
}

fn micro_layer(gates: Vec<GateArtifacts>) -> GKRLayerDescription {
    GKRLayerDescription {
        layer: 0,
        gates,
        gates_with_external_connections: vec![],
        cached_relations: BTreeMap::new(),
        intermediate_layer_width: None,
    }
}

// ── The 5 families ───────────────────────────────────────────────────────────

/// Ext-only product: `out = a·b` over two extension-field inputs.
fn family_ext_product() -> Family {
    let addr_a = GKRAddress::InnerLayer {
        layer: 0,
        offset: 0,
    };
    let addr_b = GKRAddress::InnerLayer {
        layer: 0,
        offset: 1,
    };
    let addr_out = GKRAddress::InnerLayer {
        layer: 1,
        offset: 0,
    };
    let pa = ReadPlace::LayerOutput {
        layer: 0,
        offset: 0,
    };
    let pb = ReadPlace::LayerOutput {
        layer: 0,
        offset: 1,
    };

    let a = ext_col(0xA0, POLY_SIZE);
    let b = ext_col(0xA1, POLY_SIZE);
    let out: Vec<Ext> = a.iter().zip(&b).map(|(x, y)| mul(*x, y)).collect();

    let layer = micro_layer(vec![GateArtifacts {
        output_layer: 1,
        enforced_relation: NoFieldGKRRelation::TrivialProduct {
            input: [addr_a, addr_b],
            output: addr_out,
        },
    }]);

    let dag = dag_layer(
        vec![rd(pa.clone()), rd(pb.clone())],
        vec![
            Expr::Source(SourceId(0)),
            Expr::Source(SourceId(1)),
            Expr::Mul(vec![ExprId(0), ExprId(1)]),
        ],
        vec![out_root(2, 0, 0, FieldKind::Ext, 0)],
    );

    let cross = HashMap::from_iter([(pa.clone(), FieldKind::Ext), (pb.clone(), FieldKind::Ext)]);

    Family {
        name: "ext_product",
        layer,
        dag,
        cross,
        base_inputs: vec![],
        ext_inputs: vec![(addr_a, pa, a), (addr_b, pb, b)],
        base_outputs: vec![],
        ext_outputs: vec![(addr_out, out)],
        slot_claim_addrs: vec![Some(addr_out)],
    }
}

/// Base-only product via `MaxQuadratic`: `out = a·b` over two base inputs,
/// output claim on a BASE poly.
fn family_base_product() -> Family {
    let addr_a = GKRAddress::BaseLayerWitness(0);
    let addr_b = GKRAddress::BaseLayerWitness(1);
    let addr_out = GKRAddress::InnerLayer {
        layer: 1,
        offset: 0,
    };
    let pa = ReadPlace::BaseLayerWitness { column: 0 };
    let pb = ReadPlace::BaseLayerWitness { column: 1 };

    let a = base_col(0xB0, POLY_SIZE);
    let b = base_col(0xB1, POLY_SIZE);
    let out: Vec<Bf> = a
        .iter()
        .zip(&b)
        .map(|(x, y)| {
            let mut t = *x;
            t.mul_assign(y);
            t
        })
        .collect();

    let relation = NoFieldMaxQuadraticGKRRelation {
        quadratic_terms: vec![(addr_a, vec![(1u32, addr_b)].into_boxed_slice())]
            .into_boxed_slice(),
        linear_terms: vec![].into_boxed_slice(),
        constant: 0,
    };
    let expression = NoFieldStructuredExpression::Product(vec![
        NoFieldStructuredExpression::Place(addr_a),
        NoFieldStructuredExpression::Place(addr_b),
    ]);
    let layer = micro_layer(vec![GateArtifacts {
        output_layer: 1,
        enforced_relation: NoFieldGKRRelation::MaxQuadratic {
            input: relation,
            expression,
            output: addr_out,
        },
    }]);

    let dag = dag_layer(
        vec![rd(pa.clone()), rd(pb.clone())],
        vec![
            Expr::Source(SourceId(0)),
            Expr::Source(SourceId(1)),
            Expr::Mul(vec![ExprId(0), ExprId(1)]),
        ],
        vec![out_root(2, 0, 0, FieldKind::Base, 0)],
    );

    Family {
        name: "base_product",
        layer,
        dag,
        cross: HashMap::new(),
        base_inputs: vec![(addr_a, pa, a), (addr_b, pb, b)],
        ext_inputs: vec![],
        base_outputs: vec![(addr_out, out)],
        ext_outputs: vec![],
        slot_claim_addrs: vec![Some(addr_out)],
    }
}

/// Mixed base×ext: `MaskIntoIdentityProduct`, `out = (input − 1)·mask + 1`
/// with a base-field mask and an extension-field input.
fn family_mixed_mask_identity() -> Family {
    let addr_mask = GKRAddress::BaseLayerWitness(0);
    let addr_in = GKRAddress::InnerLayer {
        layer: 0,
        offset: 0,
    };
    let addr_out = GKRAddress::InnerLayer {
        layer: 1,
        offset: 0,
    };
    let p_mask = ReadPlace::BaseLayerWitness { column: 0 };
    let p_in = ReadPlace::LayerOutput {
        layer: 0,
        offset: 0,
    };

    let mask = base_col(0xC0, POLY_SIZE);
    let input = ext_col(0xC1, POLY_SIZE);
    let out: Vec<Ext> = input
        .iter()
        .zip(&mask)
        .map(|(a, m)| add(mul(sub(*a, &Ext::ONE), &lift(*m)), &Ext::ONE))
        .collect();

    let layer = micro_layer(vec![GateArtifacts {
        output_layer: 1,
        enforced_relation: NoFieldGKRRelation::MaskIntoIdentityProduct {
            input: addr_in,
            mask: addr_mask,
            output: addr_out,
        },
    }]);

    let m1 = minus_one_u32();
    let dag = dag_layer(
        vec![
            rd(p_mask.clone()),
            rd(p_in.clone()),
            SourceKind::Constant { value: m1 },
            SourceKind::Constant { value: 1 },
        ],
        vec![
            Expr::Source(SourceId(0)),             // 0 = mask
            Expr::Source(SourceId(1)),             // 1 = input
            Expr::Source(SourceId(2)),             // 2 = -1
            Expr::Source(SourceId(3)),             // 3 = 1
            Expr::Add(vec![ExprId(1), ExprId(2)]), // 4 = input - 1
            Expr::Mul(vec![ExprId(4), ExprId(0)]), // 5 = (input - 1)·mask
            Expr::Add(vec![ExprId(5), ExprId(3)]), // 6 = (input - 1)·mask + 1
        ],
        vec![out_root(6, 0, 0, FieldKind::Ext, 0)],
    );

    let cross = HashMap::from_iter([(p_in.clone(), FieldKind::Ext)]);

    Family {
        name: "mixed_mask_identity",
        layer,
        dag,
        cross,
        base_inputs: vec![(addr_mask, p_mask, mask)],
        ext_inputs: vec![(addr_in, p_in, input)],
        base_outputs: vec![],
        ext_outputs: vec![(addr_out, out)],
        slot_claim_addrs: vec![Some(addr_out)],
    }
}

/// Claim-only MaxQuadratic constraint (`t² − t == 0`, boolean `t`) BETWEEN two
/// nonzero-output product gates — the alpha-slot pin: weights must come out as
/// `[1, beta, beta²]` with the constraint consuming the beta slot.
fn family_constraint_between_gates() -> Family {
    let addr_a0 = GKRAddress::InnerLayer {
        layer: 0,
        offset: 0,
    };
    let addr_b0 = GKRAddress::InnerLayer {
        layer: 0,
        offset: 1,
    };
    let addr_a1 = GKRAddress::InnerLayer {
        layer: 0,
        offset: 2,
    };
    let addr_b1 = GKRAddress::InnerLayer {
        layer: 0,
        offset: 3,
    };
    let addr_t = GKRAddress::BaseLayerWitness(0);
    let addr_out0 = GKRAddress::InnerLayer {
        layer: 1,
        offset: 0,
    };
    let addr_out1 = GKRAddress::InnerLayer {
        layer: 1,
        offset: 1,
    };
    let places: Vec<ReadPlace> = (0..4)
        .map(|offset| ReadPlace::LayerOutput { layer: 0, offset })
        .collect();
    let p_t = ReadPlace::BaseLayerWitness { column: 0 };

    let a0 = ext_col(0xD0, POLY_SIZE);
    let b0 = ext_col(0xD1, POLY_SIZE);
    let a1 = ext_col(0xD2, POLY_SIZE);
    let b1 = ext_col(0xD3, POLY_SIZE);
    let t = bool_col(0xD4, POLY_SIZE);
    let out0: Vec<Ext> = a0.iter().zip(&b0).map(|(x, y)| mul(*x, y)).collect();
    let out1: Vec<Ext> = a1.iter().zip(&b1).map(|(x, y)| mul(*x, y)).collect();

    let m1 = minus_one_u32();
    let constraint = NoFieldMaxQuadraticGKRRelation {
        quadratic_terms: vec![(addr_t, vec![(1u32, addr_t)].into_boxed_slice())]
            .into_boxed_slice(),
        linear_terms: vec![(m1, addr_t)].into_boxed_slice(),
        constant: 0,
    };
    let expression = NoFieldStructuredExpression::Sum(vec![
        NoFieldStructuredExpression::Product(vec![
            NoFieldStructuredExpression::Place(addr_t),
            NoFieldStructuredExpression::Place(addr_t),
        ]),
        NoFieldStructuredExpression::Product(vec![
            NoFieldStructuredExpression::Constant(m1),
            NoFieldStructuredExpression::Place(addr_t),
        ]),
    ]);

    let layer = micro_layer(vec![
        GateArtifacts {
            output_layer: 1,
            enforced_relation: NoFieldGKRRelation::TrivialProduct {
                input: [addr_a0, addr_b0],
                output: addr_out0,
            },
        },
        GateArtifacts {
            output_layer: 1,
            enforced_relation: NoFieldGKRRelation::EnforceSingleMaxQuadraticConstraint {
                input: constraint,
                expression,
            },
        },
        GateArtifacts {
            output_layer: 1,
            enforced_relation: NoFieldGKRRelation::TrivialProduct {
                input: [addr_a1, addr_b1],
                output: addr_out1,
            },
        },
    ]);

    let dag = dag_layer(
        vec![
            rd(places[0].clone()),
            rd(places[1].clone()),
            rd(places[2].clone()),
            rd(places[3].clone()),
            rd(p_t.clone()),
            SourceKind::Constant { value: m1 },
        ],
        vec![
            Expr::Source(SourceId(0)),             // 0 = a0
            Expr::Source(SourceId(1)),             // 1 = b0
            Expr::Source(SourceId(2)),             // 2 = a1
            Expr::Source(SourceId(3)),             // 3 = b1
            Expr::Source(SourceId(4)),             // 4 = t
            Expr::Source(SourceId(5)),             // 5 = -1
            Expr::Mul(vec![ExprId(0), ExprId(1)]), // 6 = a0·b0
            Expr::Mul(vec![ExprId(4), ExprId(4)]), // 7 = t²
            Expr::Mul(vec![ExprId(5), ExprId(4)]), // 8 = -t
            Expr::Add(vec![ExprId(7), ExprId(8)]), // 9 = t² - t
            Expr::Mul(vec![ExprId(2), ExprId(3)]), // 10 = a1·b1
        ],
        vec![
            out_root(6, 0, 0, FieldKind::Ext, 0),
            constraint_root(9, 1),
            out_root(10, 2, 1, FieldKind::Ext, 0),
        ],
    );

    let cross = HashMap::from_iter(places.iter().map(|p| (p.clone(), FieldKind::Ext)));

    Family {
        name: "constraint_between_gates",
        layer,
        dag,
        cross,
        base_inputs: vec![(addr_t, p_t, t)],
        ext_inputs: vec![
            (addr_a0, places[0].clone(), a0),
            (addr_b0, places[1].clone(), b0),
            (addr_a1, places[2].clone(), a1),
            (addr_b1, places[3].clone(), b1),
        ],
        base_outputs: vec![],
        ext_outputs: vec![(addr_out0, out0), (addr_out1, out1)],
        slot_claim_addrs: vec![Some(addr_out0), None, Some(addr_out1)],
    }
}

/// Two-output lookup pair over base inputs:
/// `num = (b+γ) + (d+γ)`, `den = (b+γ)·(d+γ)` — one kernel, TWO beta slots.
fn family_lookup_base_pair() -> Family {
    let addr_b = GKRAddress::BaseLayerWitness(0);
    let addr_d = GKRAddress::BaseLayerWitness(1);
    let addr_num = GKRAddress::InnerLayer {
        layer: 1,
        offset: 0,
    };
    let addr_den = GKRAddress::InnerLayer {
        layer: 1,
        offset: 1,
    };
    let pb = ReadPlace::BaseLayerWitness { column: 0 };
    let pd = ReadPlace::BaseLayerWitness { column: 1 };

    let b = base_col(0xE0, POLY_SIZE);
    let d = base_col(0xE1, POLY_SIZE);
    let g = gamma();
    let num: Vec<Ext> = b
        .iter()
        .zip(&d)
        .map(|(x, y)| add(add(lift(*x), &g), &add(lift(*y), &g)))
        .collect();
    let den: Vec<Ext> = b
        .iter()
        .zip(&d)
        .map(|(x, y)| mul(add(lift(*x), &g), &add(lift(*y), &g)))
        .collect();

    let layer = micro_layer(vec![GateArtifacts {
        output_layer: 1,
        enforced_relation: NoFieldGKRRelation::LookupPairFromMaterializedBaseInputs {
            input: [addr_b, addr_d],
            output: [addr_num, addr_den],
        },
    }]);

    let dag = dag_layer(
        vec![
            rd(pb.clone()),
            rd(pd.clone()),
            SourceKind::Challenge {
                reference: ChallengeRef {
                    key: ChallengeKey::LookupAdditive,
                    power: ChallengePower::One,
                },
            },
        ],
        vec![
            Expr::Source(SourceId(0)),             // 0 = b
            Expr::Source(SourceId(1)),             // 1 = d
            Expr::Source(SourceId(2)),             // 2 = γ
            Expr::Add(vec![ExprId(0), ExprId(2)]), // 3 = b + γ
            Expr::Add(vec![ExprId(1), ExprId(2)]), // 4 = d + γ
            Expr::Add(vec![ExprId(3), ExprId(4)]), // 5 = num
            Expr::Mul(vec![ExprId(3), ExprId(4)]), // 6 = den
        ],
        vec![
            out_root(5, 0, 0, FieldKind::Ext, 0),
            out_root(6, 0, 1, FieldKind::Ext, 1),
        ],
    );

    Family {
        name: "lookup_base_pair",
        layer,
        dag,
        cross: HashMap::new(),
        base_inputs: vec![(addr_b, pb, b), (addr_d, pd, d)],
        ext_inputs: vec![],
        base_outputs: vec![],
        ext_outputs: vec![(addr_num, num), (addr_den, den)],
        slot_claim_addrs: vec![Some(addr_num), Some(addr_den)],
    }
}

// ── Instrument-side resolvers ────────────────────────────────────────────────

fn rev_bits(x: usize, n: usize) -> usize {
    let mut r = 0usize;
    for i in 0..n {
        r |= ((x >> i) & 1) << (n - 1 - i);
    }
    r
}

/// The instrument's ORIGINALS: the bit-reversed view `O(j) = P(rev_k(j))` of
/// every production column (see the module docs for why this is the mapping).
struct Cols {
    k: usize,
    cols: HashMap<ReadPlace, Vec<Ext>>,
}

impl Cols {
    fn new(fam: &Family, k: usize) -> Self {
        let mut cols = HashMap::new();
        for (_, place, vals) in &fam.base_inputs {
            cols.insert(place.clone(), vals.iter().map(|v| lift(*v)).collect());
        }
        for (_, place, vals) in &fam.ext_inputs {
            cols.insert(place.clone(), vals.clone());
        }
        Self { k, cols }
    }
}

impl ReadResolver for Cols {
    fn read(&self, place: &ReadPlace, row: usize) -> Ext {
        let col = self
            .cols
            .get(place)
            .unwrap_or_else(|| panic!("unknown read place {place:?}"));
        col[rev_bits(row, self.k)]
    }
}

/// Materialized previous-round buffer: IS the depth-`round` fold of the same
/// originals via the shared `sumcheck_fold_point` recurrence.
struct BufferAt<'a> {
    cols: &'a Cols,
    round: u8,
    ch: &'a [Ext],
}

impl ReadResolver for BufferAt<'_> {
    fn read(&self, place: &ReadPlace, y: usize) -> Ext {
        sumcheck_fold_point(&|z| self.cols.read(place, z), y, self.round, self.ch)
            .expect("buffer fold within challenge depth")
    }
}

struct NoLookup;
impl LookupResolver for NoLookup {
    fn lookup(&self, kind: &LookupValueKind, _: usize, _: Ext, _: usize) -> Bf {
        // Distilled backward programs erase LookupValue sources (rewritten to
        // their query cones), so no leg of this gate may ever resolve one.
        panic!("bwd programs have no LookupValue sources ({kind:?})")
    }
}

struct NoVs;
impl VirtualSetupResolver for NoVs {
    fn virtual_setup(&self, kind: &VirtualSetupKind, _: usize) -> Bf {
        panic!("micro families have no VirtualSetup sources ({kind:?})")
    }
}

struct MicroChallenges {
    beta: Ext,
    gamma: Ext,
    mult: Ext,
}

impl ChallengeResolver for MicroChallenges {
    fn challenge(&self, r: &ChallengeRef) -> Ext {
        match &r.key {
            ChallengeKey::ClaimBatching => match r.power {
                ChallengePower::One => self.beta,
                ChallengePower::Static(i) => pow(self.beta, i),
            },
            ChallengeKey::LookupAdditive => self.gamma,
            ChallengeKey::LookupMultiplicative => self.mult,
            other => panic!("unexpected challenge key {other:?}"),
        }
    }
}

// ── Instrument programs (compiled once per family, round/policy-invariant) ──

fn compile_prog(d: &DistilledLayer) -> BwdCompiledLayer {
    match compile_distilled(d, BUDGET, None) {
        Ok(c) => c,
        Err(CompileError::BudgetBelowFloor { floor, .. }) => {
            compile_distilled(d, floor, None).expect("compile at reported floor")
        }
        Err(e) => panic!("compile_distilled: {e:?}"),
    }
}

// ── The instrument loop (one policy leg) ─────────────────────────────────────

struct InstrumentCtx<'a> {
    fam: &'a Family,
    run: &'a LayerOracleRun<Ext>,
    prev: &'a [Ext],
    eq_layers: &'a [Box<[Ext]>],
    cols: &'a Cols,
    chal: &'a MicroChallenges,
    d_r0: &'a DistilledLayer,
    c_r0: &'a BwdCompiledLayer,
    d_ext: &'a DistilledLayer,
    c_ext: &'a BwdCompiledLayer,
}

/// Drives the backward-VM instrument through all rounds under `policy`,
/// asserting (a)-(e) against the captured oracle run. Returns the per-round
/// `[q0, q2]` trace (for the cross-policy identity check).
fn run_instrument(cx: &InstrumentCtx<'_>, policy: MaterializationPolicy) -> Vec<[Ext; 2]> {
    let k = FOLDING_STEPS;
    let run = cx.run;
    let ctx = format!("[{} / {policy:?}]", cx.fam.name);

    static NO_LOOKUP: NoLookup = NoLookup;
    static NO_VS: NoVs = NoVs;

    let mut inst_seed = Seed::default();
    let mut claim = run.initial_combined_claim;
    let mut eq_prefactor = Ext::ONE;
    let mut drawn: Vec<Ext> = Vec::new();
    let mut q_trace: Vec<[Ext; 2]> = Vec::new();

    for r in 0..k {
        // (d) chain: round-entry claim and eq prefactor match the capture.
        assert_eq!(claim, run.per_round_claims[r], "{ctx} claim chain, round {r}");
        assert_eq!(
            eq_prefactor, run.per_round_eq_prefactor[r],
            "{ctx} eq-prefactor chain, round {r}"
        );

        // Round 0 evaluates the R0-regime program over unfolded originals;
        // rounds >= 1 the Ext-regime program with per-policy fold bindings.
        let (c, d) = if r == 0 {
            (cx.c_r0, cx.d_r0)
        } else {
            (cx.c_ext, cx.d_ext)
        };
        let bindings = bind(d, policy, r as u8);
        let materialized = bindings
            .states
            .iter()
            .any(|s| matches!(s, FoldState::Materialized));
        let buf = BufferAt {
            cols: cx.cols,
            round: r as u8,
            ch: &drawn,
        };
        let plain_r = Resolvers {
            read: cx.cols,
            lookup: &NO_LOOKUP,
            virtual_setup: &NO_VS,
            challenge: cx.chal,
        };
        let buf_r = Resolvers {
            read: &buf,
            lookup: &NO_LOOKUP,
            virtual_setup: &NO_VS,
            challenge: cx.chal,
        };
        let rr = if materialized { &buf_r } else { &plain_r };

        let acc_size = 1usize << (k - r - 1);
        let eq = &cx.eq_layers[k - r - 1];
        assert_eq!(eq.len(), acc_size);

        // q0 = Σ_y eq[rev(y)]·v_T0(y), q2 = Σ_y eq[rev(y)]·v_T2(y): the
        // instrument row `y` maps to the production accumulator index by
        // bit reversal over the surviving width (module docs).
        let mut q0 = Ext::ZERO;
        let mut q2 = Ext::ZERO;
        for y in 0..acc_size {
            let w = eq[rev_bits(y, k - r - 1)];
            let v0 = interpret_bwd_row(c, d, &bindings, rr, Role::T0, y, &drawn)
                .unwrap_or_else(|e| panic!("{ctx} interp T0 round {r} row {y}: {e:?}"));
            let v2 = interpret_bwd_row(c, d, &bindings, rr, Role::T2, y, &drawn)
                .unwrap_or_else(|e| panic!("{ctx} interp T2 round {r} row {y}: {e:?}"));
            q0.add_assign(&mul(w, &v0));
            q2.add_assign(&mul(w, &v2));
        }
        q_trace.push([q0, q2]);

        // Derive d_oracle from (z, C, c0, c2) via the production identity
        // FIRST — never from the candidate q's.
        let [c0, c2] = run.per_round_reduced[r];
        let z = cx.prev[r];
        let big_c = mul(claim, &inv(&eq_prefactor));
        let b1 = sub(Ext::ONE, &z);
        // q1 = (C - b·c0)/z (sum-constraint-pinned), d = q1 - c2 - c0.
        let q1 = mul(sub(big_c, &mul(b1, &c0)), &inv(&z));
        let d_oracle = sub(sub(q1, &c2), &c0);
        // g(2) = c0 + 2d + 4c2.
        let mut g2_oracle = c2;
        g2_oracle.double();
        g2_oracle.double();
        let mut two_d = d_oracle;
        two_d.double();
        g2_oracle.add_assign(&two_d);
        g2_oracle.add_assign(&c0);

        // (a) the reduced evaluations match the oracle coefficients.
        assert_eq!(q0, c0, "{ctx} (a) q0 != c0 at round {r}");
        assert_eq!(q2, g2_oracle, "{ctx} (a) q2 != g(2) at round {r}");

        // (b) recovered monomials: e = g(0), c from the interpolation identity.
        let e_rec = q0;
        let q1_from_q = mul(sub(big_c, &mul(b1, &q0)), &inv(&z));
        let mut two_q1 = q1_from_q;
        two_q1.double();
        let mut c_rec = sub(add(q2, &q0), &two_q1);
        let two = add(Ext::ONE, &Ext::ONE);
        c_rec.mul_assign(&inv(&two));
        assert_eq!(e_rec, c0, "{ctx} (b) recovered e != c0 at round {r}");
        assert_eq!(c_rec, c2, "{ctx} (b) recovered c != c2 at round {r}");

        // (c) emission reproduces the committed [E; 4] and (b) d == d_oracle.
        let (coeffs, d_rec) = recover_and_emit::<Bf, Ext>(z, claim, eq_prefactor, q0, q2);
        assert_eq!(d_rec, d_oracle, "{ctx} (b) recovered d at round {r}");
        assert_eq!(
            coeffs, run.round_coeffs[r],
            "{ctx} (c) committed univariate at round {r}"
        );

        // (d) transcript replay: commit + draw reproduce the oracle challenge,
        // then advance claim and eq prefactor exactly as production does.
        commit_field_els::<Bf, Ext>(&mut inst_seed, &coeffs);
        let ch = draw_random_field_els::<Bf, Ext>(&mut inst_seed, 1)[0];
        assert_eq!(
            ch, run.folding_challenges[r],
            "{ctx} (d) folding challenge at round {r}"
        );
        claim = evaluate_small_univariate_poly::<Bf, Ext, 4>(&coeffs, &ch);
        eq_prefactor = evaluate_eq_poly::<Bf, Ext>(&ch, &cx.prev[r]);
        drawn.push(ch);
    }

    // Chain closes on the loop's normalized final claim.
    let final_norm = mul(claim, &inv(&eq_prefactor));
    assert_eq!(
        final_norm, run.final_normalized_claim,
        "{ctx} final normalized claim"
    );

    // (e) final folded source evaluations: full-depth instrument fold of every
    // input column == the production last-evaluations line at r_last.
    assert_eq!(drawn.len(), k);
    let r_last = drawn[k - 1];
    let mut expected_addrs: Vec<(GKRAddress, ReadPlace)> = Vec::new();
    for (addr, place, _) in &cx.fam.base_inputs {
        expected_addrs.push((*addr, place.clone()));
    }
    for (addr, place, _) in &cx.fam.ext_inputs {
        expected_addrs.push((*addr, place.clone()));
    }
    assert_eq!(
        run.last_evaluations.len(),
        expected_addrs.len(),
        "{ctx} last_evaluations covers exactly the input columns"
    );
    for (addr, place) in &expected_addrs {
        let [f0, f1] = run.last_evaluations[addr];
        let expected = interpolate(f0, f1, &r_last);
        let full = sumcheck_fold_point(&|z| cx.cols.read(place, z), 0, k as u8, &drawn)
            .expect("full-depth fold");
        assert_eq!(full, expected, "{ctx} (e) final fold for {addr:?}");
    }

    q_trace
}

// ── The matrix driver ────────────────────────────────────────────────────────

fn check_family(fam: Family) {
    let worker = Worker::new_with_num_threads(1);
    let k = FOLDING_STEPS;
    let prev = prev_challenges();
    let beta = beta();
    let gamma = gamma();
    let mult = lookup_mult();

    // Output claims at the previous layer's point.
    let eq_full = make_eq_poly_in_full::<Ext>(&prev, &worker);
    let eq_last = &eq_full.last().unwrap()[..];
    let mut output_claims: BTreeMap<GKRAddress, Ext> = BTreeMap::new();
    for (addr, vals) in &fam.ext_outputs {
        output_claims.insert(*addr, evaluate_with_precomputed_eq_ext::<Ext>(vals, eq_last));
    }
    for (addr, vals) in &fam.base_outputs {
        output_claims.insert(
            *addr,
            evaluate_with_precomputed_eq::<Bf, Ext>(vals, eq_last),
        );
    }

    // Production oracle run (the transcript authority).
    let mut storage = build_storage(&fam);
    let mut seed = Seed::default();
    let run = run_layer_oracle::<Bf, Ext>(
        0,
        &fam.layer,
        &output_claims,
        &prev,
        &mut storage,
        beta,
        1 << k,
        mult,
        gamma,
        &[],
        0,
        &GKRExternalChallenges::default(),
        &mut seed,
        &worker,
    );

    // Alpha-slot pin: batch weights are consecutive beta powers in gate order,
    // claim-only constraint slots consume a power but contribute zero claim.
    assert_eq!(
        run.per_relation_weights.len(),
        fam.slot_claim_addrs.len(),
        "[{}] batching slot count",
        fam.name
    );
    let mut expected_claim = Ext::ZERO;
    for (i, slot) in fam.slot_claim_addrs.iter().enumerate() {
        assert_eq!(
            run.per_relation_weights[i],
            pow(beta, i as u32),
            "[{}] slot {i} weight must be beta^{i}",
            fam.name
        );
        if let Some(addr) = slot {
            expected_claim.add_assign(&mul(pow(beta, i as u32), &output_claims[addr]));
        }
    }
    assert_eq!(
        run.initial_combined_claim, expected_claim,
        "[{}] combined claim over weighted slots",
        fam.name
    );
    assert_eq!(run.per_round_claims[0], run.initial_combined_claim);

    // Instrument programs: R0 regime for round 0, Ext regime for rounds >= 1.
    let d_r0 = distill(&fam.dag, BwdRegime::R0, &fam.cross, None);
    assert!(!d_r0.skipped_decoder, "[{}] R0 distill", fam.name);
    let c_r0 = compile_prog(&d_r0);
    let d_ext = distill(&fam.dag, BwdRegime::Ext, &fam.cross, None);
    assert!(!d_ext.skipped_decoder, "[{}] Ext distill", fam.name);
    let c_ext = compile_prog(&d_ext);

    let cols = Cols::new(&fam, k);
    let chal = MicroChallenges { beta, gamma, mult };
    let cx = InstrumentCtx {
        fam: &fam,
        run: &run,
        prev: &prev,
        eq_layers: &eq_full,
        cols: &cols,
        chal: &chal,
        d_r0: &d_r0,
        c_r0: &c_r0,
        d_ext: &d_ext,
        c_ext: &c_ext,
    };

    // All policy legs assert against the SAME oracle; also pin them to each
    // other explicitly.
    let mut first_trace: Option<Vec<[Ext; 2]>> = None;
    for policy in POLICIES {
        let trace = run_instrument(&cx, policy);
        match &first_trace {
            None => first_trace = Some(trace),
            Some(f) => assert_eq!(
                &trace, f,
                "[{}] policy {policy:?} q-trace diverged from first policy",
                fam.name
            ),
        }
    }
}

// ── The matrix ───────────────────────────────────────────────────────────────

#[test]
fn protocol_parity_ext_product() {
    check_family(family_ext_product());
}

#[test]
fn protocol_parity_base_product() {
    check_family(family_base_product());
}

#[test]
fn protocol_parity_mixed_mask_identity() {
    check_family(family_mixed_mask_identity());
}

#[test]
fn protocol_parity_constraint_between_gates() {
    check_family(family_constraint_between_gates());
}

#[test]
fn protocol_parity_lookup_base_pair() {
    check_family(family_lookup_base_pair());
}

// ═════════════════════════════════════════════════════════════════════════════
// Task 11: G2 fixture layer — bigint L0 over a REAL witness
// ═════════════════════════════════════════════════════════════════════════════
//
// Same protocol gate as the micro matrix above, at fixture scale: the FULL
// bigint layer-0 relation set (216 gates — products, lookup pairs incl.
// vector/base/with-setup, copies, and 115 enforced constraints — over 140
// cache relations: MemoryTuple, SingleColumnLookup, VectorizedLookup(+Setup)).
//
// # Why a REAL witness (synthetic storage is structurally impossible here)
//
// 1. The production loop enforces global consistency (`run_sumcheck_loop`
//    recomputes the final claim from the gate kernels and asserts) — storage
//    must make every round polynomial reduce to the combined claim.
// 2. The 115 constraints are real bigint carry/product relations; the only
//    synthetic assignment vanishing all of them is all-zero (row-constant).
// 3. The backward distill INLINES same-layer caches and rewrites LookupValue
//    leaves to their query cones; production kernels read the PEEKED cache
//    columns. `peek == query` is exactly the lookup-argument witness
//    invariant — it holds only for a valid witness.
//
// The witness comes from replaying `examples/bigint_with_control` (one real
// bigint delegation call) through the production witness generator, then the
// production forward loop materializes every cache/output — ONE source of
// column truth for both the oracle and the instrument (Task-10 discipline).
//
// # Trace size
//
// Target was 2^8; the generator's minimum is larger: bigint's concatenated
// generic-lookup table is 1,390,592 rows and the `VectorizedLookupSetup`
// cache materializes it into a trace-length column, so the smallest legal
// trace is 2^21 (the artifact's committed 2^22 halved). The artifact's
// `trace_len` is overridden accordingly; nothing else in the layout depends
// on it (bigint has no inits/teardowns top-bits).
//
// # VS-ABI FINDING (real signal, documented, not fudged around)
//
// A Materialized VS read would route through `VirtualSetupResolver::
// virtual_setup -> Bf`, but a depth-r folded buffer under REAL Ext challenges
// is a genuine Ext value that ABI cannot represent (the corpus value gate only
// passed because its synthetic challenges stayed in the base subfield, noted
// there as a harness property). `bind()` therefore enforces the VS forced-lazy
// convention directly: VS-origin FoldSources always bind `LazyFromOriginals
// { depth: round }` regardless of policy (value-identical by fold-recomputation
// semantics, cheap — 2 VS leaves, O(k * 2^(k-1)) extra reads across the run).
// This test calls `bind()` unmodified; until the resolver ABI grows an
// Ext-typed VS buffer read, no Materialized VS binding can arise.
//
// # Policy legs + runtime
//
// Both dispatched policies run: `AlwaysMaterialize` fully; `LazyUpTo(2)`
// re-evaluates rounds 1..=2 (where its bindings actually differ) and is
// pinned to leg A by a binding-equality assertion for every later round
// (equal `FoldState` vectors + a deterministic interpreter ⇒ equal values).
// Row sums are parallelized over threads; materialized rounds read
// progressively folded per-column buffers (exact instrument recurrence),
// never a per-read recursive fold.

const BIGINT_LAYOUT_PATH: &str =
    "../cs/compiled_circuits/bigint_with_extended_control_layout_gkr.json";
const BIGINT_TRACE_LOG2: usize = 21;

// ── Real-witness construction ────────────────────────────────────────────────

/// Replay `examples/bigint_with_control` and evaluate the production witness
/// for the bigint delegation circuit at the 2^21 minimum trace.
fn bigint_real_witness(
    worker: &Worker,
) -> (
    GKRCircuitArtifact<Bf>,
    GKRFullWitnessTrace<Bf, Global, Global>,
    TableDriver<Bf>,
) {
    let mut artifact: GKRCircuitArtifact<Bf> =
        crate::tests::gkr::deserialize_from_file(BIGINT_LAYOUT_PATH);
    let trace_len = 1usize << BIGINT_TRACE_LOG2;
    assert!(
        artifact.total_tables_size <= trace_len,
        "generic tables ({}) must fit the trace ({trace_len})",
        artifact.total_tables_size
    );
    assert!(
        artifact.memory_layout.teardown_sets.is_empty(),
        "bigint is a delegation circuit: no inits/teardowns top bits"
    );
    artifact.trace_len = trace_len;

    let config = ProgramConfig {
        binary_path: "../examples/bigint_with_control/app.bin".to_string(),
        text_section_path: "../examples/bigint_with_control/app.text".to_string(),
        // the program takes no non-determinism input; unused padding
        non_determinism_reads: vec![15, 1],
        cycles_bound: 1 << 20,
        ram_bound_bytes: 1 << 30,
    };
    let vm = run_vm_and_capture::<DelegationsAndFamiliesCounters, FullUnsignedMachineDecoderConfig>(
        &config, worker,
    );
    let num_calls = vm.counters.bigint_calls;
    assert!(
        num_calls > 0,
        "examples/bigint_with_control must issue at least one bigint delegation call"
    );
    let expected_final_state = vm.expected_final_state();

    let mut state = vm.snapshotter.initial_snapshot.state;
    let mut ram_log_buffers = vm
        .snapshotter
        .reads_buffer
        .make_range(0..vm.snapshotter.reads_buffer.len());
    let mut ram = ReplayerRam::<{ common_constants::ROM_SECOND_WORD_BITS }> {
        ram_log: &mut ram_log_buffers,
    };
    let mut buffer = vec![DelegationWitness::empty(); num_calls];
    let mut buffers = vec![&mut buffer[..]];
    let mut tracer = BigintDelegationDestinationHolder {
        buffers: &mut buffers[..],
    };
    ReplayerVM::<DelegationsAndFamiliesCounters>::replay_basic_unrolled::<_, _, Bf>(
        &mut state,
        &mut ram,
        &vm.tape,
        &mut (),
        vm.cycles_bound,
        &mut tracer,
    );
    assert_eq!(expected_final_state, state, "replay must reproduce the run");

    let mut table_driver = TableDriver::<Bf>::new();
    cs::gkr_circuits::delegation::bigint_with_control::bigint_with_extended_control_delegation_circuit_table_driver_fn(
        &mut table_driver,
    );

    let oracle = BigintDelegationOracle {
        cycle_data: &buffer,
        marker: core::marker::PhantomData,
    };
    let full_trace = evaluate_gkr_witness_for_delegation_circuit(
        &artifact,
        crate::tests::gkr::bigint_with_extended_control::witness_eval_fn,
        trace_len,
        &oracle,
        &table_driver,
        worker,
        Global,
        Global,
    );
    (artifact, full_trace, table_driver)
}

/// Mirror `prove_configured_with_gkr`'s pre-sumcheck storage assembly: setup
/// columns + preprocessed generic lookups, the virtual range-check setup
/// polys, then the production forward loop over every layer (materializing
/// all caches and layer outputs).
fn build_bigint_storage(
    artifact: &GKRCircuitArtifact<Bf>,
    full_trace: GKRFullWitnessTrace<Bf, Global, Global>,
    table_driver: &TableDriver<Bf>,
    lookup_alpha: Ext,
    lookup_gamma: Ext,
    external: &GKRExternalChallenges<Bf, Ext>,
    worker: &Worker,
) -> GKRStorage<Bf, Ext> {
    let trace_len = artifact.trace_len;
    let setup = GKRSetup::construct(table_driver, &[], trace_len, artifact);
    let mut storage = GKRStorage::<Bf, Ext>::default();
    let (preprocessed_generic_lookup, decoder_lookup_fill_value) = setup
        .preprocess_generic_lookups(artifact, lookup_alpha, trace_len, &mut storage, worker);
    storage.insert_base_field_at_layer(
        0,
        GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheck16Bits),
        BaseFieldPoly::new(materialize_virtual_range_check_setup_poly::<Bf, Global, 16>(
            trace_len.trailing_zeros(),
        )),
    );
    storage.insert_base_field_at_layer(
        0,
        GKRAddress::VirtualSetup(VirtualSetupPoly::RangeCheckTimestamp),
        BaseFieldPoly::new(materialize_virtual_range_check_setup_poly::<
            Bf,
            Global,
            { common_constants::TIMESTAMP_COLUMNS_NUM_BITS },
        >(trace_len.trailing_zeros())),
    );

    let mut witness_eval_data = full_trace;
    for (layer_idx, layer) in artifact.layers.iter().enumerate() {
        forward_loop::evaluate_layer(
            layer_idx,
            layer,
            &mut storage,
            artifact,
            external,
            &mut witness_eval_data,
            &[],
            trace_len,
            &preprocessed_generic_lookup,
            lookup_alpha,
            lookup_gamma,
            decoder_lookup_fill_value,
            worker,
        );
    }
    storage
}

// ── Instrument-side resolvers over the REAL columns ──────────────────────────

/// The production challenge values, resolved by `ChallengeRef` for the
/// instrument. Powers are precomputed (a `ClaimBatching` leaf exists per
/// spine slot and is resolved per row-eval).
struct FixtureChallenges {
    beta_pows: Vec<Ext>,
    alpha_pows: Vec<Ext>,
    gamma: Ext,
    external: GKRExternalChallenges<Bf, Ext>,
}

impl FixtureChallenges {
    fn new(beta: Ext, alpha: Ext, gamma: Ext, external: &GKRExternalChallenges<Bf, Ext>, max_beta_pow: usize) -> Self {
        let powers = |base: Ext, n: usize| -> Vec<Ext> {
            let mut v = Vec::with_capacity(n + 1);
            let mut acc = Ext::ONE;
            for _ in 0..=n {
                v.push(acc);
                acc.mul_assign(&base);
            }
            v
        };
        Self {
            beta_pows: powers(beta, max_beta_pow),
            alpha_pows: powers(alpha, 64),
            gamma,
            external: *external,
        }
    }

    fn perm_lin(&self, slot: &PermutationSlot) -> Ext {
        let idx = match slot {
            PermutationSlot::AddressLow => PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
            PermutationSlot::AddressHigh => PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
            PermutationSlot::TimestampLow => {
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX
            }
            PermutationSlot::TimestampHigh => {
                PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX
            }
            PermutationSlot::ValueLow => PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
            PermutationSlot::ValueHigh => PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
        };
        self.external.permutation_argument_linearization_challenges[idx]
    }

    fn resolve(&self, r: &ChallengeRef) -> Ext {
        match &r.key {
            ChallengeKey::ClaimBatching => match r.power {
                ChallengePower::One => self.beta_pows[1],
                ChallengePower::Static(i) => self.beta_pows[i as usize],
            },
            ChallengeKey::LookupAdditive => self.gamma,
            ChallengeKey::LookupMultiplicative => match r.power {
                ChallengePower::One => self.alpha_pows[1],
                ChallengePower::Static(j) => self.alpha_pows[j as usize],
            },
            ChallengeKey::PermutationAdditive => self.external.permutation_argument_additive_part,
            ChallengeKey::PermutationLinearization(slot) => self.perm_lin(slot),
            other => panic!("bigint L0 must not reference challenge key {other:?}"),
        }
    }
}

/// The instrument's ORIGINALS at fixture scale: the bit-reversed view
/// `O(j) = P(rev_k(j))` of the REAL production columns (Arc'd, zero-copy from
/// the pre-oracle storage snapshot), plus the two virtual-setup polys and the
/// production challenge values. One struct serves all four resolver roles.
struct FixtureCols {
    k: usize,
    base: HashMap<ReadPlace, Arc<Box<[Bf]>>>,
    vs: HashMap<VirtualSetupKind, Arc<Box<[Bf]>>>,
    chal: FixtureChallenges,
}

impl ReadResolver for FixtureCols {
    fn read(&self, place: &ReadPlace, row: usize) -> Ext {
        let col = self
            .base
            .get(place)
            .unwrap_or_else(|| panic!("unknown read place {place:?}"));
        lift(col[rev_bits(row, self.k)])
    }
}
impl VirtualSetupResolver for FixtureCols {
    fn virtual_setup(&self, kind: &VirtualSetupKind, row: usize) -> Bf {
        let col = self
            .vs
            .get(kind)
            .unwrap_or_else(|| panic!("unknown virtual setup {kind:?}"));
        col[rev_bits(row, self.k)]
    }
}
impl ChallengeResolver for FixtureCols {
    fn challenge(&self, r: &ChallengeRef) -> Ext {
        self.chal.resolve(r)
    }
}
impl LookupResolver for FixtureCols {
    fn lookup(&self, kind: &LookupValueKind, _: usize, _: Ext, _: usize) -> Bf {
        panic!("bwd programs have no LookupValue sources ({kind:?})")
    }
}

/// Materialized-round resolver: `read` serves the CURRENT depth-r folded
/// buffers (instrument index space); `virtual_setup` serves ORIGINALS,
/// because VS-origin FoldSources stay `LazyFromOriginals` (VS-ABI note in the
/// section docs) and the lazy fold recomputes from depth 0.
struct FoldedView<'a> {
    folded: &'a HashMap<ReadPlace, Vec<Ext>>,
    origs: &'a FixtureCols,
}

impl ReadResolver for FoldedView<'_> {
    fn read(&self, place: &ReadPlace, y: usize) -> Ext {
        let col = self
            .folded
            .get(place)
            .unwrap_or_else(|| panic!("no folded buffer for {place:?}"));
        col[y]
    }
}
impl VirtualSetupResolver for FoldedView<'_> {
    fn virtual_setup(&self, kind: &VirtualSetupKind, row: usize) -> Bf {
        self.origs.virtual_setup(kind, row)
    }
}
impl ChallengeResolver for FoldedView<'_> {
    fn challenge(&self, r: &ChallengeRef) -> Ext {
        self.origs.chal.resolve(r)
    }
}
impl LookupResolver for FoldedView<'_> {
    fn lookup(&self, kind: &LookupValueKind, _: usize, _: Ext, _: usize) -> Bf {
        panic!("bwd programs have no LookupValue sources ({kind:?})")
    }
}

// ── Parallel helpers ─────────────────────────────────────────────────────────

fn test_threads() -> usize {
    std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(8)
}

/// Map `f` over `items` with `threads` scoped workers, preserving order.
fn par_map<T: Sync, R: Send>(items: &[T], threads: usize, f: impl Fn(&T) -> R + Sync) -> Vec<R> {
    if items.is_empty() {
        return Vec::new();
    }
    let chunk = items.len().div_ceil(threads).max(1);
    std::thread::scope(|s| {
        let handles: Vec<_> = items
            .chunks(chunk)
            .map(|part| s.spawn(|| part.iter().map(&f).collect::<Vec<R>>()))
            .collect();
        handles
            .into_iter()
            .flat_map(|h| h.join().expect("par_map worker"))
            .collect()
    })
}

/// `[q0, q2] = [Σ_y eq[rev(y)]·v_T0(y), Σ_y eq[rev(y)]·v_T2(y)]` over the full
/// surviving row range, parallelized (field addition is associative-exact, so
/// chunked reduction is bit-identical to a serial sum).
#[allow(clippy::too_many_arguments)]
fn par_q_sums(
    threads: usize,
    acc_size: usize,
    eq_bits: usize,
    eq: &[Ext],
    c: &BwdCompiledLayer,
    d: &DistilledLayer,
    bindings: &BwdBindings,
    cols: &FixtureCols,
    folded: Option<&HashMap<ReadPlace, Vec<Ext>>>,
    drawn: &[Ext],
    ctx: &str,
) -> [Ext; 2] {
    let chunk = acc_size.div_ceil(threads).max(1);
    let partials: Vec<[Ext; 2]> = std::thread::scope(|s| {
        let handles: Vec<_> = (0..acc_size)
            .step_by(chunk)
            .map(|start| {
                let end = (start + chunk).min(acc_size);
                s.spawn(move || {
                    // Per-thread resolver views over the shared column data.
                    let folded_view = folded.map(|f| FoldedView { folded: f, origs: cols });
                    let rr = match &folded_view {
                        Some(v) => Resolvers {
                            read: v,
                            lookup: v,
                            virtual_setup: v,
                            challenge: v,
                        },
                        None => Resolvers {
                            read: cols,
                            lookup: cols,
                            virtual_setup: cols,
                            challenge: cols,
                        },
                    };
                    let mut q0 = Ext::ZERO;
                    let mut q2 = Ext::ZERO;
                    for y in start..end {
                        let w = eq[rev_bits(y, eq_bits)];
                        let v0 = interpret_bwd_row(c, d, bindings, &rr, Role::T0, y, drawn)
                            .unwrap_or_else(|e| panic!("{ctx} interp T0 row {y}: {e:?}"));
                        let v2 = interpret_bwd_row(c, d, bindings, &rr, Role::T2, y, drawn)
                            .unwrap_or_else(|e| panic!("{ctx} interp T2 row {y}: {e:?}"));
                        q0.add_assign(&mul(w, &v0));
                        q2.add_assign(&mul(w, &v2));
                    }
                    [q0, q2]
                })
            })
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().expect("par_q_sums worker"))
            .collect()
    });
    let mut q0 = Ext::ZERO;
    let mut q2 = Ext::ZERO;
    for [a, b] in partials {
        q0.add_assign(&a);
        q2.add_assign(&b);
    }
    [q0, q2]
}

/// One fold step of the instrument recurrence over a column:
/// `f_{d+1}(y) = f_d(2y) + ch·(f_d(2y+1) − f_d(2y))`.
fn fold_step(cur: &[Ext], ch: &Ext) -> Vec<Ext> {
    let half = cur.len() / 2;
    (0..half)
        .map(|y| {
            let a = cur[2 * y];
            let b = cur[2 * y + 1];
            add(mul(sub(b, &a), ch), &a)
        })
        .collect()
}

/// Full-depth fold of one ORIGINAL column (bit-reversed view) with `drawn`.
fn full_fold_col(read: &dyn Fn(usize) -> Ext, k: usize, drawn: &[Ext]) -> Ext {
    assert_eq!(drawn.len(), k);
    let mut cur: Vec<Ext> = {
        let half = 1usize << (k - 1);
        let ch = &drawn[0];
        (0..half)
            .map(|y| {
                let a = read(2 * y);
                let b = read(2 * y + 1);
                add(mul(sub(b, &a), ch), &a)
            })
            .collect()
    };
    for ch in &drawn[1..] {
        cur = fold_step(&cur, ch);
    }
    cur[0]
}

// ── The fixture gate ─────────────────────────────────────────────────────────

#[test]
fn protocol_parity_bigint_l0() {
    let threads = test_threads();
    let worker = Worker::new_with_num_threads(threads);
    let k = BIGINT_TRACE_LOG2;

    // One source of challenge truth for the oracle AND the instrument.
    let beta = beta();
    let gamma = gamma();
    let alpha = lookup_mult();
    let external = hardcoded_external_challenges();
    let prev: Vec<Ext> = (0..k).map(|j| ext_scalar(0x7A11_0000 + j as u32)).collect();

    // Real witness → production storage (setup + caches + all layer outputs).
    let (artifact, full_trace, table_driver) = bigint_real_witness(&worker);
    let mut storage = build_bigint_storage(
        &artifact,
        full_trace,
        &table_driver,
        alpha,
        gamma,
        &external,
        &worker,
    );

    // Instrument programs over the lowered DAG (same artifact, same trace_len).
    let dag = lower_dag(&artifact).expect("lower_dag");
    validate(&dag).expect("validate(dag)");
    let cross = build_cross_layer_field_map(&dag);
    let layer0 = &dag.layers[0];
    let spine = bwd_roots(layer0);
    assert!(spine.len() > 200, "bigint L0 must batch its full root set");
    let d_r0 = distill(layer0, BwdRegime::R0, &cross, None);
    assert!(!d_r0.skipped_decoder, "bigint L0 is decoder-free (R0)");
    let c_r0 = compile_prog(&d_r0);
    let d_ext = distill(layer0, BwdRegime::Ext, &cross, None);
    assert!(!d_ext.skipped_decoder, "bigint L0 is decoder-free (Ext)");
    let c_ext = compile_prog(&d_ext);

    // Snapshot every layer-0 column (Arc bumps, zero copy) BEFORE the oracle
    // folds storage — the instrument and the (e) check read these.
    let snap_base: HashMap<GKRAddress, Arc<Box<[Bf]>>> = storage.layers[0]
        .base_field_inputs
        .iter()
        .map(|(a, p)| (*a, p.values.clone()))
        .collect();
    let snap_ext: HashMap<GKRAddress, Arc<Box<[Ext]>>> = storage.layers[0]
        .extension_field_inputs
        .iter()
        .map(|(a, p)| (*a, p.values.clone()))
        .collect();

    // Instrument originals: every Read place of the distilled programs must
    // resolve to a REAL production base column.
    let mut base_cols: HashMap<ReadPlace, Arc<Box<[Bf]>>> = HashMap::new();
    for src in &layer0.sources {
        if let SourceKind::Read { place } = &src.kind {
            let addr = crate::tests::gkr::dag_ir_reference::read_place_to_address(place);
            let col = snap_base
                .get(&addr)
                .unwrap_or_else(|| panic!("no production base column for {place:?} ({addr:?})"));
            base_cols.insert(place.clone(), col.clone());
        }
    }
    let vs_cols: HashMap<VirtualSetupKind, Arc<Box<[Bf]>>> = [
        (
            VirtualSetupKind::RangeCheck16Bits,
            VirtualSetupPoly::RangeCheck16Bits,
        ),
        (
            VirtualSetupKind::RangeCheckTimestamp,
            VirtualSetupPoly::RangeCheckTimestamp,
        ),
    ]
    .into_iter()
    .map(|(kind, poly)| {
        let col = snap_base
            .get(&GKRAddress::VirtualSetup(poly))
            .expect("virtual setup poly in storage");
        (kind, col.clone())
    })
    .collect();
    let chal = FixtureChallenges::new(beta, alpha, gamma, &external, spine.len() + 1);
    let cols = FixtureCols {
        k,
        base: base_cols,
        vs: vs_cols,
        chal,
    };

    // The places that need progressively folded buffers in materialized
    // rounds: every Read-origin FoldSource of the Ext program.
    let fold_places: Vec<ReadPlace> = (0..d_ext.specials.len())
        .filter_map(|i| match d_ext.specials.get(i as u16) {
            Some(BwdSpecial::FoldSource {
                origin: OriginLeaf::Read(place),
            }) => Some(place.clone()),
            _ => None,
        })
        .collect();
    assert!(!fold_places.is_empty());

    // Output claims at the previous layer's point (storage layer 1 holds
    // exactly the L0 outputs after the forward loop).
    let eq_full = make_eq_poly_in_full::<Ext>(&prev, &worker);
    let eq_last = &eq_full.last().unwrap()[..];
    let base_outs: Vec<(GKRAddress, Arc<Box<[Bf]>>)> = storage.layers[1]
        .base_field_inputs
        .iter()
        .map(|(a, p)| (*a, p.values.clone()))
        .collect();
    let ext_outs: Vec<(GKRAddress, Arc<Box<[Ext]>>)> = storage.layers[1]
        .extension_field_inputs
        .iter()
        .map(|(a, p)| (*a, p.values.clone()))
        .collect();
    let mut output_claims: BTreeMap<GKRAddress, Ext> = BTreeMap::new();
    for (addr, claim) in par_map(&base_outs, threads, |(addr, vals)| {
        (*addr, evaluate_with_precomputed_eq::<Bf, Ext>(vals, eq_last))
    }) {
        output_claims.insert(addr, claim);
    }
    for (addr, claim) in par_map(&ext_outs, threads, |(addr, vals)| {
        (*addr, evaluate_with_precomputed_eq_ext::<Ext>(vals, eq_last))
    }) {
        output_claims.insert(addr, claim);
    }
    assert!(!output_claims.is_empty());

    // Production oracle run (the transcript authority).
    let mut seed = Seed::default();
    let run = run_layer_oracle::<Bf, Ext>(
        0,
        &artifact.layers[0],
        &output_claims,
        &prev,
        &mut storage,
        beta,
        1 << k,
        alpha,
        gamma,
        &[],
        0,
        &external,
        &mut seed,
        &worker,
    );

    // Alpha-slot pin at scale: the collector's flattened batch weights are
    // consecutive beta powers IN `bwd_roots` ORDER, constraint slots consume a
    // power with zero claim, and the combined claim is the weighted sum.
    assert_eq!(
        run.per_relation_weights.len(),
        spine.len(),
        "collector slot count == bwd spine length"
    );
    let mut expected_claim = Ext::ZERO;
    let mut n_constraint_slots = 0usize;
    for (i, rid) in spine.iter().enumerate() {
        assert_eq!(
            run.per_relation_weights[i],
            cols.chal.beta_pows[i],
            "slot {i} weight must be beta^{i}"
        );
        let root = &layer0.roots[rid.0 as usize];
        match &root.materialize {
            Some(SinkInfo {
                kind: SinkKind::Inner { layer, offset },
                ..
            }) => {
                assert_eq!(*layer, 1);
                let addr = GKRAddress::InnerLayer {
                    layer: 1,
                    offset: *offset,
                };
                expected_claim.add_assign(&mul(cols.chal.beta_pows[i], &output_claims[&addr]));
            }
            None => n_constraint_slots += 1,
            other => panic!("unexpected L0 claim-root sink {other:?}"),
        }
    }
    assert!(n_constraint_slots > 100, "the constraint set must be in the batch");
    assert_eq!(
        run.initial_combined_claim, expected_claim,
        "combined claim over weighted slots"
    );
    assert_eq!(run.per_round_claims[0], run.initial_combined_claim);

    // ── The instrument loop: both policies, full (a)-(e) chain ──
    let mut inst_seed = Seed::default();
    let mut claim = run.initial_combined_claim;
    let mut eq_prefactor = Ext::ONE;
    let mut drawn: Vec<Ext> = Vec::new();
    let mut folded: HashMap<ReadPlace, Vec<Ext>> = HashMap::new();

    for r in 0..k {
        let ctx = format!("[bigint_l0 round {r}]");

        // (d) chain: round-entry claim and eq prefactor match the capture.
        assert_eq!(claim, run.per_round_claims[r], "{ctx} claim chain");
        assert_eq!(
            eq_prefactor, run.per_round_eq_prefactor[r],
            "{ctx} eq-prefactor chain"
        );

        let (c, d) = if r == 0 { (&c_r0, &d_r0) } else { (&c_ext, &d_ext) };
        let bind_always = bind(d, MaterializationPolicy::AlwaysMaterialize, r as u8);
        let bind_lazy2 = bind(d, MaterializationPolicy::LazyUpTo(2), r as u8);
        let materialized = bind_always
            .states
            .iter()
            .any(|s| matches!(s, FoldState::Materialized));

        let acc_size = 1usize << (k - r - 1);
        let eq = &eq_full[k - r - 1];
        assert_eq!(eq.len(), acc_size);

        // Leg A: AlwaysMaterialize (folded buffers once r >= 1).
        let [q0, q2] = par_q_sums(
            threads,
            acc_size,
            k - r - 1,
            eq,
            c,
            d,
            &bind_always,
            &cols,
            if materialized { Some(&folded) } else { None },
            &drawn,
            &format!("{ctx} AlwaysMaterialize"),
        );

        // Leg B: LazyUpTo(2). Its bindings differ from leg A only in rounds
        // 1..=2 — re-evaluate there and pin equality; everywhere else the
        // binding vectors are asserted identical (deterministic interpreter ⇒
        // identical values), so re-evaluation would be a no-op.
        if bind_lazy2.states != bind_always.states {
            assert!(
                (1..=2).contains(&r),
                "{ctx} LazyUpTo(2) may only diverge from AlwaysMaterialize in rounds 1..=2"
            );
            let [l0, l2] = par_q_sums(
                threads,
                acc_size,
                k - r - 1,
                eq,
                c,
                d,
                &bind_lazy2,
                &cols,
                None,
                &drawn,
                &format!("{ctx} LazyUpTo(2)"),
            );
            assert_eq!([l0, l2], [q0, q2], "{ctx} policy legs must agree");
        }

        // Derive d_oracle from (z, C, c0, c2) via the production identity
        // FIRST — never from the candidate q's.
        let [c0, c2] = run.per_round_reduced[r];
        let z = prev[r];
        let big_c = mul(claim, &inv(&eq_prefactor));
        let b1 = sub(Ext::ONE, &z);
        let q1 = mul(sub(big_c, &mul(b1, &c0)), &inv(&z));
        let d_oracle = sub(sub(q1, &c2), &c0);
        let mut g2_oracle = c2;
        g2_oracle.double();
        g2_oracle.double();
        let mut two_d = d_oracle;
        two_d.double();
        g2_oracle.add_assign(&two_d);
        g2_oracle.add_assign(&c0);

        // (a) the reduced evaluations match the oracle coefficients.
        assert_eq!(q0, c0, "{ctx} (a) q0 != c0");
        assert_eq!(q2, g2_oracle, "{ctx} (a) q2 != g(2)");

        // (b) recovered monomials.
        let q1_from_q = mul(sub(big_c, &mul(b1, &q0)), &inv(&z));
        let mut two_q1 = q1_from_q;
        two_q1.double();
        let mut c_rec = sub(add(q2, &q0), &two_q1);
        let two = add(Ext::ONE, &Ext::ONE);
        c_rec.mul_assign(&inv(&two));
        assert_eq!(q0, c0, "{ctx} (b) recovered e != c0");
        assert_eq!(c_rec, c2, "{ctx} (b) recovered c != c2");

        // (c) emission reproduces the committed [E; 4]; (b) d == d_oracle.
        let (coeffs, d_rec) = recover_and_emit::<Bf, Ext>(z, claim, eq_prefactor, q0, q2);
        assert_eq!(d_rec, d_oracle, "{ctx} (b) recovered d");
        assert_eq!(coeffs, run.round_coeffs[r], "{ctx} (c) committed univariate");

        // (d) transcript replay.
        commit_field_els::<Bf, Ext>(&mut inst_seed, &coeffs);
        let ch = draw_random_field_els::<Bf, Ext>(&mut inst_seed, 1)[0];
        assert_eq!(ch, run.folding_challenges[r], "{ctx} (d) folding challenge");
        claim = evaluate_small_univariate_poly::<Bf, Ext, 4>(&coeffs, &ch);
        eq_prefactor = evaluate_eq_poly::<Bf, Ext>(&ch, &prev[r]);
        drawn.push(ch);

        // Advance the folded buffers to depth r+1 for the next round.
        if r + 1 < k {
            let folded_next: Vec<(ReadPlace, Vec<Ext>)> =
                par_map(&fold_places, threads, |place| {
                    let next = if r == 0 {
                        let half = 1usize << (k - 1);
                        let col = &cols.base[place];
                        (0..half)
                            .map(|y| {
                                let a = lift(col[rev_bits(2 * y, k)]);
                                let b = lift(col[rev_bits(2 * y + 1, k)]);
                                add(mul(sub(b, &a), &ch), &a)
                            })
                            .collect()
                    } else {
                        fold_step(&folded[place], &ch)
                    };
                    (place.clone(), next)
                });
            folded = folded_next.into_iter().collect();
        }
    }

    // Chain closes on the loop's normalized final claim.
    let final_norm = mul(claim, &inv(&eq_prefactor));
    assert_eq!(
        final_norm, run.final_normalized_claim,
        "[bigint_l0] final normalized claim"
    );

    // (e) final folded source evaluations: full-depth instrument fold of every
    // production input column (base AND cached-ext) == the production
    // last-evaluations line at r_last.
    assert!(!run.last_evaluations.is_empty());
    let r_last = drawn[k - 1];
    let last_entries: Vec<(GKRAddress, [Ext; 2])> = run
        .last_evaluations
        .iter()
        .map(|(a, v)| (*a, *v))
        .collect();
    assert!(
        last_entries
            .iter()
            .any(|(a, _)| matches!(a, GKRAddress::Cached { .. })),
        "L0 inputs must include cached columns"
    );
    assert!(
        last_entries
            .iter()
            .any(|(a, _)| matches!(a, GKRAddress::BaseLayerWitness(_))),
        "L0 inputs must include base witness columns"
    );
    let e_checks = par_map(&last_entries, threads, |(addr, line)| {
        let expected = interpolate(line[0], line[1], &r_last);
        let full = if let Some(col) = snap_base.get(addr) {
            full_fold_col(&|j| lift(col[rev_bits(j, k)]), k, &drawn)
        } else if let Some(col) = snap_ext.get(addr) {
            full_fold_col(&|j| col[rev_bits(j, k)], k, &drawn)
        } else {
            panic!("last_evaluations address {addr:?} has no layer-0 snapshot column")
        };
        (*addr, full == expected)
    });
    for (addr, ok) in e_checks {
        assert!(ok, "[bigint_l0] (e) final fold mismatch for {addr:?}");
    }
}
