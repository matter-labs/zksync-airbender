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

use std::collections::{BTreeMap, HashMap};

use cs::definitions::GKRAddress;
use cs::gkr_compiler::dag_ir::{
    BatchingOrder, Bf, BwdRegime, ChallengeKey, ChallengePower, ChallengeRef, ChallengeResolver,
    ClaimInfo, DagLayer, Expr, ExprId, Ext, FieldKind, LookupResolver, LookupValueKind, ReadPlace,
    ReadResolver, Resolvers, Root, RootGroup, RootId, RootOrigin, RootSlot, SinkInfo, SinkKind,
    SourceId, SourceInfo, SourceKind, VirtualSetupKind, VirtualSetupResolver,
};
use cs::gkr_compiler::{
    GKRLayerDescription, GateArtifacts, NoFieldGKRRelation, NoFieldMaxQuadraticGKRRelation,
    NoFieldStructuredExpression,
};
use field::{Field, FieldExtension, FixedArrayConvertible, PrimeField};
use gkr_eval_isa::bwd::compile::{compile_distilled, BwdCompiledLayer};
use gkr_eval_isa::bwd::distill::{bind, distill, DistilledLayer};
use gkr_eval_isa::bwd::interp::{interpret_bwd_row, sumcheck_fold_point, Role};
use gkr_eval_isa::bwd::source::{FoldState, MaterializationPolicy};
use gkr_eval_isa::fwd::error::CompileError;
use transcript::Seed;
use worker::Worker;

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
        panic!("micro families have no LookupValue sources ({kind:?})")
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
