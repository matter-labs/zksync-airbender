//! Task 7: G1 — the backward value-parity corpus gate (spec §2, the value gate
//! of the backward-VM CPU instrument).
//!
//! For the 12 pinned Global-Constraints fixtures, per distillable layer × regime
//! {R0, Ext} × role {T0, T2} × policy {AlwaysMaterialize, LazyUpTo(1),
//! LazyUpTo(2)} × round × sampled row, this asserts the backward interpreter
//! (`interpret_bwd_row`) equals the authoritative expression oracle
//!   `Σ_i beta^i · eval(root_i)`  (root 0 unscaled)
//! over the CANONICAL `bwd_roots` order, BIT-EXACT.
//!
//! # The shared transform (why this is program-vs-expression)
//!
//! Both sides substitute each backward variable's finite-point value at the
//! LEAVES via the ONE shared helper pair exported from the interpreter —
//! [`role_combine`] (the T0/T2 role point) and [`sumcheck_fold_point`] (the
//! depth-`round` fold from originals). The interpreter applies them inside its
//! operand resolver; the oracle applies them at every canonical `Read`/
//! `VirtualSetup` leaf of a rewrite-aware evaluator (`LookupValue` ↦ its query
//! cone, the backward semantics — mirroring `bwd_distill_fixtures.rs`). So the
//! transform itself is never self-oracled; the DIFFERENTIAL is the compiled
//! program versus the canonical expression tree.
//!
//! # Round / policy coverage and the materialized-buffer resolver
//!
//! A `FoldSource` at round `r` reads either the depth-`r` fold of the originals
//! (`LazyFromOriginals`) or a materialized previous-round buffer
//! (`AlwaysMaterialize`, and `LazyUpTo(k)` once `r > k`). To keep all policies
//! bit-identical at a round where the fold genuinely engages, the materialized
//! runs are fed a `BufferAt` resolver that IS the depth-`r` fold of the same
//! originals (folded via the shared `sumcheck_fold_point`) — the corpus analogue
//! of `interp.rs`'s `BufferRead` unit-test trick. All synthetic resolver values
//! and the round/alpha challenges live in the base subfield, so the fold stays
//! in the base subfield and the `virtual_setup` buffer (a `Bf`) reproduces it
//! exactly (a parity harness property shared with the forward gate, not a
//! semantic restriction).

mod common;

use std::collections::{BTreeSet, HashMap};

use common::{lift, load_fixture, resolvers, schedule_stem, SyntheticResolvers};
use cs::gkr_compiler::dag_ir::{
    bwd_roots, eval_layer_expr, lower_dag, validate, Bf, BwdRegime, ChallengeKey, ChallengePower,
    ChallengeRef, ChallengeResolver, DagLayer, Expr, ExprId, Ext, LookupResolver, LookupValueKind,
    ReadPlace, ReadResolver, Resolvers, SourceKind, VirtualSetupKind, VirtualSetupResolver,
};
use field::{Field, FieldExtension, PrimeField};
use gkr_eval_isa::bwd::compile::compile_distilled;
use gkr_eval_isa::bwd::distill::{bind, distill};
use gkr_eval_isa::bwd::interp::{interpret_bwd_row, role_combine, sumcheck_fold_point, Role};
use gkr_eval_isa::bwd::source::MaterializationPolicy;
use gkr_eval_isa::fwd::compile::build_cross_layer_field_map;
use gkr_eval_isa::fwd::encode::{decode, encode};
use gkr_eval_isa::fwd::error::CompileError;
use gkr_eval_isa::fwd::isa::{Instr, OperandLine};

/// The 12 pinned Global-Constraints fixtures — same list as
/// `bwd_distill_fixtures.rs` / `fwd_vm_desc_census.rs`.
const FIXTURES: &[&str] = &[
    "add_sub_lui_auipc_mop_layout_gkr.json",
    "bigint_with_extended_control_layout_gkr.json",
    "blake2_g_function_layout_gkr.json",
    "blake2_with_extended_control_layout_gkr.json",
    "inits_and_teardowns_preprocessed_layout_gkr.json",
    "jump_branch_slt_layout_gkr.json",
    "keccak_special5_layout_gkr.json",
    "mem_subword_only_layout_gkr.json",
    "mem_word_only_layout_gkr.json",
    "shift_binop_layout_gkr.json",
    "unsigned_mul_div_layout_gkr.json",
    "unified_reduced_machine_layout_gkr.json",
];

/// Decoder-bearing layers, skipped in BOTH regimes (out of v1). Pinned so a
/// coverage change is loud — identical to `bwd_distill_fixtures.rs`.
const PINNED_SKIPPED_DECODER: &[&str] = &[
    "add_sub_lui_auipc_mop[L0]",
    "jump_branch_slt[L0]",
    "mem_subword_only[L0]",
    "mem_word_only[L0]",
    "shift_binop[L0]",
    "unified_reduced_machine[L0]",
    "unsigned_mul_div[L0]",
];

/// Distillable layers whose placement floor exceeds b16 — the value gate still
/// covers them by retrying `compile_distilled` at the reported floor. Pinned
/// (with floor) so drift is loud; identical to `bwd_distill_fixtures.rs`.
const PINNED_B16_INFEASIBLE: &[&str] = &[
    "bigint_with_extended_control[L0][R0] floor=83",
    "bigint_with_extended_control[L0][Ext] floor=320",
    "keccak_special5[L0][R0] floor=46",
    "keccak_special5[L0][Ext] floor=172",
    "unsigned_mul_div[L1][Ext] floor=40",
];

const BUDGET: usize = 16;
const ROUNDS: &[u8] = &[0, 1, 2];
const ROLES: &[Role] = &[Role::T0, Role::T2];
const POLICIES: &[MaterializationPolicy] = &[
    MaterializationPolicy::AlwaysMaterialize,
    MaterializationPolicy::LazyUpTo(1),
    MaterializationPolicy::LazyUpTo(2),
];
/// Sampled backward rows — modest, per the runtime budget (release, big test).
const ROWS: &[usize] = &[0, 1];

/// beta^i as the distilled spine resolves it (i >= 1): power `One` at i == 1,
/// `Static(i)` beyond — mirrors `distill`'s alpha-spine construction.
fn beta_i(r: &Resolvers<'_>, i: usize) -> Ext {
    let power = if i == 1 { ChallengePower::One } else { ChallengePower::Static(i as u32) };
    r.challenge.challenge(&ChallengeRef { key: ChallengeKey::ClaimBatching, power })
}

// ── Materialized-buffer resolver ────────────────────────────────────────────
//
// A resolver whose reads ARE the depth-`round` fold of the ORIGINALS (`orig`),
// folded with `ch` via the shared `sumcheck_fold_point`. Feeding this to a
// `Materialized` binding reproduces exactly what a `LazyFromOriginals { depth:
// round }` binding computes from `orig` — so all policies agree bit-for-bit.
struct BufferAt<'a> {
    orig: &'a SyntheticResolvers,
    round: u8,
    ch: &'a [Ext],
}

impl ReadResolver for BufferAt<'_> {
    fn read(&self, place: &ReadPlace, y: usize) -> Ext {
        sumcheck_fold_point(&|z| self.orig.read(place, z), y, self.round, self.ch)
            .expect("buffer read fold within round_challenges depth")
    }
}
impl VirtualSetupResolver for BufferAt<'_> {
    fn virtual_setup(&self, kind: &VirtualSetupKind, y: usize) -> Bf {
        let folded = sumcheck_fold_point(&|z| lift(self.orig.virtual_setup(kind, z)), y, self.round, self.ch)
            .expect("buffer vs fold within round_challenges depth");
        // Base subfield throughout (synthetic values + base round challenges),
        // so coeff 0 reproduces the folded value exactly.
        <Ext as FieldExtension<Bf>>::into_coeffs(folded)[0]
    }
}
impl LookupResolver for BufferAt<'_> {
    fn lookup(&self, kind: &LookupValueKind, set_index: usize, evaluated_query: Ext, row: usize) -> Bf {
        self.orig.lookup(kind, set_index, evaluated_query, row)
    }
}
impl ChallengeResolver for BufferAt<'_> {
    fn challenge(&self, r: &ChallengeRef) -> Ext {
        self.orig.challenge(r)
    }
}

fn buffer_resolvers<'a>(b: &'a BufferAt<'a>) -> Resolvers<'a> {
    Resolvers { read: b, lookup: b, virtual_setup: b, challenge: b }
}

// ── The oracle: rewrite-aware, finite-point evaluation of the canonical layer ──

/// Evaluate canonical expr `e` at (`regime`, `role`, `row`, `round`), applying
/// the SHARED role+fold transform at every `Read`/`VirtualSetup` leaf:
///   * `Read`  → depth = `round` in Ext (a FoldSource), 0 in R0 (a plain Global
///     backing that is not folded), then `role_combine` over the `(2row, 2row+1)`
///     pair;
///   * `VirtualSetup` → depth = `round` in BOTH regimes, then `role_combine`;
///   * `LookupValue` → recurse into its query cone (the backward rewrite);
///   * `Constant`/`Challenge` → row-independent, role/fold-invariant, delegated
///     to the authoritative `eval_layer_expr` verbatim.
#[allow(clippy::too_many_arguments)]
fn eval_oracle(
    layer: &DagLayer,
    e: ExprId,
    regime: BwdRegime,
    role: Role,
    row: usize,
    round: u8,
    ch: &[Ext],
    orig: &SyntheticResolvers,
    plain: &Resolvers<'_>,
    memo: &mut HashMap<ExprId, Ext>,
) -> Ext {
    if let Some(&v) = memo.get(&e) {
        return v;
    }
    let v = match &layer.exprs[e.0 as usize] {
        Expr::Source(sid) => match &layer.sources[sid.0 as usize].kind {
            SourceKind::LookupValue { query, .. } => {
                eval_oracle(layer, *query, regime, role, row, round, ch, orig, plain, memo)
            }
            SourceKind::Read { place } => {
                let depth = if regime == BwdRegime::Ext { round } else { 0 };
                let base = |z: usize| orig.read(place, z);
                let a = sumcheck_fold_point(&base, 2 * row, depth, ch).unwrap();
                let b = sumcheck_fold_point(&base, 2 * row + 1, depth, ch).unwrap();
                role_combine(role, a, b)
            }
            SourceKind::VirtualSetup { kind } => {
                let base = |z: usize| lift(orig.virtual_setup(kind, z));
                let a = sumcheck_fold_point(&base, 2 * row, round, ch).unwrap();
                let b = sumcheck_fold_point(&base, 2 * row + 1, round, ch).unwrap();
                role_combine(role, a, b)
            }
            SourceKind::Constant { .. } | SourceKind::Challenge { .. } => {
                eval_layer_expr(layer, e, row, plain)
            }
        },
        Expr::Add(children) => {
            let ch_ids = children.clone();
            let mut acc = Ext::ZERO;
            for c in ch_ids {
                let t = eval_oracle(layer, c, regime, role, row, round, ch, orig, plain, memo);
                acc.add_assign(&t);
            }
            acc
        }
        Expr::Mul(children) => {
            let ch_ids = children.clone();
            let mut acc = Ext::ONE;
            for c in ch_ids {
                let t = eval_oracle(layer, c, regime, role, row, round, ch, orig, plain, memo);
                acc.mul_assign(&t);
            }
            acc
        }
    };
    memo.insert(e, v);
    v
}

/// The alpha-combined oracle value: `Σ_i beta^i · eval(root_i)`, root 0 unscaled,
/// over the canonical `bwd_roots` batching order.
#[allow(clippy::too_many_arguments)]
fn oracle_root(
    layer: &DagLayer,
    regime: BwdRegime,
    role: Role,
    row: usize,
    round: u8,
    ch: &[Ext],
    orig: &SyntheticResolvers,
    plain: &Resolvers<'_>,
) -> Ext {
    let mut memo: HashMap<ExprId, Ext> = HashMap::new();
    let mut acc = Ext::ZERO;
    for (i, &rid) in bwd_roots(layer).iter().enumerate() {
        let expr = layer.roots[rid.0 as usize].expr;
        let mut t = eval_oracle(layer, expr, regime, role, row, round, ch, orig, plain, &mut memo);
        if i >= 1 {
            t.mul_assign(&beta_i(plain, i));
        }
        acc.add_assign(&t);
    }
    acc
}

// ── Structural program checks ───────────────────────────────────────────────

fn for_each_operand(p: &gkr_eval_isa::fwd::isa::Program, mut f: impl FnMut(&OperandLine)) {
    for instr in &p.instrs {
        match instr {
            Instr::Add { operands, .. } | Instr::Mul { operands, .. } => {
                operands.iter().for_each(&mut f)
            }
            Instr::Fma { pairs, .. } => pairs.iter().for_each(|(l, r)| {
                f(l);
                f(r);
            }),
            Instr::Mov { src: Some(op), .. } => f(op),
            Instr::Mov { src: None, .. } => {}
        }
    }
}

// ── The gate ────────────────────────────────────────────────────────────────

#[test]
fn bwd_value_parity_all_fixtures() {
    // Base-subfield round challenges (fold depth up to max(ROUNDS)).
    let round_challenges: Vec<Ext> = [3u32, 5, 7]
        .into_iter()
        .map(|k| lift(Bf::from_u32_with_reduction(k)))
        .collect();

    let syn = SyntheticResolvers;
    let plain = resolvers(&syn);

    let mut skipped: BTreeSet<String> = BTreeSet::new();
    let mut floor_retries: BTreeSet<String> = BTreeSet::new();
    let mut interpreted_r0 = 0usize;
    let mut interpreted_ext = 0usize;
    let mut comparisons = 0usize;

    for name in FIXTURES {
        let stem = schedule_stem(name);
        let artifact = load_fixture(name);
        let dag = lower_dag(&artifact).unwrap_or_else(|e| panic!("[{name}] lower_dag: {e}"));
        validate(&dag).unwrap_or_else(|e| panic!("[{name}] validate: {e}"));
        let cross = build_cross_layer_field_map(&dag);

        for (li, layer) in dag.layers.iter().enumerate() {
            if bwd_roots(layer).is_empty() {
                continue; // nothing to prove backward
            }
            for &regime in &[BwdRegime::R0, BwdRegime::Ext] {
                let d = distill(layer, regime, &cross, None);
                if d.skipped_decoder {
                    // Out of v1 in BOTH regimes; record once (regime-independent).
                    skipped.insert(format!("{stem}[L{li}]"));
                    continue;
                }

                let ctx = format!("{stem} L{li} {regime:?}");
                // Every distillable layer must be interpreted: retry any b16
                // placement floor at its floor (the value gate cares about
                // semantics, not budget).
                let c = match compile_distilled(&d, BUDGET, None) {
                    Ok(c) => c,
                    Err(CompileError::BudgetBelowFloor { floor, .. }) => {
                        floor_retries.insert(format!("{stem}[L{li}][{regime:?}] floor={floor}"));
                        compile_distilled(&d, floor, None)
                            .unwrap_or_else(|e| panic!("[{ctx}] compile at floor {floor}: {e:?}"))
                    }
                    Err(e) => panic!("[{ctx}] compile_distilled: {e:?}"),
                };
                match regime {
                    BwdRegime::R0 => interpreted_r0 += 1,
                    BwdRegime::Ext => interpreted_ext += 1,
                }

                // (i) encode/decode roundtrip reproduces the program exactly.
                let lanes = encode(&c.program).unwrap_or_else(|e| panic!("[{ctx}] encode: {e:?}"));
                let decoded = decode(&lanes).unwrap_or_else(|e| panic!("[{ctx}] decode: {e:?}"));
                assert_eq!(decoded, c.program, "[{ctx}] encode/decode roundtrip mismatch");

                // (ii) every Special desc is in range, and every table entry is
                // referenced (no orphan descriptors).
                let n_specials = c.specials.len();
                let mut used: BTreeSet<u16> = BTreeSet::new();
                for_each_operand(&c.program, |op| {
                    if let OperandLine::Special { desc } = op {
                        assert!(
                            (*desc as usize) < n_specials,
                            "[{ctx}] Special desc {desc} >= specials.len() {n_specials}"
                        );
                        used.insert(*desc);
                    }
                });
                for i in 0..n_specials as u16 {
                    assert!(
                        used.contains(&i),
                        "[{ctx}] orphan descriptor {i} of {n_specials} is never referenced"
                    );
                }

                // (iii) value parity: interp == oracle for every round/role/row,
                // and all policies bit-identical.
                for &round in ROUNDS {
                    for &role in ROLES {
                        for &row in ROWS {
                            let expected = oracle_root(
                                layer, regime, role, row, round, &round_challenges, &syn, &plain,
                            );

                            let mut first: Option<Ext> = None;
                            for &policy in POLICIES {
                                let bindings = bind(&d, policy, round);
                                let materialized = bindings
                                    .states
                                    .iter()
                                    .any(|s| matches!(s, gkr_eval_isa::bwd::source::FoldState::Materialized));
                                let buf = BufferAt { orig: &syn, round, ch: &round_challenges };
                                let buf_r = buffer_resolvers(&buf);
                                let run_r = if materialized { &buf_r } else { &plain };

                                let got = interpret_bwd_row(
                                    &c, &d, &bindings, run_r, role, row, &round_challenges,
                                )
                                .unwrap_or_else(|e| {
                                    panic!("[{ctx}] interp round {round} {role:?} row {row} {policy:?}: {e:?}")
                                });

                                assert_eq!(
                                    got, expected,
                                    "[{ctx}] value mismatch: round {round} {role:?} row {row} {policy:?} \
                                     interp != oracle"
                                );
                                match first {
                                    None => first = Some(got),
                                    Some(f) => assert_eq!(
                                        got, f,
                                        "[{ctx}] policy {policy:?} disagrees with first policy \
                                         (round {round} {role:?} row {row})"
                                    ),
                                }
                                comparisons += 1;
                            }
                        }
                    }
                }
            }
        }
    }

    println!(
        "bwd G1: interpreted {interpreted_r0} R0 + {interpreted_ext} Ext layer instances; \
         {comparisons} interp==oracle comparisons"
    );
    println!("floor-retries ({}):", floor_retries.len());
    for s in &floor_retries {
        println!("  {s}");
    }
    println!("skipped_decoder ({}):", skipped.len());
    for s in &skipped {
        println!("  {s}");
    }

    assert!(comparisons > 0, "vacuous — no value-parity comparisons made");
    assert!(interpreted_r0 > 0 && interpreted_ext > 0, "both regimes must be exercised");

    let pinned_skip: BTreeSet<String> =
        PINNED_SKIPPED_DECODER.iter().map(|s| s.to_string()).collect();
    assert_eq!(
        skipped, pinned_skip,
        "skipped_decoder set drifted from the pinned expectation — update deliberately"
    );
    let pinned_floor: BTreeSet<String> =
        PINNED_B16_INFEASIBLE.iter().map(|s| s.to_string()).collect();
    assert_eq!(
        floor_retries, pinned_floor,
        "b16-infeasible floor-retry set drifted from the pinned expectation — update deliberately"
    );
}
