//! Task 12: the backward-VM DRAM byte cost model (spec §6).
//!
//! Turns a compiled [`BwdCompiledLayer`] + a `(policy, round)` binding into the
//! per-row DRAM byte traffic the backward interpreter would move, split by the
//! evaluation-point [`Role`] and with fold-store bytes tallied separately. This
//! is the accounting the census ([`tests/bwd_census.rs`]) aggregates; it is
//! deliberately NOT wired into the compiler (traffic search uses the coarser
//! role-neutral [`BwdTrafficStats`] in `compile.rs`).
//!
//! # Byte model (spec §6)
//!
//! A backward round re-reads each SOURCE operand's pair `(v(2x), v(2x+1))` of the
//! previous representation and role-combines it ([`super::interp::role_combine`]).
//! The role fixes how many pair elements are actually consumed:
//!   * `T0 -> v(2x)` — **1** element read;
//!   * `T2 -> 2·v(2x+1) − v(2x)` — **2** element reads.
//!
//! Per element:
//!   * a `Materialized` fold reads one Ext buffer value = `EXT_BYTES` (16 B);
//!   * a `LazyFromOriginals { depth: d }` fold recomputes from `2^d` originals at
//!     base width = `4·2^d` B;
//!   * an `R0` `Global` backing reads one native-width value = `width·4` B.
//!
//! Fold STORES (writing a round's folded Ext buffer for the next round to read)
//! are tallied separately at `EXT_BYTES` per distinct materialized fold buffer.
//!
//! # VS-ABI constraint (Task 11)
//!
//! In the `Ext` regime a `VirtualSetup` origin leaf is rewritten to a
//! `FoldSource`, but its folded buffer cannot currently be materialized (the `Bf`
//! virtual-setup resolver cannot carry an Ext folded buffer). So VS-origin fold
//! costs are accounted under `LazyFromOriginals { depth: round }` for ALL
//! policies here. This MIRRORS the runtime binder [`super::distill::bind`], which
//! enforces the same VS forced-lazy convention: the cost model and the binder
//! agree, so this accounting is honest, not a divergent estimate.

use std::collections::BTreeSet;

use super::compile::BwdCompiledLayer;
use super::interp::Role;
use super::source::{BwdSpecial, FoldState, MaterializationPolicy, OriginLeaf};
use crate::fwd::isa::{Instr, OperandField, OperandLine};

/// Bytes per field cell (a `Bf` limb).
pub const CELL_BYTES: usize = 4;
/// Ext width in cells.
pub const EXT_CELLS: usize = 4;
/// Bytes of one Ext value (a materialized fold buffer element).
pub const EXT_BYTES: usize = EXT_CELLS * CELL_BYTES; // 16

/// How many pair elements the role actually consumes: `T0` reads `v(2x)` only
/// (1); `T2` reads `v(2x)` and `v(2x+1)` (2) to form `2b − a`.
#[inline]
pub fn role_read_count(role: Role) -> usize {
    match role {
        Role::T0 => 1,
        Role::T2 => 2,
    }
}

/// DRAM bytes of ONE fold-source pair element under its bound [`FoldState`].
#[inline]
pub fn fold_element_bytes(state: FoldState) -> usize {
    match state {
        FoldState::Materialized => EXT_BYTES,
        FoldState::LazyFromOriginals { depth } => CELL_BYTES * (1usize << depth),
    }
}

/// DRAM read bytes for one fold-source operand occurrence at `role`/`state`.
#[inline]
pub fn fold_read_bytes(role: Role, state: FoldState) -> usize {
    role_read_count(role) * fold_element_bytes(state)
}

/// DRAM read bytes for one R0 `Global` backing occurrence: native width
/// (`width_cells` cells) per element, `role`-many elements.
#[inline]
pub fn r0_read_bytes(role: Role, width_cells: usize) -> usize {
    role_read_count(role) * width_cells * CELL_BYTES
}

/// The [`FoldState`] a **Read**-origin fold source binds at `round` under
/// `policy` — mirrors the `FoldSource` branch of [`super::distill::bind`]:
/// round 0 has no previous buffer (`Lazy{0}`); `AlwaysMaterialize` reads the
/// buffer for round ≥ 1; `LazyUpTo(k)` recomputes at `depth = round` while
/// `round ≤ k`, else reads the buffer.
#[inline]
pub fn read_fold_state(policy: MaterializationPolicy, round: u8) -> FoldState {
    if round == 0 {
        return FoldState::LazyFromOriginals { depth: 0 };
    }
    match policy {
        MaterializationPolicy::AlwaysMaterialize => FoldState::Materialized,
        MaterializationPolicy::LazyUpTo(k) => {
            if round <= k {
                FoldState::LazyFromOriginals { depth: round }
            } else {
                FoldState::Materialized
            }
        }
    }
}

/// The effective [`FoldState`] the cost model accounts a fold source's origin
/// under. This MIRRORS [`super::distill::bind`] exactly — both apply the VS
/// forced-lazy convention (VS origins are always lazy, Task 11); the local copy
/// exists so the census can map an origin → state without a `BwdBindings` vector.
#[inline]
fn effective_fold_state(origin: &OriginLeaf, policy: MaterializationPolicy, round: u8) -> FoldState {
    match origin {
        // VS-ABI (Task 11): VS-origin folds cannot materialize — always lazy.
        // Same rule the runtime binder `distill::bind` enforces.
        OriginLeaf::VirtualSetup { .. } => FoldState::LazyFromOriginals { depth: round },
        OriginLeaf::Read(_) => read_fold_state(policy, round),
    }
}

/// Per-round DRAM byte breakdown of one compiled backward layer, in bytes moved
/// **per logical row** at this `(policy, round)`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RoundCost {
    /// Read bytes evaluating the row at point `T0`.
    pub t0_read_bytes: usize,
    /// Read bytes evaluating the row at point `T2`.
    pub t2_read_bytes: usize,
    /// Fold-store bytes: writing this round's materialized fold buffers
    /// (`EXT_BYTES` per distinct materialized Read-origin fold source).
    pub fold_store_bytes: usize,
}

impl RoundCost {
    /// Both evaluation points are needed each round: `T0 + T2` read bytes.
    pub fn read_bytes(&self) -> usize {
        self.t0_read_bytes + self.t2_read_bytes
    }
    /// Reads (both points) + fold stores.
    pub fn total_bytes(&self) -> usize {
        self.read_bytes() + self.fold_store_bytes
    }
}

/// Visit every operand of an instruction with its field.
fn for_each_operand(instr: &Instr, mut f: impl FnMut(&OperandLine, OperandField)) {
    match instr {
        Instr::Mov { src: Some(op), field, .. } => f(op, *field),
        Instr::Mov { src: None, .. } => {}
        Instr::Add { operands, field, .. } | Instr::Mul { operands, field, .. } => {
            for op in operands {
                f(op, *field);
            }
        }
        Instr::Fma { pairs, field_lhs, field_rhs, .. } => {
            for (l, r) in pairs {
                f(l, *field_lhs);
                f(r, *field_rhs);
            }
        }
    }
}

/// Tally the per-row DRAM byte cost of `c` at `(policy, round)`.
///
/// Reads are tallied per FoldSource/Global **operand occurrence** (an uncached
/// value used N times folds N times — the interpreter re-resolves each use;
/// admitted sites read a smem cell instead and drop out of this tally). Stores
/// are tallied per **distinct** materialized Read-origin fold buffer.
pub fn round_cost(c: &BwdCompiledLayer, policy: MaterializationPolicy, round: u8) -> RoundCost {
    let mut cost = RoundCost::default();
    let mut materialized_descs: BTreeSet<u16> = BTreeSet::new();

    for instr in &c.program.instrs {
        for_each_operand(instr, |op, field| match op {
            OperandLine::Global { .. } => {
                let w = match field {
                    OperandField::Base => 1,
                    OperandField::Ext => EXT_CELLS,
                };
                cost.t0_read_bytes += r0_read_bytes(Role::T0, w);
                cost.t2_read_bytes += r0_read_bytes(Role::T2, w);
            }
            OperandLine::Special { desc } => match c.specials.get(*desc) {
                Some(BwdSpecial::FoldSource { origin }) => {
                    let state = effective_fold_state(origin, policy, round);
                    cost.t0_read_bytes += fold_read_bytes(Role::T0, state);
                    cost.t2_read_bytes += fold_read_bytes(Role::T2, state);
                    if state == FoldState::Materialized {
                        materialized_descs.insert(*desc);
                    }
                }
                // R0 VirtualSetup specials are procedurally generated (no DRAM);
                // None is unreachable for a well-formed compile.
                _ => {}
            },
            // Smem cells / Ldc consts+challenges / inline literals: no DRAM.
            OperandLine::Smem { .. } | OperandLine::Ldc { .. } => {}
        });
    }

    cost.fold_store_bytes = materialized_descs.len() * EXT_BYTES;
    cost
}

/// Geometric-sum DRAM byte total over the backward round sequence
/// `0..=max_round`: round `r` processes `2^{-r}` of the rows, so its per-row
/// cost is weighted `2^{-r}`. Round 0 (depth-0 base) is included — it is the
/// largest, policy-invariant round. Returned in bytes (fractional; the halving
/// weights are exact powers of two).
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct GeoCost {
    pub t0_read_bytes: f64,
    pub t2_read_bytes: f64,
    pub fold_store_bytes: f64,
}

impl GeoCost {
    pub fn read_bytes(&self) -> f64 {
        self.t0_read_bytes + self.t2_read_bytes
    }
    pub fn total_bytes(&self) -> f64 {
        self.read_bytes() + self.fold_store_bytes
    }
}

/// Accumulate [`round_cost`] over `0..=max_round` with geometric `2^{-r}` row
/// weights.
pub fn geometric_total(
    c: &BwdCompiledLayer,
    policy: MaterializationPolicy,
    max_round: u8,
) -> GeoCost {
    let mut g = GeoCost::default();
    for r in 0..=max_round {
        let w = 1.0f64 / (1u64 << r) as f64;
        let rc = round_cost(c, policy, r);
        g.t0_read_bytes += rc.t0_read_bytes as f64 * w;
        g.t2_read_bytes += rc.t2_read_bytes as f64 * w;
        g.fold_store_bytes += rc.fold_store_bytes as f64 * w;
    }
    g
}

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bwd::distill::distill;
    use crate::fwd::isa::{Instr, OperandLine};
    use cs::gkr_compiler::dag_ir::{
        BatchingOrder, BwdRegime, ClaimInfo, DagLayer, Expr, ExprId, Root, RootGroup, RootId,
        RootOrigin, RootSlot, SourceId, SourceInfo, SourceKind, VirtualSetupKind,
    };
    use std::collections::{BTreeMap, HashMap};

    // ── (1) hand-computed byte model: role × policy × depth ──────────────────

    #[test]
    fn fold_element_bytes_by_state() {
        // Materialized: one Ext buffer element = 16 B.
        assert_eq!(fold_element_bytes(FoldState::Materialized), 16);
        // Lazy depth d: 2^d originals at base width (4 B).
        assert_eq!(fold_element_bytes(FoldState::LazyFromOriginals { depth: 0 }), 4);
        assert_eq!(fold_element_bytes(FoldState::LazyFromOriginals { depth: 1 }), 8);
        assert_eq!(fold_element_bytes(FoldState::LazyFromOriginals { depth: 2 }), 16);
        assert_eq!(fold_element_bytes(FoldState::LazyFromOriginals { depth: 3 }), 32);
        assert_eq!(fold_element_bytes(FoldState::LazyFromOriginals { depth: 4 }), 64);
    }

    #[test]
    fn fold_read_bytes_by_role_and_state() {
        // T0 = 1 element, T2 = 2 elements.
        assert_eq!(fold_read_bytes(Role::T0, FoldState::Materialized), 16);
        assert_eq!(fold_read_bytes(Role::T2, FoldState::Materialized), 32);
        assert_eq!(fold_read_bytes(Role::T0, FoldState::LazyFromOriginals { depth: 0 }), 4);
        assert_eq!(fold_read_bytes(Role::T2, FoldState::LazyFromOriginals { depth: 0 }), 8);
        assert_eq!(fold_read_bytes(Role::T0, FoldState::LazyFromOriginals { depth: 1 }), 8);
        assert_eq!(fold_read_bytes(Role::T2, FoldState::LazyFromOriginals { depth: 1 }), 16);
        // Crossover: lazy depth 2 costs exactly a materialized read.
        assert_eq!(
            fold_read_bytes(Role::T0, FoldState::LazyFromOriginals { depth: 2 }),
            fold_read_bytes(Role::T0, FoldState::Materialized)
        );
        // depth 3 lazy is strictly worse than materialized.
        assert!(
            fold_read_bytes(Role::T0, FoldState::LazyFromOriginals { depth: 3 })
                > fold_read_bytes(Role::T0, FoldState::Materialized)
        );
    }

    #[test]
    fn r0_read_bytes_native_widths() {
        // Base backing (width 1): T0 = 4, T2 = 8.
        assert_eq!(r0_read_bytes(Role::T0, 1), 4);
        assert_eq!(r0_read_bytes(Role::T2, 1), 8);
        // Ext backing (width 4): T0 = 16, T2 = 32.
        assert_eq!(r0_read_bytes(Role::T0, 4), 16);
        assert_eq!(r0_read_bytes(Role::T2, 4), 32);
    }

    #[test]
    fn read_fold_state_policy_round_mapping() {
        // Round 0 is always the depth-0 base regardless of policy.
        assert_eq!(
            read_fold_state(MaterializationPolicy::AlwaysMaterialize, 0),
            FoldState::LazyFromOriginals { depth: 0 }
        );
        assert_eq!(
            read_fold_state(MaterializationPolicy::LazyUpTo(3), 0),
            FoldState::LazyFromOriginals { depth: 0 }
        );
        // AlwaysMaterialize: buffer read at every round ≥ 1.
        assert_eq!(
            read_fold_state(MaterializationPolicy::AlwaysMaterialize, 2),
            FoldState::Materialized
        );
        // LazyUpTo(k): recompute at depth = round while round ≤ k, else buffer.
        assert_eq!(
            read_fold_state(MaterializationPolicy::LazyUpTo(2), 2),
            FoldState::LazyFromOriginals { depth: 2 }
        );
        assert_eq!(
            read_fold_state(MaterializationPolicy::LazyUpTo(2), 3),
            FoldState::Materialized
        );
    }

    // ── (2) program-level round_cost over compiled layers ─────────────────────

    fn read_src(column: usize) -> SourceInfo {
        SourceInfo {
            kind: SourceKind::Read {
                place: cs::gkr_compiler::dag_ir::ReadPlace::BaseLayerWitness { column },
            },
        }
    }

    fn claim_only_root(expr: ExprId) -> Root {
        Root {
            expr,
            materialize: None,
            claim: Some(ClaimInfo {
                origin: RootOrigin {
                    group: RootGroup::Gates,
                    relation_index: 0,
                    slot: RootSlot::Constraint(0),
                },
            }),
        }
    }

    fn one_root_layer(sources: Vec<SourceInfo>, exprs: Vec<Expr>, root: ExprId) -> DagLayer {
        DagLayer {
            sources,
            exprs,
            roots: vec![claim_only_root(root)],
            batching: BatchingOrder { roots: vec![RootId(0)] },
            resolutions: BTreeMap::new(),
        }
    }

    #[test]
    fn round_cost_single_ext_fold_source() {
        // One bare Read leaf → one Ext FoldSource occurrence.
        let l = one_root_layer(vec![read_src(0)], vec![Expr::Source(SourceId(0))], ExprId(0));
        let d = distill(&l, BwdRegime::Ext, &HashMap::new(), None);
        let c = compile_distilled_expect(&d);
        assert_eq!(c.stats_ext.fold_uses, 1, "exactly one fold occurrence");

        // Round 0: Lazy{0} → T0 = 4, T2 = 8, no store.
        let r0 = round_cost(&c, MaterializationPolicy::AlwaysMaterialize, 0);
        assert_eq!(r0, RoundCost { t0_read_bytes: 4, t2_read_bytes: 8, fold_store_bytes: 0 });

        // Round 2 AlwaysMaterialize → Materialized: T0 = 16, T2 = 32, one store 16.
        let r2 = round_cost(&c, MaterializationPolicy::AlwaysMaterialize, 2);
        assert_eq!(r2, RoundCost { t0_read_bytes: 16, t2_read_bytes: 32, fold_store_bytes: 16 });

        // Round 2 LazyUpTo(2) → Lazy{2}: T0 = 16, T2 = 32, no store.
        let l2 = round_cost(&c, MaterializationPolicy::LazyUpTo(2), 2);
        assert_eq!(l2, RoundCost { t0_read_bytes: 16, t2_read_bytes: 32, fold_store_bytes: 0 });

        // Round 3 LazyUpTo(2) → Materialized (past k): store reappears.
        let l3 = round_cost(&c, MaterializationPolicy::LazyUpTo(2), 3);
        assert_eq!(l3.fold_store_bytes, 16);
    }

    #[test]
    fn round_cost_vs_origin_is_always_lazy() {
        // One VirtualSetup leaf → Ext FoldSource with a VS origin. Under
        // AlwaysMaterialize it must STILL be accounted lazy (VS-ABI) — the same
        // forced-lazy state `distill::bind` binds it to — never a materialized
        // buffer, so no store bytes at any round.
        let l = one_root_layer(
            vec![SourceInfo {
                kind: SourceKind::VirtualSetup { kind: VirtualSetupKind::RangeCheck16Bits },
            }],
            vec![Expr::Source(SourceId(0))],
            ExprId(0),
        );
        let d = distill(&l, BwdRegime::Ext, &HashMap::new(), None);
        let c = compile_distilled_expect(&d);
        assert_eq!(c.stats_ext.fold_uses, 1);

        // Round 3 AlwaysMaterialize: VS override keeps it lazy depth 3.
        let r = round_cost(&c, MaterializationPolicy::AlwaysMaterialize, 3);
        assert_eq!(r.t0_read_bytes, fold_read_bytes(Role::T0, FoldState::LazyFromOriginals { depth: 3 }));
        assert_eq!(r.fold_store_bytes, 0, "VS origins never materialize (no store)");
    }

    #[test]
    fn round_cost_r0_global_backing_is_round_flat() {
        // R0 regime: the Read leaf stays a Global backing (base width 1), so per
        // round the cost is role-only and round-invariant.
        let l = one_root_layer(vec![read_src(0)], vec![Expr::Source(SourceId(0))], ExprId(0));
        let d = distill(&l, BwdRegime::R0, &HashMap::new(), None);
        let c = compile_distilled_expect(&d);
        assert_eq!(c.stats_ext.fold_uses, 0, "R0 has no fold sources");
        assert!(matches!(&c.program.instrs[0], Instr::Mov { src: Some(OperandLine::Global { .. }), .. }));

        let a = round_cost(&c, MaterializationPolicy::AlwaysMaterialize, 1);
        let b = round_cost(&c, MaterializationPolicy::AlwaysMaterialize, 4);
        assert_eq!(a, b, "R0 traffic must be round-invariant");
        // base width 1: T0 = 4, T2 = 8, no fold store.
        assert_eq!(a, RoundCost { t0_read_bytes: 4, t2_read_bytes: 8, fold_store_bytes: 0 });
    }

    #[test]
    fn geometric_total_weights_halve_per_round() {
        // Lazy depth-r cost (4·2^r) under geometric 2^{-r} weighting is a
        // constant 4 B per element per round — the key numerical property.
        let l = one_root_layer(vec![read_src(0)], vec![Expr::Source(SourceId(0))], ExprId(0));
        let d = distill(&l, BwdRegime::Ext, &HashMap::new(), None);
        let c = compile_distilled_expect(&d);
        // Force lazy at every round with a high LazyUpTo cap.
        let g = geometric_total(&c, MaterializationPolicy::LazyUpTo(255), 4);
        // T0: Σ_{r=0}^{4} (4·2^r)·2^{-r} = 4·5 = 20.
        assert!((g.t0_read_bytes - 20.0).abs() < 1e-9, "got {}", g.t0_read_bytes);
        // T2 is exactly double T0.
        assert!((g.t2_read_bytes - 40.0).abs() < 1e-9);
        assert_eq!(g.fold_store_bytes, 0.0);
    }

    /// Compile helper — the bare fixtures here are always b16-feasible.
    fn compile_distilled_expect(d: &crate::bwd::distill::DistilledLayer) -> BwdCompiledLayer {
        crate::bwd::compile::compile_distilled(d, 16, None).expect("micro layer compiles at b16")
    }
}
