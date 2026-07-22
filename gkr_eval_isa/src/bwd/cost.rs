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
//!   * a `Materialized` fold reads one Ext buffer value = `EXT_BYTES` (16 B)
//!     regardless of the origin's field (the folded buffer is always Ext);
//!   * a `LazyFromOriginals { depth: d }` fold recomputes from `2^d` originals
//!     at the ORIGIN's own width: `origin_width_cells·4·2^d` B. Most origins
//!     are base columns (`origin_width_cells == 1`), but a same-layer cache
//!     fence (Task 1-2) can fold a `Read(CacheOutput)` leaf whose place is
//!     Ext-valued (`DistilledLayer.cross_fields`), so `origin_width_cells ==
//!     4` for those — a fenced Ext cache leaf costs `16·2^d`, not `4·2^d`;
//!   * an `R0` `Global` backing reads one native-width value = `width·4` B.
//!
//! Fold STORES (writing a round's folded Ext buffer for the next round to read)
//! are tallied separately at `EXT_BYTES` per distinct materialized fold buffer.
//!
//! # VS-ABI constraint (Task 11) + closed-form fold (Task 7)
//!
//! In the `Ext` regime a `VirtualSetup` origin leaf is rewritten to a
//! `FoldSource`, but its folded buffer cannot be materialized (the `Bf`
//! virtual-setup resolver cannot carry an Ext folded buffer). So VS-origin folds
//! always bind `LazyFromOriginals { depth: round }` for ALL policies — the same
//! forced-lazy convention the runtime binder [`super::distill::bind`] enforces.
//!
//! Task 7 makes that lazy state *cheap*: VS polys are multilinear by
//! construction, so a depth-`d` fold is the same `O(k)` multilinear closed form
//! with the bound coordinates replaced by derived_e4
//! ([`cs::gkr_compiler::dag_ir::VirtualSetupResolver::virtual_setup_fold`]).
//! The device implements that closed form, so a VS-origin fold moves **zero
//! DRAM** — it is compute-only. This model therefore charges VS-origin folds 0
//! read bytes and 0 store bytes at every round, superseding the old
//! `origin_width·4·2^d` recompute-from-originals estimate.

use std::collections::{BTreeSet, HashMap};

use super::compile::BwdCompiledLayer;
use super::interp::Role;
use super::source::{BwdSpecial, FoldState, MaterializationPolicy, OriginLeaf};
use crate::fwd::isa::{Instr, OperandField, OperandLine};
use cs::gkr_compiler::dag_ir::{FieldKind, ReadPlace};

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
/// `origin_width_cells` is the ORIGIN's own field width (1 = base, 4 = Ext —
/// e.g. a fenced `Read(CacheOutput)` leaf); it only affects the lazy branch —
/// a materialized fold buffer is always Ext-width regardless of its origin.
#[inline]
pub fn fold_element_bytes(state: FoldState, origin_width_cells: usize) -> usize {
    match state {
        FoldState::Materialized => EXT_BYTES,
        FoldState::LazyFromOriginals { depth } => {
            origin_width_cells * CELL_BYTES * (1usize << depth)
        }
    }
}

/// DRAM read bytes for one fold-source operand occurrence at `role`/`state`,
/// for an origin of `origin_width_cells` (see [`fold_element_bytes`]).
#[inline]
pub fn fold_read_bytes(role: Role, state: FoldState, origin_width_cells: usize) -> usize {
    role_read_count(role) * fold_element_bytes(state, origin_width_cells)
}

/// The origin's own field width in cells: a `Read` origin is Ext-width (4)
/// iff `cross_fields` records its place as `FieldKind::Ext` (fenced same-layer
/// cache leaves, Task 1-2, and cross-layer cache reads); otherwise it is an
/// ordinary base column (1). A `VirtualSetup` origin returns 1 for shape, but
/// `round_cost` no longer consults it: VS folds are the zero-DRAM closed form
/// (Task 7) and short-circuit before any width is applied.
#[inline]
pub fn origin_width_cells(
    origin: &OriginLeaf,
    cross_fields: &HashMap<ReadPlace, FieldKind>,
) -> usize {
    match origin {
        OriginLeaf::VirtualSetup { .. } => 1,
        OriginLeaf::Read(place) => match cross_fields.get(place) {
            Some(FieldKind::Ext) => EXT_CELLS,
            _ => 1,
        },
    }
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
pub(crate) fn for_each_operand(instr: &Instr, mut f: impl FnMut(&OperandLine, OperandField)) {
    match instr {
        Instr::Mov {
            src: Some(op),
            field,
            ..
        } => f(op, *field),
        Instr::Mov { src: None, .. } => {}
        Instr::Add {
            operands, field, ..
        }
        | Instr::Mul {
            operands, field, ..
        } => {
            for op in operands {
                f(op, *field);
            }
        }
        Instr::Fma {
            pairs,
            field_lhs,
            field_rhs,
            ..
        } => {
            for (l, r) in pairs {
                f(l, *field_lhs);
                f(r, *field_rhs);
            }
        }
    }
}

/// Tally the per-row DRAM byte cost of `c` at `(policy, round)`. `cross_fields`
/// is the distilled layer's `DistilledLayer::cross_fields` — it resolves a
/// `Read`-origin fold source's own field width (Task 3): most origins are base
/// columns, but a fenced same-layer cache leaf (`Read(CacheOutput)`) is
/// Ext-valued and must cost lazy rounds at Ext width, not base width.
///
/// Reads are tallied per FoldSource/Global **operand occurrence** (an uncached
/// value used N times folds N times — the interpreter re-resolves each use;
/// admitted sites read a smem cell instead and drop out of this tally). Stores
/// are tallied per **distinct** materialized Read-origin fold buffer (always
/// Ext-width — a materialized buffer's width doesn't depend on its origin).
pub fn round_cost(
    c: &BwdCompiledLayer,
    policy: MaterializationPolicy,
    round: u8,
    cross_fields: &HashMap<ReadPlace, FieldKind>,
) -> RoundCost {
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
                    // VS-origin folds use the O(k) multilinear closed form
                    // (Task 7): the device evaluates them from a handful of
                    // derived_e4, moving ZERO DRAM — no read bytes, no store.
                    // Every other (Read) origin gathers originals / a folded
                    // buffer at its own field width, exactly as before. This
                    // short-circuit IS the cost model's side of the VS-ABI
                    // forced-lazy convention (Task 11) — it MIRRORS the
                    // runtime binder `distill::bind` exactly (a VS origin
                    // never reaches `read_fold_state`, so there is no
                    // separate "effective fold state" to compute).
                    if origin.is_vs() {
                        // compute-only closed form: contributes nothing to DRAM.
                    } else {
                        let state = read_fold_state(policy, round);
                        let width = origin_width_cells(origin, cross_fields);
                        cost.t0_read_bytes += fold_read_bytes(Role::T0, state, width);
                        cost.t2_read_bytes += fold_read_bytes(Role::T2, state, width);
                        if state == FoldState::Materialized {
                            materialized_descs.insert(*desc);
                        }
                    }
                }
                // R0 VirtualSetup specials are procedurally generated (no DRAM);
                // None is unreachable for a well-formed compile.
                _ => {}
            },
            // Smem cells / Ldc consts+derived_e4 / inline literals: no DRAM.
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
    cross_fields: &HashMap<ReadPlace, FieldKind>,
) -> GeoCost {
    let mut g = GeoCost::default();
    for r in 0..=max_round {
        let w = 1.0f64 / (1u64 << r) as f64;
        let rc = round_cost(c, policy, r, cross_fields);
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
        BatchingOrder, BwdRegime, ClaimInfo, DagLayer, Expr, ExprId, FieldKind, Root, RootGroup,
        RootId, RootOrigin, RootSlot, SinkInfo, SinkKind, SourceId, SourceInfo, SourceKind,
        VirtualSetupKind,
    };
    use std::collections::{BTreeMap, HashMap};

    // ── (1) hand-computed byte model: role × policy × depth ──────────────────

    #[test]
    fn fold_element_bytes_by_state() {
        // Materialized: one Ext buffer element = 16 B, regardless of origin width.
        assert_eq!(fold_element_bytes(FoldState::Materialized, 1), 16);
        assert_eq!(fold_element_bytes(FoldState::Materialized, 4), 16);
        // Lazy depth d, base-width origin (1 cell): 2^d originals at 4 B.
        assert_eq!(
            fold_element_bytes(FoldState::LazyFromOriginals { depth: 0 }, 1),
            4
        );
        assert_eq!(
            fold_element_bytes(FoldState::LazyFromOriginals { depth: 1 }, 1),
            8
        );
        assert_eq!(
            fold_element_bytes(FoldState::LazyFromOriginals { depth: 2 }, 1),
            16
        );
        assert_eq!(
            fold_element_bytes(FoldState::LazyFromOriginals { depth: 3 }, 1),
            32
        );
        assert_eq!(
            fold_element_bytes(FoldState::LazyFromOriginals { depth: 4 }, 1),
            64
        );
        // Lazy depth d, Ext-width origin (4 cells, e.g. a fenced cache leaf):
        // 2^d originals at 16 B (4x the base-width cost at every depth).
        assert_eq!(
            fold_element_bytes(FoldState::LazyFromOriginals { depth: 0 }, 4),
            16
        );
        assert_eq!(
            fold_element_bytes(FoldState::LazyFromOriginals { depth: 1 }, 4),
            32
        );
        assert_eq!(
            fold_element_bytes(FoldState::LazyFromOriginals { depth: 2 }, 4),
            64
        );
    }

    #[test]
    fn fold_read_bytes_by_role_and_state() {
        // T0 = 1 element, T2 = 2 elements (base-width origin).
        assert_eq!(fold_read_bytes(Role::T0, FoldState::Materialized, 1), 16);
        assert_eq!(fold_read_bytes(Role::T2, FoldState::Materialized, 1), 32);
        assert_eq!(
            fold_read_bytes(Role::T0, FoldState::LazyFromOriginals { depth: 0 }, 1),
            4
        );
        assert_eq!(
            fold_read_bytes(Role::T2, FoldState::LazyFromOriginals { depth: 0 }, 1),
            8
        );
        assert_eq!(
            fold_read_bytes(Role::T0, FoldState::LazyFromOriginals { depth: 1 }, 1),
            8
        );
        assert_eq!(
            fold_read_bytes(Role::T2, FoldState::LazyFromOriginals { depth: 1 }, 1),
            16
        );
        // Crossover: lazy depth 2 costs exactly a materialized read (base width).
        assert_eq!(
            fold_read_bytes(Role::T0, FoldState::LazyFromOriginals { depth: 2 }, 1),
            fold_read_bytes(Role::T0, FoldState::Materialized, 1)
        );
        // depth 3 lazy is strictly worse than materialized (base width).
        assert!(
            fold_read_bytes(Role::T0, FoldState::LazyFromOriginals { depth: 3 }, 1)
                > fold_read_bytes(Role::T0, FoldState::Materialized, 1)
        );
        // Ext-width origin (fenced cache leaf): 4x the base-width read cost at
        // every depth, and the crossover point shifts (already worse at depth 0).
        assert_eq!(
            fold_read_bytes(Role::T0, FoldState::LazyFromOriginals { depth: 0 }, 4),
            16
        );
        assert_eq!(
            fold_read_bytes(Role::T2, FoldState::LazyFromOriginals { depth: 0 }, 4),
            32
        );
        assert!(
            fold_read_bytes(Role::T0, FoldState::LazyFromOriginals { depth: 0 }, 4)
                >= fold_read_bytes(Role::T0, FoldState::Materialized, 4)
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
            batching: BatchingOrder {
                roots: vec![RootId(0)],
            },
            resolutions: BTreeMap::new(),
        }
    }

    #[test]
    fn round_cost_single_ext_fold_source() {
        // One bare Read leaf → one Ext FoldSource occurrence.
        let l = one_root_layer(
            vec![read_src(0)],
            vec![Expr::Source(SourceId(0))],
            ExprId(0),
        );
        let d = distill(&l, BwdRegime::Ext, &HashMap::new(), None);
        let c = compile_distilled_expect(&d);
        assert_eq!(c.stats_ext.fold_uses, 1, "exactly one fold occurrence");

        // Round 0: Lazy{0} → T0 = 4, T2 = 8, no store.
        let r0 = round_cost(
            &c,
            MaterializationPolicy::AlwaysMaterialize,
            0,
            &d.cross_fields,
        );
        assert_eq!(
            r0,
            RoundCost {
                t0_read_bytes: 4,
                t2_read_bytes: 8,
                fold_store_bytes: 0
            }
        );

        // Round 2 AlwaysMaterialize → Materialized: T0 = 16, T2 = 32, one store 16.
        let r2 = round_cost(
            &c,
            MaterializationPolicy::AlwaysMaterialize,
            2,
            &d.cross_fields,
        );
        assert_eq!(
            r2,
            RoundCost {
                t0_read_bytes: 16,
                t2_read_bytes: 32,
                fold_store_bytes: 16
            }
        );

        // Round 2 LazyUpTo(2) → Lazy{2}: T0 = 16, T2 = 32, no store.
        let l2 = round_cost(&c, MaterializationPolicy::LazyUpTo(2), 2, &d.cross_fields);
        assert_eq!(
            l2,
            RoundCost {
                t0_read_bytes: 16,
                t2_read_bytes: 32,
                fold_store_bytes: 0
            }
        );

        // Round 3 LazyUpTo(2) → Materialized (past k): store reappears.
        let l3 = round_cost(&c, MaterializationPolicy::LazyUpTo(2), 3, &d.cross_fields);
        assert_eq!(l3.fold_store_bytes, 16);
    }

    #[test]
    fn round_cost_vs_origin_is_always_lazy() {
        // One VirtualSetup leaf → Ext FoldSource with a VS origin. It always
        // binds the forced-lazy state (`distill::bind`, VS-ABI) — never a
        // materialized buffer. Task 7: the lazy fold is the O(k) multilinear
        // closed form the device computes on-chip, so it moves ZERO DRAM at
        // every round/policy — no read bytes and no store bytes.
        let l = one_root_layer(
            vec![SourceInfo {
                kind: SourceKind::VirtualSetup {
                    kind: VirtualSetupKind::RangeCheck16Bits,
                },
            }],
            vec![Expr::Source(SourceId(0))],
            ExprId(0),
        );
        let d = distill(&l, BwdRegime::Ext, &HashMap::new(), None);
        let c = compile_distilled_expect(&d);
        assert_eq!(c.stats_ext.fold_uses, 1);

        for policy in [
            MaterializationPolicy::AlwaysMaterialize,
            MaterializationPolicy::LazyUpTo(2),
        ] {
            for round in [0u8, 1, 3, 5] {
                let r = round_cost(&c, policy, round, &d.cross_fields);
                assert_eq!(
                    r,
                    RoundCost::default(),
                    "VS-origin fold is compute-only (closed form): 0 DRAM at {policy:?} round {round}"
                );
            }
        }
    }

    /// A fenced same-layer Ext cache leaf (`c = w0 + w1`, sink `Cache{layer:0,
    /// offset:2}`, field Ext) consumed alongside a plain base Read leaf (`w1`)
    /// by one claim root `Mul(c, w1)`. After distillation `w0` is gone (only
    /// reachable through the fenced cache cone); `c` survives as a
    /// `Read(CacheOutput)` fold leaf and `w1` survives as a plain base leaf —
    /// exactly the origin-width split this task must cost correctly.
    fn cache_and_base_layer() -> DagLayer {
        DagLayer {
            sources: vec![read_src(0), read_src(1)],
            exprs: vec![
                Expr::Source(SourceId(0)),             // 0 = w0
                Expr::Source(SourceId(1)),             // 1 = w1
                Expr::Add(vec![ExprId(0), ExprId(1)]), // 2 = c (cache root)
                Expr::Mul(vec![ExprId(2), ExprId(1)]), // 3 = c * w1 (claim root)
            ],
            roots: vec![
                Root {
                    expr: ExprId(2),
                    materialize: Some(SinkInfo {
                        kind: SinkKind::Cache {
                            layer: 0,
                            offset: 2,
                        },
                        field: FieldKind::Ext,
                    }),
                    claim: None,
                },
                claim_only_root(ExprId(3)),
            ],
            batching: BatchingOrder {
                roots: vec![RootId(1)],
            },
            resolutions: BTreeMap::new(),
        }
    }

    #[test]
    fn round_cost_charges_cache_origin_at_ext_width() {
        // Fenced Ext cache leaf must cost 16*2^d per T0 element (Ext-width
        // origin), while the plain base Read leaf alongside it still costs
        // 4*2^d (base-width origin) — the cost model must be origin-width-
        // aware, not blanket base-width.
        let l = cache_and_base_layer();
        let d = distill(&l, BwdRegime::Ext, &HashMap::new(), None);
        let c = compile_distilled_expect(&d);
        assert_eq!(
            c.stats_ext.fold_uses, 2,
            "cache leaf + base leaf, one use each"
        );

        for depth in [0u8, 1, 2, 3] {
            let r = round_cost(
                &c,
                MaterializationPolicy::LazyUpTo(255),
                depth,
                &d.cross_fields,
            );
            // T0 = 1 element per leaf: cache leaf 16*2^d + base leaf 4*2^d.
            let expected_t0 = 16usize * (1usize << depth) + 4usize * (1usize << depth);
            assert_eq!(
                r.t0_read_bytes, expected_t0,
                "depth {depth}: expected cache(16*2^d) + base(4*2^d) = {expected_t0}, got {}",
                r.t0_read_bytes
            );
        }
    }

    #[test]
    fn round_cost_r0_global_backing_is_round_flat() {
        // R0 regime: the Read leaf stays a Global backing (base width 1), so per
        // round the cost is role-only and round-invariant.
        let l = one_root_layer(
            vec![read_src(0)],
            vec![Expr::Source(SourceId(0))],
            ExprId(0),
        );
        let d = distill(&l, BwdRegime::R0, &HashMap::new(), None);
        let c = compile_distilled_expect(&d);
        assert_eq!(c.stats_ext.fold_uses, 0, "R0 has no fold sources");
        assert!(matches!(
            &c.program.instrs[0],
            Instr::Mov {
                src: Some(OperandLine::Global { .. }),
                ..
            }
        ));

        let a = round_cost(
            &c,
            MaterializationPolicy::AlwaysMaterialize,
            1,
            &d.cross_fields,
        );
        let b = round_cost(
            &c,
            MaterializationPolicy::AlwaysMaterialize,
            4,
            &d.cross_fields,
        );
        assert_eq!(a, b, "R0 traffic must be round-invariant");
        // base width 1: T0 = 4, T2 = 8, no fold store.
        assert_eq!(
            a,
            RoundCost {
                t0_read_bytes: 4,
                t2_read_bytes: 8,
                fold_store_bytes: 0
            }
        );
    }

    #[test]
    fn geometric_total_weights_halve_per_round() {
        // Lazy depth-r cost (4·2^r) under geometric 2^{-r} weighting is a
        // constant 4 B per element per round — the key numerical property.
        let l = one_root_layer(
            vec![read_src(0)],
            vec![Expr::Source(SourceId(0))],
            ExprId(0),
        );
        let d = distill(&l, BwdRegime::Ext, &HashMap::new(), None);
        let c = compile_distilled_expect(&d);
        // Force lazy at every round with a high LazyUpTo cap.
        let g = geometric_total(&c, MaterializationPolicy::LazyUpTo(255), 4, &d.cross_fields);
        // T0: Σ_{r=0}^{4} (4·2^r)·2^{-r} = 4·5 = 20.
        assert!(
            (g.t0_read_bytes - 20.0).abs() < 1e-9,
            "got {}",
            g.t0_read_bytes
        );
        // T2 is exactly double T0.
        assert!((g.t2_read_bytes - 40.0).abs() < 1e-9);
        assert_eq!(g.fold_store_bytes, 0.0);
    }

    /// Compile helper — the bare fixtures here are always b16-feasible.
    fn compile_distilled_expect(d: &crate::bwd::distill::DistilledLayer) -> BwdCompiledLayer {
        crate::bwd::compile::compile_distilled(d, 16, None).expect("micro layer compiles at b16")
    }
}
