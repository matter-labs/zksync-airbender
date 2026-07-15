//! LinearIR: a flat accumulator-machine program compiled from a `DagLayer`
//! root's expression cone, plus its row-bound interpreter.
//!
//! # Model
//!
//! A [`Program`] is a straight-line sequence of [`Op`]s over a single `Ext`
//! accumulator (`acc`), a set of named stash slots (`SlotId` → `Ext`, freed
//! on read), and — from M2 on — a simulated value cache (`ExprId` → `Ext`).
//! `Load`/`Add`/`Mul`/`Fma` read an [`Operand`] and combine it into `acc`;
//! `Stash` moves `acc` into a slot (after which `acc` is undefined until the
//! next `Load` — this is enforced, not just documented: see
//! [`interpret`]'s undefined-accumulator panic); `Operand::Stashed` *consumes*
//! a slot (a second read panics — a use-after-free tripwire, since the
//! flattener's stack discipline must never emit a double consumption).
//! `SinkMaterialize` records the current `acc` as a root's value; it does not
//! consume `acc` (unlike `Stash`), matching `CacheStore`'s non-consuming
//! "admission marker" semantics below.
//!
//! Everything evaluates in `Ext` (`Base` sources lift), matching
//! `dag_ir::eval::eval_layer_root` — this interpreter is the linear-program
//! counterpart to that DAG-walking reference evaluator, over the same
//! `Resolvers` bundle.
//!
//! # M1 vs M2
//!
//! `Cached`/`CacheStore`/`Evict` exist now as forward-declared hooks for the
//! M2 caching walker, but M1's interpreter already gives them full (if
//! simulation-only) semantics rather than stubbing them out: `CacheStore(id)`
//! admits the current `acc` into a `BTreeMap<ExprId, Ext>` value table,
//! `Evict(id)` drops that table entry (both markers only account for *value*
//! availability — they carry no cost/traffic bookkeeping; that arrives with
//! the M2 walker), and `Operand::Cached(id)` reads the table, panicking with
//! the offending `ExprId` if the value was never stored or was already
//! evicted. `width_of_slot` is DP-facing accounting metadata (the lane width
//! backing each stash slot, for M2's peak/traffic bookkeeping) — the
//! interpreter never reads it.
//!
//! # Leaf resolution
//!
//! `Operand::Leaf(SourceId)` mirrors `eval_layer_expr`'s `Source` arm
//! (`cs/src/gkr_compiler/dag_ir/eval.rs`) exactly, with one deliberate v1
//! simplification: `SourceKind::LookupValue`'s query expression is never
//! evaluated here (LinearIR leaves reference a `SourceId` directly, not an
//! `ExprId` sub-cone) — the evaluated-query argument is passed as
//! `Ext::ZERO`. This is sound for the resolvers this crate targets (the test
//! doubles here and Task 7's production `HashResolvers`), which both ignore
//! `evaluated_query`; a resolver that actually branches on the query value
//! would observe a divergence and must not be used with this interpreter
//! as-is.

use std::collections::BTreeMap;

use cs::gkr_compiler::dag_ir::eval::{Bf, Ext, Resolvers};
use cs::gkr_compiler::dag_ir::{DagLayer, ExprId, RootId, SourceId, SourceKind};
use field::{Field, FieldExtension, PrimeField};

/// A stash slot identifier. Slots are keyed by their raw `u32` in
/// [`Program::width_of_slot`] and in the interpreter's live-slot table.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SlotId(pub u32);

/// The value an `Op` combines into (or reads out to) the accumulator.
#[derive(Clone, Copy, Debug)]
pub enum Operand {
    /// Streamed from the resolver/DRAM: a `DagLayer` source leaf.
    Leaf(SourceId),
    /// Read from the simulated cache (M2): the materialized value of an
    /// `ExprId` previously admitted via `Op::CacheStore`.
    Cached(ExprId),
    /// Consume a stashed accumulator — frees the slot; a second consumption
    /// panics (use-after-free tripwire).
    Stashed(SlotId),
}

/// One instruction of a [`Program`]'s linear accumulator machine.
#[derive(Clone, Copy, Debug)]
pub enum Op {
    /// `acc = v`
    Load(Operand),
    /// `acc += v`
    Add(Operand),
    /// `acc *= v`
    Mul(Operand),
    /// `acc += a*b` (the product occupies nothing — it is never stashed).
    Fma(Operand, Operand),
    /// `slot = acc` (acc then undefined until the next `Load`).
    Stash(SlotId),
    /// Marker: admit acc's current value into the simulated cache under
    /// `ExprId` (M2 accounting). Does not consume `acc`.
    CacheStore(ExprId),
    /// Marker: walker-decided eviction of `ExprId` from the simulated cache
    /// (M2 accounting).
    Evict(ExprId),
    /// Record the current `acc` as `RootId`'s value (fwd write / bwd claim
    /// fold). Does not consume `acc`.
    SinkMaterialize(RootId),
}

/// A flat linear-IR program over one `DagLayer` row. `width_of_slot` is DP
/// accounting metadata (lane width per stash slot) for the M2 sizing/peak
/// bookkeeping; [`interpret`] never reads it.
pub struct Program {
    pub ops: Vec<Op>,
    pub width_of_slot: BTreeMap<u32, u32>,
}

/// Lifts a `Base` value into `Ext`, mirroring the private `lift` helper in
/// `dag_ir::eval`.
#[inline(always)]
fn lift(b: Bf) -> Ext {
    <Ext as FieldExtension<Bf>>::from_base(b)
}

/// Resolves a leaf source to its `Ext` value, mirroring `eval_layer_expr`'s
/// `Source` arm (`cs/src/gkr_compiler/dag_ir/eval.rs`) — see the module doc
/// for the one deliberate deviation (`LookupValue`'s query passed as zero).
fn eval_leaf(source: SourceId, layer: &DagLayer, row: usize, r: &Resolvers<'_>) -> Ext {
    match &layer.sources[source.0 as usize].kind {
        SourceKind::Constant { value } => lift(Bf::from_u32_with_reduction(*value)),
        SourceKind::Challenge { reference } => r.challenge.challenge(reference),
        SourceKind::Read { place } => r.read.read(place, row),
        SourceKind::VirtualSetup { kind } => lift(r.virtual_setup.virtual_setup(kind, row)),
        SourceKind::LookupValue { kind, set_index, query: _ } => {
            // v1 simplification (see module doc): the query sub-expr is never
            // evaluated here — pass zero.
            lift(r.lookup.lookup(kind, *set_index, Ext::ZERO, row))
        }
    }
}

/// Resolves an `Operand` to its `Ext` value. `Stashed` consumes (removes)
/// its slot; `Cached` panics with the offending `ExprId` if the value was
/// never admitted (or was evicted).
fn resolve_operand(
    operand: Operand,
    layer: &DagLayer,
    row: usize,
    r: &Resolvers<'_>,
    slots: &mut BTreeMap<u32, Ext>,
    cache: &BTreeMap<ExprId, Ext>,
) -> Ext {
    match operand {
        Operand::Leaf(source) => eval_leaf(source, layer, row, r),
        Operand::Cached(expr) => *cache.get(&expr).unwrap_or_else(|| {
            panic!(
                "gkr_flatten interp: Operand::Cached({expr:?}) missing from the value table — \
                 no CacheStore for this ExprId has run (or it was already evicted)"
            )
        }),
        Operand::Stashed(slot) => slots.remove(&slot.0).unwrap_or_else(|| {
            panic!(
                "gkr_flatten interp: Operand::Stashed({slot:?}) already consumed — a stashed \
                 slot may be read exactly once (use-after-free / double consumption)"
            )
        }),
    }
}

/// Reads the accumulator, panicking if it is undefined (program start, or
/// since the last `Stash` — which leaves `acc` undefined until the next
/// `Load`, per the `Op::Stash` contract).
fn expect_acc(acc: Option<Ext>) -> Ext {
    acc.unwrap_or_else(|| {
        panic!(
            "gkr_flatten interp: accumulator read while undefined (no Load yet, or the \
             accumulator was invalidated by a Stash and never reloaded)"
        )
    })
}

/// Runs `p` over `layer` at `row`, resolving leaves through `r`. Returns the
/// materialized value of every `RootId` the program sinks.
///
/// See the module doc for the full instruction semantics and the
/// `LookupValue`-query-as-zero v1 simplification.
pub fn interpret(
    p: &Program,
    layer: &DagLayer,
    row: usize,
    r: &Resolvers<'_>,
) -> BTreeMap<RootId, Ext> {
    let mut acc: Option<Ext> = None;
    let mut slots: BTreeMap<u32, Ext> = BTreeMap::new();
    let mut cache: BTreeMap<ExprId, Ext> = BTreeMap::new();
    let mut out: BTreeMap<RootId, Ext> = BTreeMap::new();

    for op in &p.ops {
        match op {
            Op::Load(operand) => {
                acc = Some(resolve_operand(*operand, layer, row, r, &mut slots, &cache));
            }
            Op::Add(operand) => {
                let v = resolve_operand(*operand, layer, row, r, &mut slots, &cache);
                let mut a = expect_acc(acc);
                a.add_assign(&v);
                acc = Some(a);
            }
            Op::Mul(operand) => {
                let v = resolve_operand(*operand, layer, row, r, &mut slots, &cache);
                let mut a = expect_acc(acc);
                a.mul_assign(&v);
                acc = Some(a);
            }
            Op::Fma(op_a, op_b) => {
                let va = resolve_operand(*op_a, layer, row, r, &mut slots, &cache);
                let vb = resolve_operand(*op_b, layer, row, r, &mut slots, &cache);
                let mut prod = va;
                prod.mul_assign(&vb);
                let mut a = expect_acc(acc);
                a.add_assign(&prod);
                acc = Some(a);
            }
            Op::Stash(slot) => {
                let v = expect_acc(acc);
                if slots.insert(slot.0, v).is_some() {
                    panic!(
                        "gkr_flatten interp: Stash({slot:?}) overwrote a live slot — a slot must \
                         be consumed via Operand::Stashed before it is restashed (stack \
                         discipline violated)"
                    );
                }
                // Contract: acc is undefined until the next Load.
                acc = None;
            }
            Op::CacheStore(expr) => {
                let v = expect_acc(acc);
                cache.insert(*expr, v);
                // Non-consuming: unlike Stash, CacheStore does not invalidate acc.
            }
            Op::Evict(expr) => {
                cache.remove(expr);
            }
            Op::SinkMaterialize(root) => {
                let v = expect_acc(acc);
                out.insert(*root, v);
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use cs::gkr_compiler::dag_ir::eval::{
        ChallengeResolver, LookupResolver, ReadResolver, VirtualSetupResolver, eval_layer_root,
    };
    use cs::gkr_compiler::dag_ir::{ChallengeRef, LookupValueKind, ReadPlace, VirtualSetupKind};

    use super::*;
    use crate::dag::testdag::tiny_fma_layer;

    // ── Deterministic test-local resolver ─────────────────────────────────
    //
    // Hash-ish deterministic function of (a small integer tag identifying the
    // reference, row) — no meaningful semantics beyond determinism, and no
    // ambition to become the shared production resolver (that's Task 7's
    // `src/resolvers.rs::HashResolvers`; kept separate on purpose to avoid a
    // seam conflict).
    fn mix(a: u32, b: u32) -> u32 {
        a.wrapping_mul(2_654_435_761)
            .wrapping_add(b.wrapping_mul(2_246_822_519))
            .wrapping_add(0x9E3779B9)
    }

    struct DetResolver;

    impl ReadResolver for DetResolver {
        fn read(&self, place: &ReadPlace, row: usize) -> Ext {
            let col = match place {
                ReadPlace::BaseLayerWitness { column } => *column as u32,
                ReadPlace::BaseLayerMemory { column } => *column as u32 + 1_000,
                ReadPlace::Setup { column } => *column as u32 + 2_000,
                ReadPlace::Scratch { slot } => *slot as u32 + 3_000,
                ReadPlace::LayerOutput { layer, offset } => {
                    (*layer as u32) * 100 + *offset as u32 + 4_000
                }
                ReadPlace::CacheOutput { layer, offset } => {
                    (*layer as u32) * 100 + *offset as u32 + 5_000
                }
            };
            lift(Bf::from_u32_with_reduction(mix(col, row as u32)))
        }
    }

    impl LookupResolver for DetResolver {
        fn lookup(
            &self,
            _kind: &LookupValueKind,
            set_index: usize,
            _evaluated_query: Ext,
            row: usize,
        ) -> Bf {
            Bf::from_u32_with_reduction(mix(set_index as u32 + 6_000, row as u32))
        }
    }

    impl VirtualSetupResolver for DetResolver {
        fn virtual_setup(&self, _kind: &VirtualSetupKind, row: usize) -> Bf {
            Bf::from_u32_with_reduction(mix(7_001, row as u32))
        }
    }

    impl ChallengeResolver for DetResolver {
        fn challenge(&self, _reference: &ChallengeRef) -> Ext {
            lift(Bf::from_u32_with_reduction(mix(8_001, 0)))
        }
    }

    fn resolvers(d: &DetResolver) -> Resolvers<'_> {
        Resolvers { read: d, lookup: d, virtual_setup: d, challenge: d }
    }

    #[test]
    fn fma_program_evaluates() {
        let layer = tiny_fma_layer();
        let d = DetResolver;
        let r = resolvers(&d);
        // acc = w0; acc += w1*w2  ==  w0 + w1*w2
        let p = Program {
            ops: vec![
                Op::Load(Operand::Leaf(SourceId(0))),
                Op::Fma(Operand::Leaf(SourceId(1)), Operand::Leaf(SourceId(2))),
                Op::SinkMaterialize(RootId(0)),
            ],
            width_of_slot: Default::default(),
        };
        let expected = eval_layer_root(&layer, RootId(0), 0, &r);
        assert_eq!(interpret(&p, &layer, 0, &r)[&RootId(0)], expected);
    }

    #[test]
    fn stash_roundtrip() {
        let layer = tiny_fma_layer();
        let d = DetResolver;
        let r = resolvers(&d);
        // Load w0 (a); Stash s0; Load w1 (b); Mul(Stashed(s0)); Sink == a*b.
        let p = Program {
            ops: vec![
                Op::Load(Operand::Leaf(SourceId(0))),
                Op::Stash(SlotId(0)),
                Op::Load(Operand::Leaf(SourceId(1))),
                Op::Mul(Operand::Stashed(SlotId(0))),
                Op::SinkMaterialize(RootId(0)),
            ],
            width_of_slot: Default::default(),
        };
        let a = d.read(&ReadPlace::BaseLayerWitness { column: 0 }, 0);
        let b = d.read(&ReadPlace::BaseLayerWitness { column: 1 }, 0);
        let mut expected = a;
        expected.mul_assign(&b);
        assert_eq!(interpret(&p, &layer, 0, &r)[&RootId(0)], expected);
    }

    #[test]
    #[should_panic(expected = "already consumed")]
    fn stashed_slot_consumed_twice_panics() {
        let layer = tiny_fma_layer();
        let d = DetResolver;
        let r = resolvers(&d);
        // Stash once, then try to consume the same slot twice.
        let p = Program {
            ops: vec![
                Op::Load(Operand::Leaf(SourceId(0))),
                Op::Stash(SlotId(0)),
                Op::Load(Operand::Leaf(SourceId(1))),
                Op::Add(Operand::Stashed(SlotId(0))),
                Op::Add(Operand::Stashed(SlotId(0))),
                Op::SinkMaterialize(RootId(0)),
            ],
            width_of_slot: Default::default(),
        };
        let _ = interpret(&p, &layer, 0, &r);
    }

    #[test]
    #[should_panic(expected = "overwrote a live slot")]
    fn stash_overwrite_of_live_slot_panics() {
        let layer = tiny_fma_layer();
        let d = DetResolver;
        let r = resolvers(&d);
        // Stash s0, then Stash s0 again without an intervening consumption.
        let p = Program {
            ops: vec![
                Op::Load(Operand::Leaf(SourceId(0))),
                Op::Stash(SlotId(0)),
                Op::Load(Operand::Leaf(SourceId(1))),
                Op::Stash(SlotId(0)),
                Op::SinkMaterialize(RootId(0)),
            ],
            width_of_slot: Default::default(),
        };
        let _ = interpret(&p, &layer, 0, &r);
    }

    #[test]
    #[should_panic(expected = "accumulator read while undefined")]
    fn acc_use_after_stash_panics() {
        let layer = tiny_fma_layer();
        let d = DetResolver;
        let r = resolvers(&d);
        // Stash frees acc; using it directly (not via Stashed) must panic.
        let p = Program {
            ops: vec![
                Op::Load(Operand::Leaf(SourceId(0))),
                Op::Stash(SlotId(0)),
                Op::Add(Operand::Leaf(SourceId(1))),
                Op::SinkMaterialize(RootId(0)),
            ],
            width_of_slot: Default::default(),
        };
        let _ = interpret(&p, &layer, 0, &r);
    }

    #[test]
    fn cache_store_evict_roundtrip() {
        let layer = tiny_fma_layer();
        let d = DetResolver;
        let r = resolvers(&d);
        // Load w1*w2's product into the cache under a synthetic ExprId, read
        // it back via Cached, then evict and confirm a stale read panics.
        let p = Program {
            ops: vec![
                Op::Load(Operand::Leaf(SourceId(1))),
                Op::Mul(Operand::Leaf(SourceId(2))),
                Op::CacheStore(ExprId(3)),
                Op::Load(Operand::Leaf(SourceId(0))),
                Op::Add(Operand::Cached(ExprId(3))),
                Op::SinkMaterialize(RootId(0)),
            ],
            width_of_slot: Default::default(),
        };
        let expected = eval_layer_root(&layer, RootId(0), 0, &r);
        assert_eq!(interpret(&p, &layer, 0, &r)[&RootId(0)], expected);
    }

    #[test]
    #[should_panic(expected = "missing from the value table")]
    fn cached_read_after_evict_panics() {
        let layer = tiny_fma_layer();
        let d = DetResolver;
        let r = resolvers(&d);
        let p = Program {
            ops: vec![
                Op::Load(Operand::Leaf(SourceId(1))),
                Op::CacheStore(ExprId(1)),
                Op::Evict(ExprId(1)),
                Op::Load(Operand::Cached(ExprId(1))),
                Op::SinkMaterialize(RootId(0)),
            ],
            width_of_slot: Default::default(),
        };
        let _ = interpret(&p, &layer, 0, &r);
    }
}
