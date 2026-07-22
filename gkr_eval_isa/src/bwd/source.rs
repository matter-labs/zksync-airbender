//! Bwd descriptor namespace: `BwdSpecial` (`FoldSource`/`VirtualSetup`) + the
//! interning table `BwdSpecialTable`, plus `FoldState`/`MaterializationPolicy`
//! (spec §2.3). Namespace rule: bwd programs' `OperandLine::Special{desc}`
//! indexes ONLY `BwdSpecialTable` — fwd's `SpecialTable`, `peek.rs`
//! validators, and fwd stats are never applied to bwd programs.

use cs::gkr_compiler::dag_ir::{ReadPlace, VirtualSetupKind};

/// Which stored representation a `FoldSource` reads from at a given round.
/// REV2: not carried by `BwdSpecial` (that's structural-only) — this lives in
/// per-run `BwdBindings` (Task 4); kept here as the shared vocabulary type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FoldState {
    /// Read the materialized previous-round buffer (depth-1 fold of it).
    Materialized,
    /// Recompute from original columns: 2^depth reads + fold tree with round
    /// derived_e4. `depth` == current round index (1-based fold count).
    LazyFromOriginals { depth: u8 },
}

/// The pre-distillation identity of a fold origin.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OriginLeaf {
    /// Exactly the payload of `cs::gkr_compiler::dag_ir::SourceKind::Read`.
    Read(ReadPlace),
    VirtualSetup { kind: VirtualSetupKind },
    // REV2: LookupColumn placeholder DELETED — decoder binding is deferred design.
}

impl OriginLeaf {
    /// Whether this origin is a `VirtualSetup` leaf — the single predicate
    /// backing the VS zero-DRAM convention (VS-ABI, Task 11): VS-origin folds
    /// use the O(k) multilinear closed form (compute-only, zero DRAM, always
    /// lazy), never the ordinary Read-origin materialize/lazy machinery. Used
    /// at every site that encodes this convention: `cost::round_cost`'s
    /// short-circuit, `compile::tally_bwd_program`'s traffic gate, and the
    /// `bwd_distill_fixtures` VS-use counter. `pub` (not `pub(crate)`): the
    /// last of those is an external integration test (`tests/`), which only
    /// sees the crate's public surface.
    pub fn is_vs(&self) -> bool {
        matches!(self, OriginLeaf::VirtualSetup { .. })
    }
}

/// A backward-VM special-descriptor payload. STRUCTURAL only — `FoldState`
/// moved to per-run `BwdBindings` (Task 4).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BwdSpecial {
    FoldSource { origin: OriginLeaf },
    /// The typed enum, not a raw device-ABI `u8`.
    VirtualSetup { kind: VirtualSetupKind },
    /// A fragment's summed coefficient recipe value (CS-M5a Task 3): the interp
    /// serves `d.fragments.fragments[fragment].recipe`, a scalar-pure `Σ Π` over
    /// `Constant`/`Challenge` factors, via [`MergedRecipe::evaluate`]. Row- and
    /// role-invariant (no fold, no `bindings.states`). Emitted ONLY into a
    /// compiled layer's CLONED table by the Task-5 fragment lowering — interned
    /// BEYOND `d.specials.len()` — so the distilled `d.specials` (which `bind`
    /// iterates) never holds one.
    ///
    /// [`MergedRecipe::evaluate`]: super::fragment::MergedRecipe::evaluate
    Coefficient { fragment: u32 },
    /// The backward accumulator's initial value (CS-M5a Task 3): the interp
    /// serves `d.fragments.c_init` (the scalar-pure `Σ Π` of the spine's
    /// scalar-pure addends) via [`MergedRecipe::evaluate`]. Same
    /// resolution/emission rules as [`BwdSpecial::Coefficient`].
    ///
    /// [`MergedRecipe::evaluate`]: super::fragment::MergedRecipe::evaluate
    AccInit,
}

/// Interning table for `BwdSpecial`; dense `u16` descriptors assigned from 0
/// in first-seen order. Bwd-only namespace — see module docs.
#[derive(Debug, Clone, Default)]
pub struct BwdSpecialTable {
    descs: Vec<BwdSpecial>,
}

impl BwdSpecialTable {
    /// Interns `s`, returning its dense descriptor index. Identical entries
    /// (by `PartialEq`) dedup to the same index.
    pub fn intern(&mut self, s: BwdSpecial) -> u16 {
        if let Some(i) = self.descs.iter().position(|d| *d == s) {
            return i as u16;
        }
        let i = self.descs.len() as u16;
        self.descs.push(s);
        i
    }

    pub fn get(&self, desc: u16) -> Option<&BwdSpecial> {
        self.descs.get(desc as usize)
    }

    pub fn len(&self) -> usize {
        self.descs.len()
    }
}

/// When a fold's materialized buffer is kept around vs. recomputed lazily
/// from originals (spec §2.3).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MaterializationPolicy {
    AlwaysMaterialize,
    LazyUpTo(u8),
}

#[cfg(test)]
mod tests {
    use super::*;

    fn read_origin(column: usize) -> OriginLeaf {
        OriginLeaf::Read(ReadPlace::BaseLayerMemory { column })
    }

    #[test]
    fn intern_dedups_identical_entries() {
        let mut t = BwdSpecialTable::default();
        let a = t.intern(BwdSpecial::FoldSource { origin: read_origin(3) });
        let b = t.intern(BwdSpecial::FoldSource { origin: read_origin(3) });
        assert_eq!(a, b);
        assert_eq!(t.len(), 1);
    }

    #[test]
    fn intern_distinct_entries_get_distinct_dense_indices() {
        let mut t = BwdSpecialTable::default();
        let a = t.intern(BwdSpecial::FoldSource { origin: read_origin(3) });
        let b = t.intern(BwdSpecial::FoldSource { origin: read_origin(4) });
        let c = t.intern(BwdSpecial::VirtualSetup { kind: VirtualSetupKind::RangeCheck16Bits });
        assert_eq!([a, b, c], [0, 1, 2]);
        assert_eq!(t.len(), 3);
    }

    #[test]
    fn get_out_of_range_is_none() {
        let mut t = BwdSpecialTable::default();
        t.intern(BwdSpecial::VirtualSetup { kind: VirtualSetupKind::RangeCheckTimestamp });
        assert!(t.get(1).is_none());
        assert!(t.get(u16::MAX).is_none());
    }

    #[test]
    fn get_in_range_roundtrips() {
        let mut t = BwdSpecialTable::default();
        let spec = BwdSpecial::VirtualSetup { kind: VirtualSetupKind::InitsAndTeardownsLow };
        let i = t.intern(spec.clone());
        assert_eq!(t.get(i), Some(&spec));
    }

    #[test]
    fn coefficient_and_acc_init_intern_and_dedup() {
        let mut t = BwdSpecialTable::default();
        let acc = t.intern(BwdSpecial::AccInit);
        let acc2 = t.intern(BwdSpecial::AccInit);
        let c0 = t.intern(BwdSpecial::Coefficient { fragment: 0 });
        let c0_again = t.intern(BwdSpecial::Coefficient { fragment: 0 });
        let c1 = t.intern(BwdSpecial::Coefficient { fragment: 1 });
        assert_eq!(acc, acc2, "AccInit dedups");
        assert_eq!(c0, c0_again, "Coefficient dedups by fragment");
        assert_ne!(c0, c1, "distinct fragments are distinct descriptors");
        assert_eq!([acc, c0, c1], [0, 1, 2]);
        assert_eq!(t.len(), 3);
        assert_eq!(t.get(c1), Some(&BwdSpecial::Coefficient { fragment: 1 }));
    }

    #[test]
    fn fold_state_variants_are_distinct() {
        assert_ne!(FoldState::Materialized, FoldState::LazyFromOriginals { depth: 1 });
        assert_ne!(
            FoldState::LazyFromOriginals { depth: 1 },
            FoldState::LazyFromOriginals { depth: 2 }
        );
    }

    #[test]
    fn materialization_policy_is_copy() {
        let p = MaterializationPolicy::LazyUpTo(2);
        let q = p; // Copy, not move
        assert_eq!(p, q);
        assert_eq!(MaterializationPolicy::AlwaysMaterialize, MaterializationPolicy::AlwaysMaterialize);
    }
}
