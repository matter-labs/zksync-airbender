//! Genome + decode (spec §5): a fixed-length keep-gene encoding over a
//! layer's site domain (`SiteTable`) that a search — see `crate::search` —
//! mutates and scores, decoded (`decode`) into a `GenomeOracle` the
//! walker (`crate::walk::flatten_budgeted`) consumes exactly like any other
//! `Oracle` — genome search never touches the walker itself.
//!
//! Encoding: `root_keys[i]` is a tie-breaking key for root `i` — `root_order`
//! sorts root indices by `(root_keys[i], i)`, reordering VISITATION only
//! (`RootId`s keep their original `DagLayer::roots` indices, same contract as
//! every other `Oracle`). `keep[locus]` is a per-site "worth" gene: a site is
//! offered to the walker (`Some(keep[locus] as u32)`) iff it is
//! cache-admissible AND its gene strictly exceeds `threshold`, else refused
//! (`None`) — the decode rule (spec §5).
//!
//! The two endpoint constructors are the M2 gates' regression net:
//! `ceiling` (every gene 0, threshold 0) refuses every site — `0 > 0` is
//! false — so decoding it must reproduce `NeutralOracle` byte-for-byte at any
//! budget; `all_admit` (every gene 1, threshold 0) admits every admissible
//! site, so decoding it at an unbounded budget must reach
//! `analysis::SizingReport::floor`. `random` draws search seed material from
//! a `SplitMix64` stream.

use cs::gkr_compiler::dag_ir::{DagLayer, RootId};

use crate::oracle::{Oracle, SitePath, SiteTable};

/// Deterministic, seeded PRNG (Steele/Lea/Flood's splitmix64 output
/// function — same shape as `resolvers.rs`'s `splitmix64`/`SplitMix64Hasher`,
/// reimplemented here as a standalone counter rather than a `Hasher` since
/// genome search needs a plain `next_u64`/`below` stream, not byte-folding).
pub struct SplitMix64(pub u64);

impl SplitMix64 {
    /// Advances the counter by the golden-ratio increment and applies the
    /// splitmix64 avalanche to the new state.
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A value in `0..n`. Modulo bias is irrelevant for search purposes (not
    /// used anywhere requiring cryptographic uniformity).
    pub fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }
}

/// A fixed-length keep-gene encoding over one layer's site domain (spec §5).
/// `root_keys` and `keep` are addressed by plain index — `root_keys[i]` for
/// root `i` (`0..n_roots`), `keep[locus]` for the site at `locus` in the
/// `SiteTable` this genome was built against. Genomes from different tables
/// (or root counts) are not interchangeable — `decode`/`root_order` size
/// their lookups off the SAME table/layer the genome names.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Genome {
    pub root_keys: Vec<u32>,
    pub keep: Vec<u16>,
    pub threshold: u16,
}

impl Genome {
    /// All-refuse endpoint (spec §5 M2 gate): every keep gene is `0`,
    /// threshold `0` — `0 > 0` is false, so decoding this refuses every site
    /// regardless of admissibility. Decoding it must reproduce
    /// `NeutralOracle` byte-for-byte at any budget.
    pub fn ceiling(table: &SiteTable, n_roots: usize) -> Genome {
        Genome { root_keys: (0..n_roots as u32).collect(), keep: vec![0; table.len()], threshold: 0 }
    }

    /// All-admit endpoint (spec §5 M2 gate): every keep gene is `1`,
    /// threshold `0` — `1 > 0` admits every ADMISSIBLE site. Decoding this at
    /// an unbounded budget must reach the sizing floor
    /// (`analysis::SizingReport::floor`).
    pub fn all_admit(table: &SiteTable, n_roots: usize) -> Genome {
        Genome { root_keys: (0..n_roots as u32).collect(), keep: vec![1; table.len()], threshold: 0 }
    }

    /// A uniformly random genome (search seed material, M2): random root
    /// tie-break keys and per-site keep genes drawn from `rng`, threshold
    /// fixed at the midpoint (`u16::MAX / 2`).
    pub fn random(table: &SiteTable, n_roots: usize, rng: &mut SplitMix64) -> Genome {
        Genome {
            root_keys: (0..n_roots).map(|_| rng.next_u64() as u32).collect(),
            keep: (0..table.len()).map(|_| rng.next_u64() as u16).collect(),
            threshold: u16::MAX / 2,
        }
    }
}

/// The `Oracle` a `Genome` decodes into (spec §5): borrows the `SiteTable` it
/// was decoded against, so `keep_priority`'s `locus` lookup runs against the
/// SAME table every walk over this oracle observes (the coverage invariant
/// its `debug_assert` checks). `root_keys` and the per-locus `priority` (the
/// decode rule applied once, up front — not recomputed per `keep_priority`
/// call) are private: this type is only ever produced by `decode` and
/// consumed as an `Oracle`.
pub struct GenomeOracle<'t> {
    table: &'t SiteTable,
    root_keys: Vec<u32>,
    priority: Vec<Option<u32>>,
}

/// Decodes `g` against `table` (spec §5's rule): locus `i` maps to
/// `Some(g.keep[i] as u32)` iff `table.sites[i].admissible && g.keep[i] >
/// g.threshold`, else `None`.
pub fn decode<'t>(g: &Genome, table: &'t SiteTable) -> GenomeOracle<'t> {
    assert_eq!(
        g.keep.len(),
        table.len(),
        "gkr_flatten: genome/table length mismatch — stale table or foreign genome"
    );
    let priority = table
        .sites
        .iter()
        .enumerate()
        .map(|(i, s)| (s.admissible && g.keep[i] > g.threshold).then_some(g.keep[i] as u32))
        .collect();
    GenomeOracle { table, root_keys: g.root_keys.clone(), priority }
}

impl<'t> Oracle for GenomeOracle<'t> {
    /// Sorts root indices by `(root_keys[i], i)` — a random, tie-broken
    /// visitation order (M2 search lever). Reorders VISITATION only:
    /// `RootId`s keep their original `layer.roots` indices.
    fn root_order(&self, layer: &DagLayer) -> Vec<RootId> {
        assert_eq!(
            self.root_keys.len(),
            layer.roots.len(),
            "gkr_flatten: GenomeOracle decoded with {} root keys but `layer` has {} roots — \
             genome/layer mismatch",
            self.root_keys.len(),
            layer.roots.len()
        );
        let mut order: Vec<RootId> = (0..layer.roots.len() as u32).map(RootId).collect();
        order.sort_by_key(|r| (self.root_keys[r.0 as usize], r.0));
        order
    }

    fn keep_priority(&self, site: &SitePath) -> Option<u32> {
        let locus = self.table.locus(site);
        debug_assert!(
            locus.is_some(),
            "gkr_flatten: coverage invariant violated — walked site {site:?} missing from the \
             neutral-enumerated table"
        );
        locus.and_then(|l| self.priority[l as usize])
    }
}

#[cfg(test)]
mod tests {
    use cs::gkr_compiler::dag_ir::{ExprId, RootId};

    use super::*;
    use crate::dag::LayerView;
    use crate::oracle::{NeutralOracle, SiteTable};
    use crate::walk::{flatten, flatten_budgeted};

    #[test]
    fn splitmix64_is_deterministic_and_bounded() {
        let mut a = SplitMix64(42);
        let mut b = SplitMix64(42);
        for _ in 0..8 {
            assert_eq!(a.next_u64(), b.next_u64(), "same seed must reproduce the same stream");
        }
        let mut c = SplitMix64(43);
        assert_ne!(a.next_u64(), c.next_u64(), "different seeds should (almost surely) diverge");

        let mut rng = SplitMix64(1);
        for _ in 0..200 {
            assert!(rng.below(7) < 7, "below(n) must stay in 0..n");
        }
    }

    #[test]
    fn ceiling_genome_is_byte_identical_to_neutral() {
        let (dag, cross) = crate::fixtures::load_circuit("add_sub_lui_auipc_mop_layout_gkr.json");
        let v = LayerView::new(&dag.layers[0], &cross, None);
        let table = SiteTable::enumerate(&v);
        let g = Genome::ceiling(&table, dag.layers[0].roots.len());
        let o = decode(&g, &table);
        let a = flatten_budgeted(&v, &o, Some(16));
        let b = flatten(&v, &NeutralOracle);
        assert_eq!(a.program, b.program);
        assert_eq!(a.stats, b.stats);
    }

    #[test]
    fn all_admit_unbounded_reaches_floor() {
        let (dag, cross) = crate::fixtures::load_circuit("add_sub_lui_auipc_mop_layout_gkr.json");
        let v = LayerView::new(&dag.layers[0], &cross, None);
        let roots: Vec<ExprId> = dag.layers[0].roots.iter().map(|r| r.expr).collect();
        let report = crate::analysis::size_layer(&v, &roots);
        let table = SiteTable::enumerate(&v);
        let g = Genome::all_admit(&table, dag.layers[0].roots.len());
        let out = flatten_budgeted(&v, &decode(&g, &table), None);
        assert_eq!(out.stats.traffic, report.floor);
    }

    #[test]
    fn same_genome_same_program() {
        let (dag, cross) = crate::fixtures::load_circuit("add_sub_lui_auipc_mop_layout_gkr.json");
        let v = LayerView::new(&dag.layers[0], &cross, None);
        let table = SiteTable::enumerate(&v);
        let mut rng = SplitMix64(42);
        let g = Genome::random(&table, dag.layers[0].roots.len(), &mut rng);
        let a = flatten_budgeted(&v, &decode(&g, &table), Some(12));
        let b = flatten_budgeted(&v, &decode(&g, &table), Some(12));
        assert_eq!(a.program, b.program);
        assert_eq!(a.stats, b.stats);
    }

    #[test]
    fn random_genomes_stay_in_bracket() {
        let (dag, cross) = crate::fixtures::load_circuit("add_sub_lui_auipc_mop_layout_gkr.json");
        let v = LayerView::new(&dag.layers[0], &cross, None);
        let roots: Vec<ExprId> = dag.layers[0].roots.iter().map(|r| r.expr).collect();
        let report = crate::analysis::size_layer(&v, &roots);
        let table = SiteTable::enumerate(&v);
        let n = dag.layers[0].roots.len();
        let ceiling = flatten(&v, &NeutralOracle).stats.traffic;
        let mut rng = SplitMix64(7);
        for _ in 0..20 {
            let g = Genome::random(&table, n, &mut rng);
            for budget in [Some(report.peak), Some(report.peak + 2), Some(16), None] {
                let out = flatten_budgeted(&v, &decode(&g, &table), budget);
                assert!(out.stats.traffic >= report.floor, "below floor");
                assert!(out.stats.traffic <= ceiling, "above ceiling");
                assert!(out.stats.peak <= report.peak, "stash peak above model");
            }
        }
    }

    #[test]
    fn root_order_decodes_by_key_then_index() {
        let layer = crate::dag::testdag::shared_diamond();
        let cross = std::collections::HashMap::new();
        let v = LayerView::new(&layer, &cross, None);
        let table = SiteTable::enumerate(&v);
        let mut g = Genome::ceiling(&table, layer.roots.len());
        // Two roots: give root 1 the smaller key -> visited first.
        g.root_keys = vec![10, 5];
        let o = decode(&g, &table);
        assert_eq!(o.root_order(&layer), vec![RootId(1), RootId(0)]);
    }
}
