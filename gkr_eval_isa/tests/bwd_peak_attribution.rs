//! Task 6 (LIGHT) — peak-live composition diagnostic.
//!
//! SP1's streaming (Tasks 1–2) collapses every wide backward L0 to fit `b16` at ZERO
//! traffic cost (no residual). This diagnostic is the coarse follow-on the residual report
//! asked for: it reads out WHAT fills the `b16` placement peak — how many of the peak-live
//! cells are LEAF READS (by origin: witness / cache / virtual-setup / …) versus INTERNAL
//! ARITHMETIC TEMPS (streamed stash/product/accumulator working set, plus distilled interior
//! nodes materialized to a cell) — for the tight/representative wide L0s, above all
//! **unified L0 Ext**, which sits exactly at the `b16` ceiling (`max_live = 16`).
//!
//! It is NOT the full 5-file provenance machinery (attribution.rs / distill provenance /
//! mint-site side-maps): the classification is the LIGHT `OriginKind` from the task brief
//! (an `INTERNAL_BASE` check + a distilled-expr origin lookup). The precise
//! "under-uncached-lookup cone" attribution — which `LookupLeaf` cells a real kernel could
//! instead read from forward-materialized columns — is DEFERRED to SP3.

mod common;

use std::collections::BTreeMap;

use gkr_eval_ir::{Expr, ExprId, ReadPlace, SourceKind};
use gkr_eval_isa::BwdRegime;
use gkr_eval_isa::bwd::compile::compile_distilled_peak;
use gkr_eval_isa::bwd::distill::{distill, DistilledLayer};

/// Fresh internal `ValueId`s are minted from this base in the bwd/fwd lowerer so they never
/// collide with real layer `ExprId`s (`0..layer.exprs.len()`) — `lower.rs:143`. A peak-live
/// value at or above it is a streamed working-set temp with no DAG source.
const INTERNAL_BASE: u32 = 1 << 30;

/// LIGHT origin classification (brief §Classification). No provenance side-map: a coarse
/// `INTERNAL_BASE` split + a distilled-expr origin lookup, nothing finer.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum OriginKind {
    /// `Read` from a `BaseLayer{Witness,Memory}` column — a genuine witness/memory leaf.
    Witness,
    /// `Read` from a `CacheOutput` — a forward-materialized cache column.
    CacheOutput,
    /// Any other `Read` (Setup / Scratch / cross-layer `LayerOutput`).
    LayerRead,
    /// `VirtualSetup` leaf (resolver-computed setup column).
    VirtualSetup,
    /// Inlined lookup-query leaf. NOTE: after distillation `LookupValue` leaves are
    /// rewritten to their `query` cone, so this is expected to be 0 on real fixtures; the
    /// precise under-lookup cone attribution is deferred to SP3.
    LookupLeaf,
    /// `Constant` / `Challenge` leaf.
    ConstOrChallenge,
    /// A distilled interior `Add`/`Mul` node that was materialized to a cell.
    MaterializedNode,
    /// A streamed internal temp (`v.0 >= INTERNAL_BASE`): stash partial / product operand /
    /// reduction accumulator — arithmetic working set, no DAG source.
    InternalTemp,
}

impl OriginKind {
    /// Every enum variant, in report order (source origins first, then temps).
    const ALL: &'static [OriginKind] = &[
        OriginKind::Witness,
        OriginKind::CacheOutput,
        OriginKind::LayerRead,
        OriginKind::VirtualSetup,
        OriginKind::LookupLeaf,
        OriginKind::ConstOrChallenge,
        OriginKind::MaterializedNode,
        OriginKind::InternalTemp,
    ];

    fn label(self) -> &'static str {
        match self {
            OriginKind::Witness => "Witness",
            OriginKind::CacheOutput => "CacheOutput",
            OriginKind::LayerRead => "LayerRead",
            OriginKind::VirtualSetup => "VirtualSetup",
            OriginKind::LookupLeaf => "LookupLeaf",
            OriginKind::ConstOrChallenge => "ConstOrChallenge",
            OriginKind::MaterializedNode => "MaterializedNode",
            OriginKind::InternalTemp => "InternalTemp",
        }
    }

    /// A leaf READ (an origin-backed source), as opposed to an arithmetic temp
    /// (`MaterializedNode` / `InternalTemp`). Drives the leaf-vs-temp headline split.
    fn is_leaf_read(self) -> bool {
        !matches!(self, OriginKind::MaterializedNode | OriginKind::InternalTemp)
    }
}

/// Classify a peak-live `ValueId` (brief §Classification). Total by construction — every
/// value lands in exactly one `OriginKind`, so there is never an "unknown" bucket.
fn classify(d: &DistilledLayer, v: ExprId) -> OriginKind {
    if v.0 >= INTERNAL_BASE {
        return OriginKind::InternalTemp;
    }
    match &d.layer.exprs[v.0 as usize] {
        Expr::Source(sid) => match &d.layer.sources[sid.0 as usize].kind {
            SourceKind::Read { place } => match place {
                ReadPlace::BaseLayerWitness { .. } | ReadPlace::BaseLayerMemory { .. } => {
                    OriginKind::Witness
                }
                ReadPlace::CacheOutput { .. } => OriginKind::CacheOutput,
                ReadPlace::Setup { .. } | ReadPlace::Scratch { .. } | ReadPlace::LayerOutput { .. } => {
                    OriginKind::LayerRead
                }
            },
            SourceKind::VirtualSetup { .. } => OriginKind::VirtualSetup,
            SourceKind::LookupValue { .. } => OriginKind::LookupLeaf,
            SourceKind::Constant { .. } | SourceKind::Challenge { .. } => OriginKind::ConstOrChallenge,
        },
        Expr::Add(_) | Expr::Mul(_) => OriginKind::MaterializedNode,
    }
}

/// Per-category tally: lanes (Σ cell width) and value count.
#[derive(Clone, Copy, Default)]
struct Bucket {
    lanes: usize,
    count: usize,
}

/// Compile `d` at `b16` (streamed) with the peak readout, classify every peak-live value,
/// and return the per-category tally alongside the raw peak facts. Also enforces the three
/// brief invariants: (a) `Σ width == max_live_cells`; (b) every live value is classified
/// (no unknown / no dropped lane); (c) `max_live_cells <= 16`.
fn tally_peak(d: &DistilledLayer) -> (BTreeMap<OriginKind, Bucket>, usize, usize, usize) {
    let (c, peak_instr, live) =
        compile_distilled_peak(d, 16, None).expect("streamed compile at b16");
    let max_live = c.stats.max_live_cells;

    let mut tally: BTreeMap<OriginKind, Bucket> = BTreeMap::new();
    let mut sum_w = 0usize;
    for &(v, w) in &live {
        let b = tally.entry(classify(d, v)).or_default();
        b.lanes += w;
        b.count += 1;
        sum_w += w;
    }

    // (a) the peak-live widths sum EXACTLY to the placement peak.
    assert_eq!(sum_w, max_live, "Σ(peak-live widths) must equal max_live_cells");
    // (b) every live value was classified into exactly one category (no unknown/dropped).
    let classified: usize = tally.values().map(|b| b.count).sum();
    assert_eq!(classified, live.len(), "every peak-live value must be classified exactly once");
    let classified_lanes: usize = tally.values().map(|b| b.lanes).sum();
    assert_eq!(classified_lanes, max_live, "classified lanes must cover the whole peak");
    // (c) the peak fits the b16 ceiling.
    assert!(max_live <= 16, "max_live_cells {max_live} exceeds the b16 ceiling");

    (tally, max_live, peak_instr, live.len())
}

/// Render the peak composition as a small human-readable table (brief §Report): one row per
/// non-empty `OriginKind` (lanes + value count), then the headline leaf-read-vs-temp split.
pub fn report_peak_composition(
    name: &str,
    tally: &BTreeMap<OriginKind, Bucket>,
    max_live: usize,
    peak_instr: usize,
    n_live: usize,
) -> String {
    let mut s = String::new();
    s.push_str(&format!(
        "### {name} — peak-live composition (max_live = {max_live}, peak instr {peak_instr}, {n_live} live values)\n\n"
    ));
    s.push_str("| OriginKind        | lanes | values |\n");
    s.push_str("|-------------------|-------|--------|\n");
    let (mut leaf_lanes, mut temp_lanes) = (0usize, 0usize);
    for &k in OriginKind::ALL {
        let b = tally.get(&k).copied().unwrap_or_default();
        if b.count == 0 {
            continue;
        }
        s.push_str(&format!("| {:<17} | {:>5} | {:>6} |\n", k.label(), b.lanes, b.count));
        if k.is_leaf_read() {
            leaf_lanes += b.lanes;
        } else {
            temp_lanes += b.lanes;
        }
    }
    s.push_str(&format!(
        "\n**Split:** {leaf_lanes} leaf-read lanes + {temp_lanes} arithmetic-temp lanes = {max_live} total.\n"
    ));
    s
}

/// One-line composition summary (e.g. `16 lanes = 4 InternalTemp + 12 Witness`) — lanes per
/// non-empty category, temps first, for the report headline.
fn one_line(tally: &BTreeMap<OriginKind, Bucket>, max_live: usize) -> String {
    let mut parts: Vec<String> = Vec::new();
    // Temps first (they explain the streamed working set), then leaf origins.
    for &k in OriginKind::ALL.iter().rev() {
        if let Some(b) = tally.get(&k) {
            if b.lanes > 0 {
                parts.push(format!("{} {}", b.lanes, k.label()));
            }
        }
    }
    format!("{max_live} lanes = {}", parts.join(" + "))
}

fn distill_ext(name: &str) -> DistilledLayer {
    let (layer, cross) = common::load_layer(name, 0);
    distill(&layer, BwdRegime::Ext, &cross, None)
}

/// The headline layer: unified L0 Ext sits EXACTLY at the b16 ceiling (`max_live = 16`).
/// Its composition is the D2 attribution datum the residual report was waiting on.
#[test]
fn unified_l0_ext_peak_composition() {
    let d = distill_ext("unified_reduced_machine_layout_gkr.json");
    let (tally, max_live, peak_instr, n_live) = tally_peak(&d);
    assert_eq!(max_live, 16, "unified L0 Ext must be exactly at the b16 ceiling");
    println!("{}", report_peak_composition("unified L0 Ext", &tally, max_live, peak_instr, n_live));
    println!("ONE-LINE unified L0 Ext: {}", one_line(&tally, max_live));
}

/// bigint L0 Ext (`max_live = 12`) — a second wide, FMA-streamed representative.
#[test]
fn bigint_l0_ext_peak_composition() {
    let d = distill_ext("bigint_with_extended_control_layout_gkr.json");
    let (tally, max_live, peak_instr, n_live) = tally_peak(&d);
    assert!(max_live <= 16, "max_live {max_live}");
    println!("{}", report_peak_composition("bigint L0 Ext", &tally, max_live, peak_instr, n_live));
    println!("ONE-LINE bigint L0 Ext: {}", one_line(&tally, max_live));
}

/// add_sub L0 Ext (`max_live = 12`) — the third representative wide L0.
#[test]
fn add_sub_l0_ext_peak_composition() {
    let d = distill_ext("add_sub_lui_auipc_mop_layout_gkr.json");
    let (tally, max_live, peak_instr, n_live) = tally_peak(&d);
    assert!(max_live <= 16, "max_live {max_live}");
    println!("{}", report_peak_composition("add_sub L0 Ext", &tally, max_live, peak_instr, n_live));
    println!("ONE-LINE add_sub L0 Ext: {}", one_line(&tally, max_live));
}
