//! Structure-aware backward-cache search diagnostics for the heavy L0 circuits.
//!
//! The report tests are ignored and CPU-only; the stable-key permutation gate
//! runs normally:
//!
//! - `stable_intervals_and_gene_mapping_l0` assigns every distilled value/site a
//!   deterministic semantic fingerprint that is independent of re-interned
//!   `ExprId`s. It reports how much the raw distilled site ordering moves under
//!   unit reversal, then emits the highest-value inter-unit cache intervals.
//! - `production_stable_site_keys_survive_unit_permutations` is a non-ignored
//!   regression gate for the compiler's exact canonical-provenance mapping.
//! - `proxy_exact_score_correlation_l0` samples deterministic, semantically-keyed
//!   policies and compares the search proxy (`global + fold_traffic`) with the
//!   policy/round-aware geometric DRAM byte model.
//! - `structured_seed_equal_eval_heavy_l0` compares legacy and structure-aware
//!   initial populations at the same exact-compiler evaluation budget.
//!
//! Environment knobs:
//! - `GKR_BWD_INTERVAL_LIMIT` (default 40, `0` = all intervals);
//! - `GKR_BWD_CORR_SAMPLES` (default 12 feasible candidates per circuit);
//! - `GKR_BWD_SEED_AB_EVALS` (default 4 exact evaluations per seed mode).
//! - `GKR_BWD_CURVE_SEEDS` (default 3 deterministic seeds);
//! - `GKR_BWD_CURVE_EVALS` (default `4,8,16,40`).
//!
//! Marginal interval costs are the DRAM reads required to recompute the value's
//! complete cone with NO cached descendant. They are therefore exact for a Read
//! and an upper bound / initialization weight for an intermediate. A stateful
//! replay must re-price intermediates after parent/descendant cache decisions.

mod common;

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet, HashSet};

use common::load_layer;
use gkr_eval_ir::{DagLayer, Expr, ExprId, FieldKind, RootId, SourceKind, join, source_field};
use gkr_eval_isa::bwd::compile::{BwdCompiledLayer, compile_distilled, spine_terms};
use gkr_eval_isa::bwd::cost::{
    fold_read_bytes, geometric_total, origin_width_cells, r0_read_bytes, read_fold_state,
};
use gkr_eval_isa::bwd::distill::{
    DistilledLayer, distill, distilled_site_domain, stable_distilled_site_domain,
};
use gkr_eval_isa::bwd::interp::Role;
use gkr_eval_isa::bwd::search::{
    BwdOrderMutation, BwdSearchConfig, BwdSeedStrategy, search_bwd_layer,
};
use gkr_eval_isa::bwd::source::{BwdSpecial, MaterializationPolicy};
use gkr_eval_isa::fwd::compile::SiteDecisions;
use gkr_eval_isa::fwd::error::CompileError;
use gkr_eval_isa::{BwdRegime, SiteConsumer, SiteKey};
use rayon::prelude::*;

const HEAVY: &[&str] = &[
    "bigint_with_extended_control_layout_gkr.json",
    "keccak_special5_layout_gkr.json",
];

const MAX_ROUND: u8 = 4;
const HEADROOM_LANES: usize = 48; // 12 Ext buckets above the no-decisions floor.
const POLICIES: &[(&str, MaterializationPolicy)] = &[
    ("AlwaysMat", MaterializationPolicy::AlwaysMaterialize),
    ("Lazy<=2", MaterializationPolicy::LazyUpTo(2)),
    ("Lazy<=4", MaterializationPolicy::LazyUpTo(4)),
];

// ── Order-independent semantic identity ─────────────────────────────────────

/// Deterministic 128-bit structural fingerprint. Add/Mul children are sorted by
/// their own fingerprints, so an order-driven `ExprId` renumbering cannot move
/// the semantic identity. This is diagnostic provenance, not a persisted ABI.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct SemanticId(u128);

impl std::fmt::Display for SemanticId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:032x}", self.0)
    }
}

const FNV64_PRIME: u64 = 0x0000_0100_0000_01b3;
const FNV64_OFFSET_A: u64 = 0xcbf2_9ce4_8422_2325;
const FNV64_OFFSET_B: u64 = 0x8422_2325_cbf2_9ce4;

fn fnv64(mut h: u64, bytes: &[u8]) -> u64 {
    for &b in bytes {
        h ^= b as u64;
        h = h.wrapping_mul(FNV64_PRIME);
    }
    h
}

fn semantic_atom(tag: u8, payload: &str) -> SemanticId {
    let mut a = fnv64(FNV64_OFFSET_A, &[tag]);
    let mut b = fnv64(FNV64_OFFSET_B, &[tag ^ 0xa5]);
    a = fnv64(a, payload.as_bytes());
    b = fnv64(b, payload.as_bytes());
    SemanticId(((a as u128) << 64) | b as u128)
}

fn semantic_node(tag: u8, mut children: Vec<SemanticId>) -> SemanticId {
    children.sort_unstable();
    let mut a = fnv64(FNV64_OFFSET_A, &[tag]);
    let mut b = fnv64(FNV64_OFFSET_B, &[tag ^ 0x5a]);
    a = fnv64(a, &(children.len() as u64).to_le_bytes());
    b = fnv64(b, &(children.len() as u64).to_le_bytes());
    for child in children {
        a = fnv64(a, &child.0.to_le_bytes());
        b = fnv64(b, &child.0.rotate_left(37).to_le_bytes());
    }
    SemanticId(((a as u128) << 64) | b as u128)
}

fn semantic_id(layer: &DagLayer, id: ExprId, memo: &mut [Option<SemanticId>]) -> SemanticId {
    if let Some(id) = memo[id.0 as usize] {
        return id;
    }
    let out = match &layer.exprs[id.0 as usize] {
        Expr::Add(children) => semantic_node(
            1,
            children
                .iter()
                .map(|&child| semantic_id(layer, child, memo))
                .collect(),
        ),
        Expr::Mul(children) => semantic_node(
            2,
            children
                .iter()
                .map(|&child| semantic_id(layer, child, memo))
                .collect(),
        ),
        Expr::Source(source_id) => {
            let kind = &layer.sources[source_id.0 as usize].kind;
            match kind {
                // A query is a semantic edge even though it is not an Expr child.
                SourceKind::LookupValue {
                    kind,
                    set_index,
                    query,
                } => semantic_node(
                    8,
                    vec![
                        semantic_atom(9, &format!("{kind:?}/{set_index}")),
                        semantic_id(layer, *query, memo),
                    ],
                ),
                SourceKind::Read { place } => semantic_atom(3, &format!("{place:?}")),
                SourceKind::Constant { value } => semantic_atom(4, &value.to_string()),
                SourceKind::Challenge { reference } => semantic_atom(5, &format!("{reference:?}")),
                SourceKind::VirtualSetup { kind } => semantic_atom(6, &format!("{kind:?}")),
            }
        }
    };
    memo[id.0 as usize] = Some(out);
    out
}

fn semantic_ids(layer: &DagLayer) -> Vec<SemanticId> {
    let mut memo = vec![None; layer.exprs.len()];
    (0..layer.exprs.len())
        .map(|i| semantic_id(layer, ExprId(i as u32), &mut memo))
        .collect()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum StableConsumer {
    RootOutput,
    Expr {
        expr: SemanticId,
        /// Distinguishes repeated equal operands without depending on the raw
        /// input index, which can move when commutative children are re-interned.
        duplicate_ordinal: u32,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct StableSiteKey {
    consumer: StableConsumer,
    value: SemanticId,
}

fn duplicate_ordinal(layer: &DagLayer, ids: &[SemanticId], site: &SiteKey) -> u32 {
    let SiteConsumer::Expr { expr, input_index } = site.consumer else {
        return 0;
    };
    let target = ids[site.value.0 as usize];
    match &layer.exprs[expr.0 as usize] {
        Expr::Add(children) | Expr::Mul(children) => children
            .iter()
            .take(input_index as usize + 1)
            .filter(|child| ids[child.0 as usize] == target)
            .count()
            .saturating_sub(1) as u32,
        Expr::Source(_) => 0,
    }
}

fn stable_site_key(layer: &DagLayer, ids: &[SemanticId], site: &SiteKey) -> StableSiteKey {
    let consumer = match site.consumer {
        SiteConsumer::RootOutput => StableConsumer::RootOutput,
        SiteConsumer::Expr { expr, .. } => StableConsumer::Expr {
            expr: ids[expr.0 as usize],
            duplicate_ordinal: duplicate_ordinal(layer, ids, site),
        },
    };
    StableSiteKey {
        consumer,
        value: ids[site.value.0 as usize],
    }
}

/// Current `BTreeSet<SiteKey>` order paired with the intended semantic identity.
fn stable_sites(d: &DistilledLayer) -> Vec<(SiteKey, StableSiteKey)> {
    let ids = semantic_ids(&d.layer);
    distilled_site_domain(d)
        .into_iter()
        .map(|site| {
            let stable = stable_site_key(&d.layer, &ids, &site);
            (site, stable)
        })
        .collect()
}

fn stable_site_hash(site: StableSiteKey) -> u64 {
    let (tag, consumer, ordinal) = match site.consumer {
        StableConsumer::RootOutput => (0u64, 0u128, 0u64),
        StableConsumer::Expr {
            expr,
            duplicate_ordinal,
        } => (1, expr.0, duplicate_ordinal as u64),
    };
    let mut h = FNV64_OFFSET_A;
    h = fnv64(h, &tag.to_le_bytes());
    h = fnv64(h, &consumer.to_le_bytes());
    h = fnv64(h, &ordinal.to_le_bytes());
    fnv64(h, &site.value.0.to_le_bytes())
}

// ── Width + uncached-cone marginal DRAM cost ────────────────────────────────

fn expr_field(d: &DistilledLayer, id: ExprId, memo: &mut [Option<FieldKind>]) -> FieldKind {
    if let Some(field) = memo[id.0 as usize] {
        return field;
    }
    if let Some(&field) = d.field_overrides.get(&id) {
        memo[id.0 as usize] = Some(field);
        return field;
    }
    let field = match &d.layer.exprs[id.0 as usize] {
        Expr::Source(source_id) => {
            let kind = &d.layer.sources[source_id.0 as usize].kind;
            source_field(kind).unwrap_or_else(|place| {
                *d.cross_fields
                    .get(&place)
                    .unwrap_or_else(|| panic!("missing cross-layer field for {place:?}"))
            })
        }
        Expr::Add(children) | Expr::Mul(children) => {
            children.iter().fold(FieldKind::Base, |acc, &child| {
                join(acc, expr_field(d, child, memo))
            })
        }
    };
    memo[id.0 as usize] = Some(field);
    field
}

fn width_lanes(d: &DistilledLayer, id: ExprId, memo: &mut [Option<FieldKind>]) -> usize {
    match expr_field(d, id, memo) {
        FieldKind::Base => 1,
        FieldKind::Ext => 4,
    }
}

#[derive(Clone, Copy, Debug, Default)]
struct MarginalCost {
    proxy_cells: usize,
    geo_read_bytes: [f64; 3],
}

impl std::ops::AddAssign for MarginalCost {
    fn add_assign(&mut self, rhs: Self) {
        self.proxy_cells += rhs.proxy_cells;
        for (dst, src) in self.geo_read_bytes.iter_mut().zip(rhs.geo_read_bytes) {
            *dst += src;
        }
    }
}

fn source_marginal(
    d: &DistilledLayer,
    id: ExprId,
    field_memo: &mut [Option<FieldKind>],
) -> MarginalCost {
    let mut out = MarginalCost::default();
    match d.regime {
        BwdRegime::R0 => {
            let Expr::Source(source_id) = &d.layer.exprs[id.0 as usize] else {
                unreachable!()
            };
            if matches!(
                d.layer.sources[source_id.0 as usize].kind,
                SourceKind::Read { .. }
            ) {
                let width = width_lanes(d, id, field_memo);
                out.proxy_cells = width;
                let per_row = r0_read_bytes(Role::T0, width) + r0_read_bytes(Role::T2, width);
                let geo_weight: f64 = (0..=MAX_ROUND).map(|r| 1.0 / (1u64 << r) as f64).sum();
                out.geo_read_bytes.fill(per_row as f64 * geo_weight);
            }
        }
        BwdRegime::Ext => {
            let Some(&desc) = d.leaf_descs.get(&id) else {
                return out;
            };
            let Some(BwdSpecial::FoldSource { origin }) = d.specials.get(desc) else {
                return out;
            };
            if origin.is_vs() {
                return out;
            }
            out.proxy_cells = 4;
            let origin_width = origin_width_cells(origin, &d.cross_fields);
            for (pi, (_, policy)) in POLICIES.iter().enumerate() {
                for round in 0..=MAX_ROUND {
                    let state = read_fold_state(*policy, round);
                    let bytes = fold_read_bytes(Role::T0, state, origin_width)
                        + fold_read_bytes(Role::T2, state, origin_width);
                    out.geo_read_bytes[pi] += bytes as f64 / (1u64 << round) as f64;
                }
            }
        }
    }
    out
}

fn cone_marginal(
    d: &DistilledLayer,
    id: ExprId,
    memo: &mut [Option<MarginalCost>],
    field_memo: &mut [Option<FieldKind>],
) -> MarginalCost {
    if let Some(cost) = memo[id.0 as usize] {
        return cost;
    }
    let cost = match &d.layer.exprs[id.0 as usize] {
        Expr::Source(_) => source_marginal(d, id, field_memo),
        Expr::Add(children) | Expr::Mul(children) => {
            let mut total = MarginalCost::default();
            for &child in children {
                total += cone_marginal(d, child, memo, field_memo);
            }
            total
        }
    };
    memo[id.0 as usize] = Some(cost);
    cost
}

fn node_class(layer: &DagLayer, id: ExprId) -> &'static str {
    match &layer.exprs[id.0 as usize] {
        Expr::Add(_) | Expr::Mul(_) => "INTERMEDIATE",
        Expr::Source(source_id) => match layer.sources[source_id.0 as usize].kind {
            SourceKind::Read { .. } => "Read",
            SourceKind::Constant { .. } => "Constant",
            SourceKind::Challenge { .. } => "Challenge",
            SourceKind::VirtualSetup { .. } => "VirtualSetup",
            SourceKind::LookupValue { .. } => "LookupValue",
        },
    }
}

#[derive(Clone, Debug)]
struct IntervalRow {
    value: SemanticId,
    class: &'static str,
    width_lanes: usize,
    from_root: RootId,
    to_root: RootId,
    from_pos: usize,
    to_pos: usize,
    consumer_count: usize,
    marginal: MarginalCost,
}

fn interval_rows(d: &DistilledLayer, permutation: &[usize]) -> Vec<IntervalRow> {
    let terms = spine_terms(d);
    let term_roots: Vec<RootId> = permutation
        .iter()
        .flat_map(|&unit| d.unit_order[unit].iter().copied())
        .collect();
    assert_eq!(
        terms.len(),
        term_roots.len(),
        "one stable canonical root per spine term"
    );

    let ids = semantic_ids(&d.layer);
    let domain_values: BTreeSet<SemanticId> = distilled_site_domain(d)
        .into_iter()
        .map(|site| ids[site.value.0 as usize])
        .collect();
    let mut representative: BTreeMap<SemanticId, ExprId> = BTreeMap::new();
    let mut consumers: BTreeMap<SemanticId, Vec<(usize, RootId)>> = BTreeMap::new();

    for (position, (&term, &root)) in terms.iter().zip(&term_roots).enumerate() {
        let mut seen_exprs = HashSet::new();
        let mut seen_values = BTreeSet::new();
        let mut work = vec![term];
        while let Some(id) = work.pop() {
            if !seen_exprs.insert(id) {
                continue;
            }
            let stable = ids[id.0 as usize];
            if domain_values.contains(&stable) && seen_values.insert(stable) {
                representative.entry(stable).or_insert(id);
                consumers.entry(stable).or_default().push((position, root));
            }
            match &d.layer.exprs[id.0 as usize] {
                Expr::Add(children) | Expr::Mul(children) => work.extend(children.iter().copied()),
                Expr::Source(source_id) => {
                    if let SourceKind::LookupValue { query, .. } =
                        d.layer.sources[source_id.0 as usize].kind
                    {
                        work.push(query);
                    }
                }
            }
        }
    }

    let mut marginal_memo = vec![None; d.layer.exprs.len()];
    let mut field_memo = vec![None; d.layer.exprs.len()];
    let mut rows = Vec::new();
    for (value, uses) in consumers {
        if uses.len() < 2 {
            continue;
        }
        let id = representative[&value];
        let marginal = cone_marginal(d, id, &mut marginal_memo, &mut field_memo);
        let width_lanes = width_lanes(d, id, &mut field_memo);
        let class = node_class(&d.layer, id);
        for pair in uses.windows(2) {
            let (from_pos, from_root) = pair[0];
            let (to_pos, to_root) = pair[1];
            rows.push(IntervalRow {
                value,
                class,
                width_lanes,
                from_root,
                to_root,
                from_pos,
                to_pos,
                consumer_count: uses.len(),
                marginal,
            });
        }
    }
    rows
}

// ── Fast structural report ──────────────────────────────────────────────────

#[test]
fn production_stable_site_keys_survive_unit_permutations() {
    for &name in HEAVY {
        let (layer, cross) = load_layer(name, 0);
        for regime in [BwdRegime::R0, BwdRegime::Ext] {
            let natural = distill(&layer, regime, &cross, None);
            let natural_domain = stable_distilled_site_domain(&natural);
            assert_eq!(natural_domain.len(), distilled_site_domain(&natural).len());
            let expected: Vec<_> = natural_domain.into_keys().collect();

            for seed in 1..=5 {
                let permutation = shuffled_permutation(natural.unit_order.len(), seed);
                let candidate = distill(&layer, regime, &cross, Some(&permutation));
                let candidate_domain = stable_distilled_site_domain(&candidate);
                assert_eq!(
                    candidate_domain.len(),
                    distilled_site_domain(&candidate).len(),
                    "{name} {regime:?} seed {seed}: stable keys must be collision-free"
                );
                assert_eq!(
                    candidate_domain.into_keys().collect::<Vec<_>>(),
                    expected,
                    "{name} {regime:?} seed {seed}: cache genes changed semantic sites"
                );
            }
        }
    }
}

#[test]
#[ignore = "diagnostic: run with --ignored --nocapture"]
fn stable_intervals_and_gene_mapping_l0() {
    let limit = std::env::var("GKR_BWD_INTERVAL_LIMIT")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(40);

    println!("\n# Stable semantic cache intervals + gene-mapping audit (heavy L0, Ext)");
    println!(
        "# marginal costs = full uncached cone; intermediate costs are conditional upper bounds"
    );
    println!("# interval limit = {limit} (0 means all)\n");

    for &name in HEAVY {
        let stem = name.trim_end_matches("_layout_gkr.json");
        let (layer, cross) = load_layer(name, 0);
        let natural = distill(&layer, BwdRegime::Ext, &cross, None);
        assert!(!natural.skipped_decoder, "{stem} L0 must be decoder-free");
        let n_units = natural.unit_order.len();
        let reverse_perm: Vec<usize> = (0..n_units).rev().collect();
        let reversed = distill(&layer, BwdRegime::Ext, &cross, Some(&reverse_perm));

        let natural_sites = stable_sites(&natural);
        let reversed_sites = stable_sites(&reversed);
        let natural_set: BTreeSet<StableSiteKey> =
            natural_sites.iter().map(|(_, key)| *key).collect();
        let reversed_set: BTreeSet<StableSiteKey> =
            reversed_sites.iter().map(|(_, key)| *key).collect();
        let same_position = natural_sites
            .iter()
            .map(|(_, key)| key)
            .zip(reversed_sites.iter().map(|(_, key)| key))
            .filter(|(a, b)| a == b)
            .count();
        let semantic_collisions = natural_sites.len().saturating_sub(natural_set.len());

        println!("## {stem}");
        println!(
            "mapping: sites={} semantic_set_equal={} semantic_collisions={} same_raw_position={}/{} ({:.1}%)",
            natural_sites.len(),
            natural_set == reversed_set,
            semantic_collisions,
            same_position,
            natural_sites.len(),
            100.0 * same_position as f64 / natural_sites.len().max(1) as f64,
        );
        println!(
            "mapping interpretation: semantic_set_equal=true with low same_raw_position shows why cache genes require the production canonical-provenance translation"
        );

        let natural_perm: Vec<usize> = (0..n_units).collect();
        let mut intervals = interval_rows(&natural, &natural_perm);
        let pairwise_values: BTreeSet<SemanticId> = intervals
            .iter()
            .filter(|row| row.consumer_count == 2)
            .map(|row| row.value)
            .collect();
        let hub_values: BTreeSet<SemanticId> = intervals
            .iter()
            .filter(|row| row.consumer_count > 2)
            .map(|row| row.value)
            .collect();
        intervals.sort_by(|a, b| {
            b.marginal.geo_read_bytes[1]
                .total_cmp(&a.marginal.geo_read_bytes[1])
                .then_with(|| (a.to_pos - a.from_pos).cmp(&(b.to_pos - b.from_pos)))
                .then_with(|| a.value.cmp(&b.value))
        });
        println!(
            "intervals={} pairwise_values={} hub_values={} (natural order)",
            intervals.len(),
            pairwise_values.len(),
            hub_values.len(),
        );
        println!(
            "| value semantic id | class | lanes | from root@pos | to root@pos | gap | consumers | proxy cells | geo AlwaysMat B | geo Lazy<=2 B | geo Lazy<=4 B |"
        );
        println!("|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|");
        let take = if limit == 0 {
            intervals.len()
        } else {
            limit.min(intervals.len())
        };
        for row in intervals.iter().take(take) {
            println!(
                "| {} | {} | {} | {}@{} | {}@{} | {} | {} | {} | {:.1} | {:.1} | {:.1} |",
                row.value,
                row.class,
                row.width_lanes,
                row.from_root.0,
                row.from_pos,
                row.to_root.0,
                row.to_pos,
                row.to_pos - row.from_pos,
                row.consumer_count,
                row.marginal.proxy_cells,
                row.marginal.geo_read_bytes[0],
                row.marginal.geo_read_bytes[1],
                row.marginal.geo_read_bytes[2],
            );
        }
        println!();
    }
}

// ── Compile-in-loop proxy/exact correlation ─────────────────────────────────

struct SeedRng(u64);

impl SeedRng {
    fn new(seed: u64) -> Self {
        Self(seed ^ 0x9e37_79b9_7f4a_7c15)
    }

    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }
}

fn shuffled_permutation(n: usize, seed: u64) -> Vec<usize> {
    let mut out: Vec<usize> = (0..n).collect();
    if seed == 0 {
        return out;
    }
    if seed == 1 {
        out.reverse();
        return out;
    }
    let mut rng = SeedRng::new(seed);
    for i in (1..out.len()).rev() {
        let j = (rng.next() as usize) % (i + 1);
        out.swap(i, j);
    }
    out
}

fn semantic_priority(site: StableSiteKey, seed: u64) -> f64 {
    let mut h = stable_site_hash(site) ^ seed.wrapping_mul(0x9e37_79b9_7f4a_7c15);
    // SplitMix64 finalizer.
    h = (h ^ (h >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    h = (h ^ (h >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    h ^= h >> 31;
    let unit = (h >> 11) as f64 * (1.0 / ((1u64 << 53) as f64));
    unit * 2.0 - 1.0
}

fn semantic_decisions(d: &DistilledLayer, seed: u64) -> SiteDecisions {
    let ids = semantic_ids(&d.layer);
    SiteDecisions::new(distilled_site_domain(d).into_iter().map(|site| {
        let stable = stable_site_key(&d.layer, &ids, &site);
        (site, semantic_priority(stable, seed))
    }))
}

fn no_decisions_floor(d: &DistilledLayer) -> usize {
    match compile_distilled(d, 1, None) {
        Ok(_) => 1,
        Err(CompileError::BudgetBelowFloor { floor, .. }) => floor,
        Err(error) => panic!("unexpected floor probe error: {error:?}"),
    }
}

#[test]
#[ignore = "diagnostic: heavy compile-in-loop seed A/B; run --release --ignored --nocapture"]
fn structured_seed_equal_eval_heavy_l0() {
    let evals = std::env::var("GKR_BWD_SEED_AB_EVALS")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .unwrap_or(4)
        .max(1);
    let config = |strategy| BwdSearchConfig {
        pop: 4,
        evals,
        seed: 0,
        mutation_sigma: 0.2,
        seed_strategy: strategy,
        order_mutation: BwdOrderMutation::PerKey,
    };

    let mut rows: Vec<_> = HEAVY
        .par_iter()
        .map(|&name| {
            let (layer, cross) = load_layer(name, 0);
            let natural = distill(&layer, BwdRegime::Ext, &cross, None);
            let floor = no_decisions_floor(&natural);
            let budget = floor + HEADROOM_LANES;
            let baseline = compile_distilled(&natural, budget, None)
                .unwrap_or_else(|error| panic!("{name}: baseline compile: {error:?}"));
            let baseline_traffic = baseline.stats_ext.global + baseline.stats_ext.fold_traffic;
            let legacy = search_bwd_layer(
                &layer,
                BwdRegime::Ext,
                &cross,
                budget,
                &config(BwdSeedStrategy::Legacy),
            );
            let structured = search_bwd_layer(
                &layer,
                BwdRegime::Ext,
                &cross,
                budget,
                &config(BwdSeedStrategy::StructureAware),
            );
            let legacy_traffic = legacy.stats.global + legacy.stats.fold_traffic;
            let structured_traffic = structured.stats.global + structured.stats.fold_traffic;
            assert!(legacy_traffic <= baseline_traffic);
            assert!(structured_traffic <= baseline_traffic);
            (
                name.trim_end_matches("_layout_gkr.json"),
                floor,
                budget,
                baseline_traffic,
                legacy_traffic,
                structured_traffic,
            )
        })
        .collect();
    rows.sort_by_key(|row| row.0);

    println!("\n# Equal-evaluation seed A/B (heavy L0 Ext, release)");
    println!("# exact compiler evaluations per mode: {evals}");
    println!(
        "| circuit | floor | budget | uncached | legacy | structured | structured vs legacy |"
    );
    println!("|---|---:|---:|---:|---:|---:|---:|");
    for (name, floor, budget, baseline, legacy, structured) in rows {
        let delta = structured as isize - legacy as isize;
        println!(
            "| {name} | {floor} | {budget} | {baseline} | {legacy} | {structured} | {delta:+} |"
        );
    }
}

#[derive(Clone, Copy, Debug)]
struct CurvePoint {
    circuit: usize,
    evals: usize,
    seed: u64,
    variant: CurveVariant,
    traffic: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum CurveVariant {
    LegacyPerKey,
    StructuredPerKey,
    StructuredEdge,
}

fn median(values: &mut [usize]) -> usize {
    values.sort_unstable();
    values[values.len() / 2]
}

#[test]
#[ignore = "diagnostic: multi-seed heavy convergence curves; run --release --ignored --nocapture"]
fn structured_seed_convergence_curves_heavy_l0() {
    let seeds = std::env::var("GKR_BWD_CURVE_SEEDS")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .unwrap_or(3)
        .max(1);
    let mut eval_budgets: Vec<usize> = std::env::var("GKR_BWD_CURVE_EVALS")
        .unwrap_or_else(|_| "4,8,16,40".to_owned())
        .split(',')
        .filter_map(|value| value.trim().parse::<usize>().ok())
        .filter(|value| *value > 0)
        .collect();
    eval_budgets.sort_unstable();
    eval_budgets.dedup();
    assert!(
        !eval_budgets.is_empty(),
        "GKR_BWD_CURVE_EVALS must contain a positive integer"
    );

    struct Circuit {
        name: &'static str,
        layer: DagLayer,
        cross: common::CrossFields,
        floor: usize,
        budget: usize,
        baseline: usize,
    }

    let circuits: Vec<Circuit> = HEAVY
        .iter()
        .map(|&name| {
            let (layer, cross) = load_layer(name, 0);
            let natural = distill(&layer, BwdRegime::Ext, &cross, None);
            let floor = no_decisions_floor(&natural);
            let budget = floor + HEADROOM_LANES;
            let baseline = compile_distilled(&natural, budget, None)
                .unwrap_or_else(|error| panic!("{name}: baseline compile: {error:?}"));
            Circuit {
                name: name.trim_end_matches("_layout_gkr.json"),
                layer,
                cross,
                floor,
                budget,
                baseline: baseline.stats_ext.global + baseline.stats_ext.fold_traffic,
            }
        })
        .collect();

    // Six independent circuit×seed jobs by default. Each search still scores
    // its candidate cohort through Rayon; nested work stealing keeps both
    // levels bounded by the global pool rather than creating extra threads.
    let jobs: Vec<(usize, u64)> = (0..circuits.len())
        .flat_map(|circuit| (0..seeds as u64).map(move |seed| (circuit, seed)))
        .collect();
    let mut points: Vec<CurvePoint> = jobs
        .into_par_iter()
        .flat_map_iter(|(circuit_index, seed)| {
            let circuit = &circuits[circuit_index];
            let mut points = Vec::with_capacity(eval_budgets.len() * 3);
            for &evals in &eval_budgets {
                for (variant, seed_strategy, order_mutation) in [
                    (
                        CurveVariant::LegacyPerKey,
                        BwdSeedStrategy::Legacy,
                        BwdOrderMutation::PerKey,
                    ),
                    (
                        CurveVariant::StructuredPerKey,
                        BwdSeedStrategy::StructureAware,
                        BwdOrderMutation::PerKey,
                    ),
                    (
                        CurveVariant::StructuredEdge,
                        BwdSeedStrategy::StructureAware,
                        BwdOrderMutation::ReuseEdgeRelocate,
                    ),
                ] {
                    let config = BwdSearchConfig {
                        pop: 4,
                        evals,
                        seed,
                        mutation_sigma: 0.2,
                        seed_strategy,
                        order_mutation,
                    };
                    let outcome = search_bwd_layer(
                        &circuit.layer,
                        BwdRegime::Ext,
                        &circuit.cross,
                        circuit.budget,
                        &config,
                    );
                    let traffic = outcome.stats.global + outcome.stats.fold_traffic;
                    assert!(traffic <= circuit.baseline);
                    points.push(CurvePoint {
                        circuit: circuit_index,
                        evals,
                        seed,
                        variant,
                        traffic,
                    });
                }
            }
            points
        })
        .collect();
    points.sort_by_key(|point| (point.circuit, point.evals, point.seed, point.variant));

    println!("\n# Multi-seed convergence curves (heavy L0 Ext, release)");
    println!("# seeds=0..{} eval_budgets={eval_budgets:?}", seeds - 1);
    println!(
        "| circuit | evals | uncached | legacy/per-key median | structured/per-key median | structured/edge median | edge median delta | edge vs per-key W/T/L |"
    );
    println!("|---|---:|---:|---:|---:|---:|---:|---:|");
    for (circuit_index, circuit) in circuits.iter().enumerate() {
        for &evals in &eval_budgets {
            let paired: Vec<(usize, usize, usize)> = (0..seeds as u64)
                .map(|seed| {
                    let get = |variant| {
                        points
                            .iter()
                            .find(|point| {
                                point.circuit == circuit_index
                                    && point.evals == evals
                                    && point.seed == seed
                                    && point.variant == variant
                            })
                            .expect("every benchmark job must produce one point")
                            .traffic
                    };
                    (
                        get(CurveVariant::LegacyPerKey),
                        get(CurveVariant::StructuredPerKey),
                        get(CurveVariant::StructuredEdge),
                    )
                })
                .collect();
            let mut legacy: Vec<usize> = paired.iter().map(|point| point.0).collect();
            let mut per_key: Vec<usize> = paired.iter().map(|point| point.1).collect();
            let mut edge: Vec<usize> = paired.iter().map(|point| point.2).collect();
            let legacy_median = median(&mut legacy);
            let per_key_median = median(&mut per_key);
            let edge_median = median(&mut edge);
            let wins = paired
                .iter()
                .filter(|(_, per_key, edge)| edge < per_key)
                .count();
            let ties = paired
                .iter()
                .filter(|(_, per_key, edge)| edge == per_key)
                .count();
            let losses = seeds - wins - ties;
            let delta = edge_median as isize - per_key_median as isize;
            println!(
                "| {} | {evals} | {} | {legacy_median} | {per_key_median} | \
                 {edge_median} | {delta:+} | {wins}/{ties}/{losses} |",
                circuit.name, circuit.baseline,
            );
        }
    }

    println!("\n## Paired raw traffic");
    println!(
        "| circuit | evals | seed | legacy/per-key | structured/per-key | structured/edge | edge delta |"
    );
    println!("|---|---:|---:|---:|---:|---:|---:|");
    for point in points
        .iter()
        .filter(|point| point.variant == CurveVariant::LegacyPerKey)
    {
        let per_key = points
            .iter()
            .find(|candidate| {
                candidate.circuit == point.circuit
                    && candidate.evals == point.evals
                    && candidate.seed == point.seed
                    && candidate.variant == CurveVariant::StructuredPerKey
            })
            .expect("paired structured/per-key point");
        let edge = points
            .iter()
            .find(|candidate| {
                candidate.circuit == point.circuit
                    && candidate.evals == point.evals
                    && candidate.seed == point.seed
                    && candidate.variant == CurveVariant::StructuredEdge
            })
            .expect("paired structured/edge point");
        let delta = edge.traffic as isize - per_key.traffic as isize;
        println!(
            "| {} | {} | {} | {} | {} | {} | {delta:+} |",
            circuits[point.circuit].name,
            point.evals,
            point.seed,
            point.traffic,
            per_key.traffic,
            edge.traffic,
        );
    }
    println!(
        "\n# floors/budgets: {:?}",
        circuits
            .iter()
            .map(|circuit| (circuit.name, circuit.floor, circuit.budget))
            .collect::<Vec<_>>()
    );
}

#[derive(Clone, Debug)]
struct ScoreRow {
    seed: u64,
    proxy: usize,
    exact: [f64; 3],
    program_lanes: usize,
}

fn compile_score(
    d: &DistilledLayer,
    decisions: &SiteDecisions,
    budget: usize,
    seed: u64,
) -> Result<ScoreRow, usize> {
    let compiled: BwdCompiledLayer = match compile_distilled(d, budget, Some(decisions)) {
        Ok(compiled) => compiled,
        Err(CompileError::BudgetBelowFloor { floor, .. }) => return Err(floor),
        Err(error) => panic!("unexpected candidate compile error: {error:?}"),
    };
    let mut exact = [0.0; 3];
    for (i, (_, policy)) in POLICIES.iter().enumerate() {
        exact[i] = geometric_total(&compiled, *policy, MAX_ROUND, &d.cross_fields).total_bytes();
    }
    Ok(ScoreRow {
        seed,
        proxy: compiled.stats_ext.global + compiled.stats_ext.fold_traffic,
        exact,
        program_lanes: compiled.stats.program_lanes,
    })
}

fn average_ranks(values: &[f64]) -> Vec<f64> {
    let mut order: Vec<usize> = (0..values.len()).collect();
    order.sort_by(|&a, &b| values[a].total_cmp(&values[b]).then_with(|| a.cmp(&b)));
    let mut ranks = vec![0.0; values.len()];
    let mut start = 0;
    while start < order.len() {
        let mut end = start + 1;
        while end < order.len()
            && values[order[start]].total_cmp(&values[order[end]]) == Ordering::Equal
        {
            end += 1;
        }
        let rank = (start + end - 1) as f64 / 2.0;
        for &idx in &order[start..end] {
            ranks[idx] = rank;
        }
        start = end;
    }
    ranks
}

fn pearson(xs: &[f64], ys: &[f64]) -> f64 {
    assert_eq!(xs.len(), ys.len());
    if xs.len() < 2 {
        return f64::NAN;
    }
    let mx = xs.iter().sum::<f64>() / xs.len() as f64;
    let my = ys.iter().sum::<f64>() / ys.len() as f64;
    let mut cov = 0.0;
    let mut vx = 0.0;
    let mut vy = 0.0;
    for (&x, &y) in xs.iter().zip(ys) {
        cov += (x - mx) * (y - my);
        vx += (x - mx) * (x - mx);
        vy += (y - my) * (y - my);
    }
    if vx == 0.0 || vy == 0.0 {
        return f64::NAN;
    }
    cov / (vx * vy).sqrt()
}

fn spearman(proxy: &[usize], exact: &[f64]) -> f64 {
    let proxy: Vec<f64> = proxy.iter().map(|&v| v as f64).collect();
    pearson(&average_ranks(&proxy), &average_ranks(exact))
}

#[test]
#[ignore = "diagnostic: expensive compile-in-loop correlation report"]
fn proxy_exact_score_correlation_l0() {
    let samples = std::env::var("GKR_BWD_CORR_SAMPLES")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(12)
        .max(1);
    println!("\n# Proxy vs exact DRAM-score correlation (heavy L0, Ext)");
    println!("# samples={samples}; policies={POLICIES:?}; rounds=0..={MAX_ROUND}");
    println!("# priorities are keyed by StableSiteKey, so their semantics survive reordering\n");

    for &name in HEAVY {
        let stem = name.trim_end_matches("_layout_gkr.json");
        let (layer, cross) = load_layer(name, 0);
        let natural = distill(&layer, BwdRegime::Ext, &cross, None);
        assert!(!natural.skipped_decoder, "{stem} L0 must be decoder-free");
        let floor = no_decisions_floor(&natural);
        let budget = floor + HEADROOM_LANES;
        let n_units = natural.unit_order.len();
        let mut rows = Vec::with_capacity(samples);
        let mut infeasible = 0usize;
        let max_attempts = samples.saturating_mul(4).max(samples);

        for attempt in 0..max_attempts {
            if rows.len() == samples {
                break;
            }
            let seed = attempt as u64;
            let permutation = shuffled_permutation(n_units, seed);
            let d = distill(&layer, BwdRegime::Ext, &cross, Some(&permutation));
            let decisions = semantic_decisions(&d, seed ^ 0xa5a5_5a5a_0123_4567);
            match compile_score(&d, &decisions, budget, seed) {
                Ok(row) => rows.push(row),
                Err(_) => infeasible += 1,
            }
        }
        assert!(
            !rows.is_empty(),
            "{stem}: no feasible sampled policy at floor+{HEADROOM_LANES} lanes"
        );

        println!(
            "## {stem}: floor={floor} budget={budget} feasible={} infeasible={infeasible}",
            rows.len()
        );
        println!(
            "| seed | proxy cells | program lanes | geo AlwaysMat B | geo Lazy<=2 B | geo Lazy<=4 B |"
        );
        println!("|---:|---:|---:|---:|---:|---:|");
        for row in &rows {
            println!(
                "| {} | {} | {} | {:.1} | {:.1} | {:.1} |",
                row.seed, row.proxy, row.program_lanes, row.exact[0], row.exact[1], row.exact[2]
            );
        }

        let proxy: Vec<usize> = rows.iter().map(|row| row.proxy).collect();
        for (pi, (policy, _)) in POLICIES.iter().enumerate() {
            let exact: Vec<f64> = rows.iter().map(|row| row.exact[pi]).collect();
            let rho = spearman(&proxy, &exact);
            let proxy_pick = rows
                .iter()
                .enumerate()
                .min_by_key(|(_, row)| (row.proxy, row.program_lanes))
                .map(|(i, _)| i)
                .unwrap();
            let exact_best = exact.iter().copied().fold(f64::INFINITY, f64::min);
            let regret = exact[proxy_pick] - exact_best;
            println!(
                "{policy}: spearman={rho:.6} proxy-pick-seed={} exact-regret={regret:.1} B",
                rows[proxy_pick].seed
            );
        }
        println!();
    }
}
