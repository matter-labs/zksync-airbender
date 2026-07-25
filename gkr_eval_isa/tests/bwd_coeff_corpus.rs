//! Task-2 corpus gate: lower EVERY layer of the 12 pinned fixtures in both
//! backward regimes and pin the census exactly.
//!
//! The synthetic gates in `bwd_coeff_lower.rs` / `bwd_coeff_parity.rs` prove the
//! lowering rules; this file proves they hold on real cones — the ones with cache
//! fences, cross-layer reads, virtual-setup leaves, rewritten lookup queries, and
//! `beta` powers in the hundreds. It also carries the counts Task 3 re-pins
//! against the full corpus, so every number here is asserted EXACTLY: a change is
//! meant to be a signal, not noise.
//!
//! Task 3 adds `bwd_coeff_committed_layout_census` at the bottom: the same 114
//! coordinates, censused per-coordinate through `coeff::stats` and pinned against
//! the frozen `coeff::limits` maxima. It covers only the layouts this crate can
//! reach; the GPU crate's `bwd_coeff_complete_corpus_census` extends it with the
//! conditional `blake2_with_compression` setup.
//!
//! Parity is checked against an independent oracle — the DISTILLED spine
//! evaluated at `X = 0, 1, 2` over affine source pairs, then interpolated. Both
//! coefficients are checked in the `Ext` regime. In `R0` only `acc_c2` can be:
//! `acc_c0` there reads materialized OUTPUT columns, which requires a
//! witness-consistent oracle (`read(output) == cone(0)`), and that is what the
//! synthetic layers in `bwd_coeff_parity.rs` construct. `r0_acc_c0_nonzero_rows`
//! below records that R0's `acc_c0` is nevertheless live everywhere, so the
//! shortcut is not silently producing zero.

mod common;

use std::collections::BTreeMap;
use std::sync::OnceLock;

use common::{FIXTURES, layers_with_bwd_roots};
use cs::gkr_compiler::dag_ir::{
    Bf, BwdRegime, ChallengeKey, ChallengePower, ChallengeRef, ChallengeResolver, DagLayer, Ext,
    FieldKind, LookupResolver, LookupValueKind, ReadPlace, ReadResolver, Resolvers, SinkKind,
    VirtualSetupKind, VirtualSetupResolver, eval_layer_expr,
};
use field::{Field, FieldExtension, PrimeField};
use gkr_eval_isa::bwd::coeff::limits::{in_scope, with_conditional_blake2};
use gkr_eval_isa::bwd::coeff::{
    CoeffCensus, CoeffLayer, CoeffResolver, CoeffTerm, CoefficientRecipeId, SourceId,
    interpret_coeff_layer, lower_coeff_layer,
};
use gkr_eval_isa::bwd::distill::distill;
use gkr_eval_isa::bwd::source::OriginLeaf;
use rayon::prelude::*;

/// Rows sampled per layer x regime for the parity check.
const ROWS: usize = 3;

// ── Affine source model (shared by the oracle and the interpreter) ────────────

const FNV_OFFSET: u32 = 0x811c_9dc5;
const FNV_PRIME: u32 = 0x0100_0193;

fn fnv(words: &[u32]) -> u32 {
    let mut h = FNV_OFFSET;
    for w in words {
        for b in w.to_le_bytes() {
            h ^= b as u32;
            h = h.wrapping_mul(FNV_PRIME);
        }
    }
    h
}

fn lift(v: Bf) -> Ext {
    <Ext as FieldExtension<Bf>>::from_base(v)
}

fn bf(v: u32) -> Bf {
    Bf::from_u32_with_reduction(v)
}

fn place_tag(p: &ReadPlace) -> (u32, u32, u32) {
    match p {
        ReadPlace::BaseLayerMemory { column } => (0, *column as u32, 0),
        ReadPlace::BaseLayerWitness { column } => (1, *column as u32, 0),
        ReadPlace::Setup { column } => (2, *column as u32, 0),
        ReadPlace::Scratch { slot } => (3, *slot as u32, 0),
        ReadPlace::LayerOutput { layer, offset } => (4, *layer as u32, *offset as u32),
        ReadPlace::CacheOutput { layer, offset } => (5, *layer as u32, *offset as u32),
    }
}

fn vs_tag(k: &VirtualSetupKind) -> u32 {
    match k {
        VirtualSetupKind::RangeCheck16Bits => 0,
        VirtualSetupKind::RangeCheckTimestamp => 1,
        VirtualSetupKind::InitsAndTeardownsLow => 2,
        VirtualSetupKind::InitsAndTeardownsHigh => 3,
    }
}

/// `(Endpoint0, Delta)` of a read place.
fn read_pair(p: &ReadPlace, row: usize) -> (Ext, Ext) {
    let (a, b, c) = place_tag(p);
    (lift(bf(fnv(&[0xe0, a, b, c, row as u32]))), lift(bf(fnv(&[0xd1, a, b, c, row as u32]))))
}

/// `(Endpoint0, Delta)` of a virtual-setup source, in the BASE field —
/// `VirtualSetupResolver` serves `Bf`, so both sides must agree there.
fn vs_pair(k: &VirtualSetupKind, row: usize) -> (Bf, Bf) {
    (bf(fnv(&[0xb0, vs_tag(k), row as u32])), bf(fnv(&[0xb1, vs_tag(k), row as u32])))
}

/// Deliberately NOT power-consistent: `challenge(Static(2)) != challenge(One)^2`.
/// Both the oracle and the coefficient bank go through this same resolver, so
/// parity holds — but it fails loudly if normalization ever starts merging
/// challenge exponents, which would be unsound for the power-ignoring keys.
struct Chal;
impl ChallengeResolver for Chal {
    fn challenge(&self, r: &ChallengeRef) -> Ext {
        let key = match &r.key {
            ChallengeKey::LookupAdditive => 0u32,
            ChallengeKey::LookupMultiplicative => 1,
            ChallengeKey::PermutationAdditive => 2,
            ChallengeKey::PermutationLinearization(slot) => 3 + slot_tag(slot),
            ChallengeKey::ConstraintAggregation => 10,
            ChallengeKey::ClaimBatching => 11,
        };
        let power = match &r.power {
            ChallengePower::One => 1u32,
            ChallengePower::Static(i) => *i,
        };
        lift(bf(fnv(&[0xc0, key, power])))
    }
}

fn slot_tag(slot: &cs::gkr_compiler::dag_ir::PermutationSlot) -> u32 {
    use cs::gkr_compiler::dag_ir::PermutationSlot as S;
    match slot {
        S::AddressLow => 0,
        S::AddressHigh => 1,
        S::TimestampLow => 2,
        S::TimestampHigh => 3,
        S::ValueLow => 4,
        S::ValueHigh => 5,
    }
}

/// Evaluates every leaf at the sumcheck point `x`: `S(x) = s0 + x*ds`.
struct Leaves {
    x: u32,
}

impl ReadResolver for Leaves {
    fn read(&self, place: &ReadPlace, row: usize) -> Ext {
        let (e0, ds) = read_pair(place, row);
        let mut v = ds;
        v.mul_assign(&lift(bf(self.x)));
        v.add_assign(&e0);
        v
    }
}

impl VirtualSetupResolver for Leaves {
    fn virtual_setup(&self, kind: &VirtualSetupKind, row: usize) -> Bf {
        let (e0, ds) = vs_pair(kind, row);
        let mut v = ds;
        v.mul_assign(&bf(self.x));
        v.add_assign(&e0);
        v
    }
}

impl LookupResolver for Leaves {
    fn lookup(&self, k: &LookupValueKind, _: usize, _: Ext, _: usize) -> Bf {
        panic!("distillation rewrites LookupValue leaves to their query ({k:?})")
    }
}

struct Pairs<'a> {
    layer: &'a CoeffLayer,
}

impl CoeffResolver for Pairs<'_> {
    fn coefficient(&self, id: CoefficientRecipeId) -> Ext {
        self.layer
            .banked_recipe(id)
            .unwrap_or_else(|| panic!("interpreter asked for unbanked {id:?}"))
            .evaluate(&Chal)
    }

    fn source_pair(&self, id: SourceId, row: usize) -> (Ext, Ext) {
        match &self.layer.sources[id.0 as usize].origin {
            OriginLeaf::Read(p) => read_pair(p, row),
            OriginLeaf::VirtualSetup { kind } => {
                let (e0, ds) = vs_pair(kind, row);
                (lift(e0), lift(ds))
            }
        }
    }
}

/// The distilled spine at sumcheck point `x`.
fn spine_at(distilled: &DagLayer, row: usize, x: u32) -> Ext {
    let leaves = Leaves { x };
    let ch = Chal;
    let r = Resolvers { read: &leaves, lookup: &leaves, virtual_setup: &leaves, challenge: &ch };
    eval_layer_expr(distilled, distilled.roots[0].expr, row, &r)
}

/// `(c0, c2)` of the quadratic through `P(0), P(1), P(2)`.
fn interpolate(v0: Ext, v1: Ext, v2: Ext) -> (Ext, Ext) {
    let mut num = v2;
    num.sub_assign(&v1);
    num.sub_assign(&v1);
    num.add_assign(&v0);
    let two_inv = lift(bf(2)).inverse().expect("2 is invertible");
    let mut c2 = num;
    c2.mul_assign(&two_inv);
    (v0, c2)
}

// ── Census ───────────────────────────────────────────────────────────────────

#[derive(Default)]
struct Census {
    layers: usize,
    lowerings: usize,
    /// `(regime, term kind) -> count`.
    terms: BTreeMap<(&'static str, &'static str), usize>,
    /// Claim-bearing canonical roots by materialized-sink family.
    claim_root_sinks: BTreeMap<&'static str, usize>,
    /// `(regime, read family) -> count` over `CoeffLayer::sources`.
    source_families: BTreeMap<(&'static str, &'static str), usize>,
    /// `(regime, field) -> count` over `CoeffLayer::sources`.
    source_fields: BTreeMap<(&'static str, &'static str), usize>,
    /// Lowered layers with a `c_init`, by regime.
    c_init_layers: BTreeMap<&'static str, usize>,
    /// R0 layers whose DISTILLED spine `c_init` is non-empty (the ones §5.3's
    /// migration assert would have rejected).
    r0_layers_with_spine_c_init: usize,
    bank_total: usize,
    sources_total: usize,
    max_bank: usize,
    max_sources: usize,
    max_terms: usize,
    duals_with_identical_factors: usize,
    /// Non-canonical `Static(1)` / degenerate `Static(0)` spellings surviving
    /// normalization.
    static_one_spellings: usize,
    static_zero_spellings: usize,
    /// Products repeating a POWER-HONOURING key (`ClaimBatching`,
    /// `LookupMultiplicative`) — the only case where an exponent merge would be
    /// both needed and sound.
    products_repeating_power_key: usize,
    /// Products repeating a power-IGNORING key, by key and multiplicity.
    products_repeating_other_key: BTreeMap<String, usize>,
    parity_c2_ok: usize,
    parity_c0_ok_ext: usize,
    parity_failures: Vec<String>,
    r0_acc_c0_nonzero_rows: usize,
    lowering_errors: Vec<String>,
}

fn census() -> &'static Census {
    static CENSUS: OnceLock<Census> = OnceLock::new();
    CENSUS.get_or_init(build_census)
}

fn build_census() -> Census {
    let mut c = Census::default();
    for name in FIXTURES {
        for (li, layer, cross) in layers_with_bwd_roots(name) {
            c.layers += 1;
            for root in &layer.roots {
                if root.claim.is_none() {
                    continue;
                }
                let family = match &root.materialize {
                    None => "none",
                    Some(sink) => match sink.kind {
                        SinkKind::Inner { .. } => "Inner",
                        SinkKind::Cache { .. } => "Cache",
                        SinkKind::Scratch { .. } => "Scratch",
                        SinkKind::Export { .. } => "Export",
                    },
                };
                *c.claim_root_sinks.entry(family).or_default() += 1;
            }
            for regime in [BwdRegime::R0, BwdRegime::Ext] {
                let tag = if regime == BwdRegime::R0 { "R0" } else { "Ext" };
                let d = distill(&layer, regime, &cross, None);
                if regime == BwdRegime::R0 && !d.fragments.c_init.terms.is_empty() {
                    c.r0_layers_with_spine_c_init += 1;
                }
                let lowered = match lower_coeff_layer(&layer, &d) {
                    Ok(lowered) => lowered,
                    Err(e) => {
                        c.lowering_errors.push(format!("{name} L{li} {tag}: {e:?}"));
                        continue;
                    }
                };
                c.lowerings += 1;
                collect(&mut c, tag, &lowered);
                check_parity(&mut c, tag, regime, name, li, &d.layer, &lowered);
            }
        }
    }
    c
}

fn collect(c: &mut Census, tag: &'static str, lowered: &CoeffLayer) {
    for t in &lowered.terms {
        let kind = match t {
            CoeffTerm::C0Linear { .. } => "C0Linear",
            CoeffTerm::C2Product { .. } => "C2Product",
            CoeffTerm::DualProduct { lhs, rhs, .. } => {
                if lhs == rhs {
                    c.duals_with_identical_factors += 1;
                }
                "DualProduct"
            }
        };
        *c.terms.entry((tag, kind)).or_default() += 1;
    }
    for s in &lowered.sources {
        let family = match &s.origin {
            OriginLeaf::Read(ReadPlace::BaseLayerMemory { .. }) => "BaseLayerMemory",
            OriginLeaf::Read(ReadPlace::BaseLayerWitness { .. }) => "BaseLayerWitness",
            OriginLeaf::Read(ReadPlace::Setup { .. }) => "Setup",
            OriginLeaf::Read(ReadPlace::Scratch { .. }) => "Scratch",
            OriginLeaf::Read(ReadPlace::LayerOutput { .. }) => "LayerOutput",
            OriginLeaf::Read(ReadPlace::CacheOutput { .. }) => "CacheOutput",
            OriginLeaf::VirtualSetup { .. } => "VirtualSetup",
        };
        *c.source_families.entry((tag, family)).or_default() += 1;
        let field = if s.field == FieldKind::Ext { "Ext" } else { "Base" };
        *c.source_fields.entry((tag, field)).or_default() += 1;
    }
    if lowered.c_init.is_some() {
        *c.c_init_layers.entry(tag).or_default() += 1;
    }
    c.bank_total += lowered.coefficients.len();
    c.sources_total += lowered.sources.len();
    c.max_bank = c.max_bank.max(lowered.coefficients.len());
    c.max_sources = c.max_sources.max(lowered.sources.len());
    c.max_terms = c.max_terms.max(lowered.terms.len());

    for recipe in &lowered.coefficients {
        assert!(!recipe.is_zero(), "an encoded zero must never be banked");
        assert!(recipe.reserved_id().is_none(), "a reserved literal must never be banked");
        for product in &recipe.terms {
            assert_ne!(product.scalar, 0, "a zero scalar must never survive normalization");
            let mut per_key: BTreeMap<String, usize> = BTreeMap::new();
            for challenge in &product.challenges {
                match challenge.0.power {
                    ChallengePower::Static(1) => c.static_one_spellings += 1,
                    ChallengePower::Static(0) => c.static_zero_spellings += 1,
                    _ => {}
                }
                *per_key.entry(format!("{:?}", challenge.0.key)).or_default() += 1;
            }
            for (key, n) in per_key {
                if n <= 1 {
                    continue;
                }
                let honours_power =
                    key.starts_with("ClaimBatching") || key.starts_with("LookupMultiplicative");
                if honours_power {
                    c.products_repeating_power_key += 1;
                } else {
                    *c.products_repeating_other_key.entry(format!("{key} x{n}")).or_default() += 1;
                }
            }
        }
    }
}

fn check_parity(
    c: &mut Census,
    tag: &'static str,
    regime: BwdRegime,
    name: &str,
    li: usize,
    distilled: &DagLayer,
    lowered: &CoeffLayer,
) {
    let pairs = Pairs { layer: lowered };
    for row in 0..ROWS {
        let (want_c0, want_c2) = interpolate(
            spine_at(distilled, row, 0),
            spine_at(distilled, row, 1),
            spine_at(distilled, row, 2),
        );
        let (got_c0, got_c2) = interpret_coeff_layer(lowered, row, &pairs)
            .unwrap_or_else(|e| panic!("[{name} L{li} {tag}] interpret row {row}: {e:?}"));
        if got_c2 == want_c2 {
            c.parity_c2_ok += 1;
        } else {
            c.parity_failures.push(format!("{name} L{li} {tag} row{row} acc_c2"));
        }
        if regime == BwdRegime::Ext {
            if got_c0 == want_c0 {
                c.parity_c0_ok_ext += 1;
            } else {
                c.parity_failures.push(format!("{name} L{li} {tag} row{row} acc_c0"));
            }
        } else if got_c0 != Ext::ZERO {
            c.r0_acc_c0_nonzero_rows += 1;
        }
    }
}

// ── Gates ────────────────────────────────────────────────────────────────────

#[test]
fn corpus_lowers_and_matches_the_canonical_dag_with_a_pinned_census() {
    let c = census();

    assert_eq!(c.lowering_errors, Vec::<String>::new(), "every corpus layer must lower");
    assert_eq!(c.layers, 57, "layers with backward roots across the 12 pinned fixtures");
    assert_eq!(c.lowerings, 114, "57 layers x 2 regimes");

    // Parity against the distilled-spine oracle.
    assert_eq!(c.parity_failures, Vec::<String>::new(), "coefficient parity");
    assert_eq!(c.parity_c2_ok, 114 * ROWS, "acc_c2 checked on every layer x regime x row");
    assert_eq!(c.parity_c0_ok_ext, 57 * ROWS, "acc_c0 checked on every Ext layer x row");
    assert_eq!(
        c.r0_acc_c0_nonzero_rows,
        57 * ROWS,
        "R0's acc_c0 is live on every layer — the output shortcut is not silently zero"
    );

    // Term census. No third continuation category exists to populate: Ext emits
    // only C0Linear and native DualProduct, so a standalone continuation
    // C0Product/C2Product remains a structural compiler error.
    assert_eq!(
        c.terms,
        BTreeMap::from([
            (("Ext", "C0Linear"), 2157),
            (("Ext", "DualProduct"), 5872),
            (("R0", "C0Linear"), 1959),
            (("R0", "C2Product"), 5872),
        ])
    );
    assert_eq!(c.duals_with_identical_factors, 402, "A*A duals are still native duals");

    // Zero degree-three rejections corpus-wide (the `lowering_errors` assertion
    // above covers it; this states the intent).
    assert!(
        !c.lowering_errors.iter().any(|e| e.contains("DegreeTooHigh")),
        "no fragment exceeds degree two on the corpus"
    );

    // R0 acc_c0 reads exactly one materialized output per claim-bearing output
    // root: 1959 `Inner` sinks, 1959 R0 `C0Linear` terms. Every other claim root
    // is a claim-only constraint contributing nothing.
    assert_eq!(
        c.claim_root_sinks,
        BTreeMap::from([("Inner", 1959), ("none", 901)]),
        "the corpus materializes claim roots only to Inner sinks — Cache/Scratch/Export \
         sink handling in `sink_read_place` is therefore covered only synthetically"
    );
    assert_eq!(c.terms[&("R0", "C0Linear")], c.claim_root_sinks["Inner"]);

    // Source interning covers every read family the corpus uses, including the
    // cross-layer ones whose width comes from `cross_fields`, plus virtual setup.
    assert_eq!(
        c.source_families,
        BTreeMap::from([
            (("Ext", "BaseLayerMemory"), 472),
            (("Ext", "BaseLayerWitness"), 1064),
            (("Ext", "CacheOutput"), 817),
            (("Ext", "LayerOutput"), 1783),
            (("Ext", "VirtualSetup"), 23),
            (("R0", "BaseLayerMemory"), 352),
            (("R0", "BaseLayerWitness"), 755),
            (("R0", "CacheOutput"), 804),
            (("R0", "LayerOutput"), 3561),
            (("R0", "VirtualSetup"), 23),
        ])
    );

    // Widths: every `Ext`-regime source is an Ext fold leaf (`field_overrides`),
    // while R0 keeps native widths and takes cross-layer ones from `cross_fields`
    // / the sink's own field.
    assert_eq!(
        c.source_fields,
        BTreeMap::from([
            (("Ext", "Ext"), 4159),
            (("R0", "Base"), 1626),
            (("R0", "Ext"), 3869),
        ])
    );
    assert_eq!(c.source_fields[&("Ext", "Ext")], 4159, "no Ext-regime source stays Base");
    assert!(!c.source_fields.contains_key(&("Ext", "Base")));

    // c_init: R0 always drops it, even though 26 of the 57 R0 layers have a
    // structurally non-empty spine `c_init` (design §5.3's migration assert would
    // have rejected all 26 — see `lower_c_init` for the parity explanation).
    assert_eq!(c.r0_layers_with_spine_c_init, 26);
    assert_eq!(c.c_init_layers, BTreeMap::from([("Ext", 27)]));
    assert!(!c.c_init_layers.contains_key("R0"), "R0 never emits a c_init");

    // Bank / source volume, and the per-layer ceilings Task 3 checks against the
    // 13-bit coefficient field (`bank + 2 <= 8192`).
    assert_eq!(c.bank_total, 8320);
    assert_eq!(c.sources_total, 9654);
    assert_eq!(c.max_bank, 1138, "largest per-layer coefficient bank");
    assert_eq!(c.max_sources, 1062);
    assert_eq!(c.max_terms, 1791);
    assert!(
        c.max_bank + CoefficientRecipeId::RESERVED as usize <= 8_192,
        "the largest bank plus the two reserved literals must fit a 13-bit field"
    );

    // Normalization leaves no non-canonical challenge spelling behind.
    assert_eq!(c.static_one_spellings, 0, "Static(1) is canonicalized to One");
    assert_eq!(c.static_zero_spellings, 0);
}

// ── Task 3: the committed-layout freeze census ────────────────────────────────

/// Every censused coordinate of the 12 committed layouts, lexically sorted.
///
/// Built once and shared, because the whole point of the freeze gate is that ONE
/// set of numbers backs every assertion below.
fn committed_rows() -> &'static Vec<gkr_eval_isa::bwd::coeff::CoeffCensusRow> {
    static ROWS: OnceLock<Vec<gkr_eval_isa::bwd::coeff::CoeffCensusRow>> = OnceLock::new();
    ROWS.get_or_init(|| {
        // Fixture loading + DAG lowering is the expensive part, so it is the outer
        // parallel unit; the per-coordinate work inside is independent too.
        let mut coordinates: Vec<(String, usize, DagLayer, common::CrossFields)> = FIXTURES
            .par_iter()
            .flat_map_iter(|name| {
                layers_with_bwd_roots(name)
                    .map(move |(li, layer, cross)| ((*name).to_string(), li, layer, cross))
            })
            .collect();
        coordinates.sort_by(|a, b| (&a.0, a.1).cmp(&(&b.0, b.1)));

        let (mut rows, failures): (Vec<_>, Vec<_>) = coordinates
            .par_iter()
            .map(|(name, li, layer, cross)| {
                gkr_eval_isa::bwd::coeff::census_layer(name, *li, layer, cross)
            })
            .unzip();
        let failures: Vec<_> = failures.into_iter().flatten().collect();
        assert!(
            failures.is_empty(),
            "every committed-layout coordinate must lower: {failures:?}"
        );
        let mut rows: Vec<_> = rows.drain(..).flatten().collect();
        rows.sort_by(|a, b| a.sort_key().cmp(&b.sort_key()));
        rows
    })
}

/// Task 3's freeze gate over the layouts this crate can reach.
///
/// Everything here is an EXACT pin against `coeff::limits::in_scope`, and every
/// encoding limit is asserted SEPARATELY from the measurement that must fit it —
/// a measured maximum and a format ceiling are different kinds of fact.
#[test]
fn bwd_coeff_committed_layout_census() {
    let rows = committed_rows();

    println!("{}", gkr_eval_isa::bwd::coeff::stats::CSV_HEADER);
    for row in rows {
        println!("{}", gkr_eval_isa::bwd::coeff::stats::csv_line(row));
    }

    // ── corpus shape ─────────────────────────────────────────────────────
    assert_eq!(FIXTURES.len(), in_scope::CIRCUITS);
    assert_eq!(rows.len(), in_scope::COORDINATES);
    assert_eq!(rows.len() / 2, in_scope::LAYERS);
    assert!(rows.iter().all(|row| row.census.canonical_roots > 0));

    // ── per-coordinate maxima ────────────────────────────────────────────
    let mut max = CoeffCensus::default();
    for row in rows {
        max.merge_max(&row.census);
    }
    println!("in-scope maxima: {max:#?}");

    assert_eq!(max.coefficient_recipes, in_scope::MAX_COEFFICIENT_RECIPES);
    assert_eq!(max.sources, in_scope::MAX_SOURCES);
    assert_eq!(max.projections, in_scope::MAX_PROJECTIONS);
    assert_eq!(max.terms, in_scope::MAX_TERMS);
    assert_eq!(max.max_expansion_factor, in_scope::MAX_EXPANSION_FACTOR);
    assert_eq!(max.max_fragment_atoms, in_scope::MAX_FRAGMENT_ATOMS);
    assert_eq!(max.source_windows, in_scope::MAX_SOURCE_WINDOWS_USED);
    assert_eq!(max.lower_bound_program_bytes, in_scope::MAX_LOWER_BOUND_PROGRAM_BYTES);
    assert_eq!(max.upper_bound_program_bytes, in_scope::MAX_UPPER_BOUND_PROGRAM_BYTES);
    assert_eq!(
        max.cont_standalone_product,
        in_scope::MAX_CONTINUATION_STANDALONE_PRODUCTS,
        "a live standalone continuation product would need its own opcode"
    );

    // ── encoding limits (separate from the measurements above) ────────────
    assert!(
        max.coefficient_recipes + CoefficientRecipeId::RESERVED as usize
            <= gkr_eval_isa::bwd::coeff::MAX_COEFFICIENT_ENCODINGS,
        "deduplicated_bank_recipe_count + 2 must fit the 13-bit coefficient field"
    );
    assert!(
        max.source_windows <= gkr_eval_isa::bwd::coeff::MAX_SOURCE_WINDOWS,
        "final source-window count must fit the 6-bit window field"
    );

    // ── the lower bound is the only unrepairable one ──────────────────────
    let overflowing: Vec<_> =
        rows.iter().filter(|row| !row.census.lower_bound_fits()).map(|r| r.sort_key()).collect();
    assert_eq!(
        overflowing,
        Vec::new(),
        "a lower-bound overflow cannot be repaired by any later codec"
    );
    let inconclusive: Vec<_> =
        rows.iter().filter(|row| row.census.inconclusive()).map(|r| r.sort_key()).collect();
    println!(
        "proven to fit: {}/{}; inconclusive (Task 8 decides): {:?}",
        rows.len() - inconclusive.len(),
        rows.len(),
        inconclusive
    );
    // Every coordinate's CONSERVATIVE maximum program stream fits, so the term
    // set is proven encodable before paging/placement exist. This bounds the
    // PROGRAM STREAM only — the remaining by-value descriptor metadata still has
    // `MIN_DESCRIPTOR_HEADROOM_BYTES` to fit in, and Tasks 8-9 freeze that.
    assert_eq!(inconclusive.len(), in_scope::INCONCLUSIVE_COORDINATES);
    assert_eq!(
        in_scope::MIN_DESCRIPTOR_HEADROOM_BYTES,
        gkr_eval_isa::bwd::coeff::KERNEL_ARGUMENT_CEILING_BYTES
            - in_scope::MAX_UPPER_BOUND_PROGRAM_BYTES
    );

    // ── frozen opcode tables ─────────────────────────────────────────────
    let mut live_r0: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut live_ext: BTreeMap<&'static str, usize> = BTreeMap::new();
    for row in rows {
        let sink = if row.regime == BwdRegime::R0 { &mut live_r0 } else { &mut live_ext };
        for category in &row.live_categories {
            *sink.entry(category.label()).or_default() += 1;
            let opcode = if row.regime == BwdRegime::R0 {
                gkr_eval_isa::bwd::coeff::r0_opcode(*category)
            } else {
                gkr_eval_isa::bwd::coeff::continuation_opcode(*category)
            };
            assert!(
                opcode.is_some(),
                "{:?} emitted {} which the {} opcode table does not encode",
                row.sort_key(),
                category.label(),
                if row.regime == BwdRegime::R0 { "R0" } else { "continuation" }
            );
        }
    }
    println!("live R0 categories: {live_r0:?}\nlive Ext categories: {live_ext:?}");
    // Continuation stays a two-term ISA plus its move: no third arithmetic
    // category exists to give opcode 3 to.
    assert_eq!(
        live_ext.keys().copied().collect::<Vec<_>>(),
        vec!["C0LinearE4", "DualProductE4"],
        "continuation emits only C0Linear and native DualProduct"
    );

    // ── aggregates, re-confirming Task 2 through the new census path ──────
    let sum = |f: fn(&CoeffCensus) -> usize| rows.iter().map(|r| f(&r.census)).sum::<usize>();
    assert_eq!(sum(|c| c.r0_c0_linear()), 1959);
    assert_eq!(sum(|c| c.r0_c2_product()), 5872);
    assert_eq!(sum(|c| c.cont_c0_linear), 2157);
    assert_eq!(sum(|c| c.cont_dual_product), 5872);
    assert_eq!(sum(|c| c.coefficient_recipes), 8320);
    assert_eq!(sum(|c| c.sources), 9654);
    assert_eq!(sum(|c| c.cont_c0_linear_bf), 0, "every continuation source is an Ext fold leaf");
    assert_eq!(
        rows.iter().filter(|r| r.census.has_c_init).count(),
        27,
        "only the Ext regime emits a c_init"
    );
    assert!(
        rows.iter().filter(|r| r.regime == BwdRegime::R0).all(|r| !r.census.has_c_init),
        "R0 drops the spine c_init (design §5.3)"
    );

    // Claim roots materialize ONLY to Inner sinks on this corpus, so
    // `sink_read_place`'s Cache/Scratch arms are covered synthetically only.
    let r0 = || rows.iter().filter(|r| r.regime == BwdRegime::R0);
    assert_eq!(r0().map(|r| r.census.sinks_inner).sum::<usize>(), 1959);
    assert_eq!(r0().map(|r| r.census.sinks_cache).sum::<usize>(), 0);
    assert_eq!(r0().map(|r| r.census.sinks_scratch).sum::<usize>(), 0);
    assert_eq!(r0().map(|r| r.census.sinks_export).sum::<usize>(), 0);
    assert_eq!(r0().map(|r| r.census.constraint_only_roots).sum::<usize>(), 901);
}

/// The conditional-scope bookkeeping this crate can state on its own (design
/// §3.1): `blake2_with_compression` has no committed `_layout_gkr.json`, so the
/// in-scope maxima above are exactly the 12 mandatory layouts, and the diagnostic
/// set differs from them only by that one conditional circuit.
#[test]
fn conditional_blake2_scope_is_recorded_separately() {
    assert_eq!(in_scope::CIRCUITS, FIXTURES.len());
    assert_eq!(with_conditional_blake2::CIRCUITS, in_scope::CIRCUITS + 1);
    assert!(
        with_conditional_blake2::COORDINATES > in_scope::COORDINATES,
        "the diagnostic set must actually include the conditional circuit"
    );
    // Diagnostic maxima may never be SMALLER than in-scope ones: they are a
    // superset census.
    assert!(with_conditional_blake2::MAX_COEFFICIENT_RECIPES >= in_scope::MAX_COEFFICIENT_RECIPES);
    assert!(with_conditional_blake2::MAX_TERMS >= in_scope::MAX_TERMS);
    assert!(with_conditional_blake2::MAX_SOURCES >= in_scope::MAX_SOURCES);
    assert!(
        with_conditional_blake2::MAX_LOWER_BOUND_PROGRAM_BYTES
            >= in_scope::MAX_LOWER_BOUND_PROGRAM_BYTES
    );
    // No format is sized from the diagnostic set, so it is allowed to be equal —
    // and it IS equal here, because `get_blake2_with_compression_circuit_setup`
    // compiles the same GKR circuit as the committed
    // `blake2_with_extended_control_layout_gkr.json`. The GPU crate's
    // `bwd_coeff_complete_corpus_census` is what proves that empirically.
    assert_eq!(with_conditional_blake2::MAX_TERMS, in_scope::MAX_TERMS);
}

/// The guard behind the decision NOT to merge repeated challenge factors into an
/// exponent.
///
/// `ChallengePower` is only an exponent for the keys whose resolver arm reads it —
/// `ClaimBatching` (`pow(beta, i)` / `beta_pows[i]`) and `LookupMultiplicative`
/// (`alpha_pows[j]`). `LookupAdditive`, `PermutationAdditive` and
/// `PermutationLinearization` ignore `power` and return their single challenge, so
/// rewriting `gamma*gamma` as `{LookupAdditive, Static(2)}` would resolve to
/// `gamma`, losing a factor.
///
/// On this corpus the repeated-key products are EXCLUSIVELY on those
/// power-ignoring keys, and no product repeats a power-honouring key — so the
/// merge would deduplicate nothing while corrupting 528 products. If a future
/// compiler change ever emits `beta * beta`, this fires, and the exponent merge
/// can then be introduced for that key alone, where it is sound.
#[test]
fn coefficient_products_never_repeat_a_power_honouring_key() {
    let c = census();
    assert_eq!(
        c.products_repeating_power_key, 0,
        "a repeated ClaimBatching/LookupMultiplicative factor would make `beta*beta` and \
         `beta^2` two bank entries for one value; only then is an exponent merge warranted"
    );
    assert_eq!(
        c.products_repeating_other_key,
        BTreeMap::from([
            ("LookupAdditive x2".to_string(), 334),
            ("PermutationAdditive x2".to_string(), 18),
            ("PermutationLinearization(AddressHigh) x2".to_string(), 68),
            ("PermutationLinearization(AddressLow) x2".to_string(), 36),
            ("PermutationLinearization(TimestampHigh) x2".to_string(), 18),
            ("PermutationLinearization(TimestampLow) x2".to_string(), 18),
            ("PermutationLinearization(ValueHigh) x2".to_string(), 18),
            ("PermutationLinearization(ValueLow) x2".to_string(), 18),
        ]),
        "repeated factors live only on keys whose resolver ignores ChallengePower, where \
         merging them into an exponent would silently drop a factor"
    );
}
