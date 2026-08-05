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
//! Parity is checked against the DISTILLED spine evaluated at `X = 0, 1, 2` over
//! affine source pairs, then interpolated. That oracle is independent of the
//! COEFFICIENT lowering but not of `distill`, which sits on both sides — the
//! canonical-DAG oracle that is independent of both is `bwd_coeff_parity.rs`, over
//! five hand-built layers. Both coefficients are checked in the `Ext` regime. In
//! `R0` only `acc_c2` can be:
//! `acc_c0` there reads materialized OUTPUT columns, which requires a
//! witness-consistent oracle (`read(output) == cone(0)`), and that is what the
//! synthetic layers in `bwd_coeff_parity.rs` construct. `r0_acc_c0_nonzero_rows`
//! below records that R0's `acc_c0` is nevertheless live everywhere, so the
//! shortcut is not silently producing zero.

mod common;

use std::collections::{BTreeMap, BTreeSet};
use std::sync::OnceLock;

use common::{FIXTURES, layers_with_bwd_roots};
use field::{Field, FieldExtension, PrimeField};
use gkr_eval_ir::{
    Bf, ChallengeKey, ChallengePower, ChallengeRef, ChallengeResolver, DagLayer, Ext, FieldKind,
    LookupResolver, LookupValueKind, ReadPlace, ReadResolver, Resolvers, SinkKind,
    VirtualSetupKind, VirtualSetupResolver, eval_layer_expr,
};
use gkr_eval_isa::BwdRegime;
use gkr_eval_isa::bwd::coeff::lean::decode_atoms;
use gkr_eval_isa::bwd::coeff::limits::{LEAN_MAX_IMMEDIATES, in_scope, with_conditional_blake2};
use gkr_eval_isa::bwd::coeff::model::ImmediateId;
use gkr_eval_isa::bwd::coeff::{
    CoeffCensus, CoeffLayer, CoeffResolver, CoeffTerm, CoefficientRecipeId, LeanAtom, LeanProgram,
    NormalizedCoefficientRecipe, SourceId, TermId, compile_lean_coordinate, factor,
    group_coeff_layer, immediate_value, interpret_coeff_layer, lower_coeff_layer, lower_lean_layer,
    rescale,
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
    (
        lift(bf(fnv(&[0xe0, a, b, c, row as u32]))),
        lift(bf(fnv(&[0xd1, a, b, c, row as u32]))),
    )
}

/// `(Endpoint0, Delta)` of a virtual-setup source, in the BASE field —
/// `VirtualSetupResolver` serves `Bf`, so both sides must agree there.
fn vs_pair(k: &VirtualSetupKind, row: usize) -> (Bf, Bf) {
    (
        bf(fnv(&[0xb0, vs_tag(k), row as u32])),
        bf(fnv(&[0xb1, vs_tag(k), row as u32])),
    )
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

fn slot_tag(slot: &gkr_eval_ir::PermutationSlot) -> u32 {
    use gkr_eval_ir::PermutationSlot as S;
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
    let r = Resolvers {
        read: &leaves,
        lookup: &leaves,
        virtual_setup: &leaves,
        challenge: &ch,
    };
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
        let field = if s.field == FieldKind::Ext {
            "Ext"
        } else {
            "Base"
        };
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
        assert!(
            recipe.reserved_id().is_none(),
            "a reserved literal must never be banked"
        );
        for product in &recipe.terms {
            assert_ne!(
                product.scalar, 0,
                "a zero scalar must never survive normalization"
            );
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
                    *c.products_repeating_other_key
                        .entry(format!("{key} x{n}"))
                        .or_default() += 1;
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
            c.parity_failures
                .push(format!("{name} L{li} {tag} row{row} acc_c2"));
        }
        if regime == BwdRegime::Ext {
            if got_c0 == want_c0 {
                c.parity_c0_ok_ext += 1;
            } else {
                c.parity_failures
                    .push(format!("{name} L{li} {tag} row{row} acc_c0"));
            }
        } else if got_c0 != Ext::ZERO {
            c.r0_acc_c0_nonzero_rows += 1;
        }
    }
}

// ── Gates ────────────────────────────────────────────────────────────────────

/// Corpus-scale lowering, value parity against the DISTILLED SPINE, and the
/// frozen census.
///
/// The oracle is `distilled.roots[0].expr` (`spine_at`), NOT the canonical DAG, so
/// a distillation bug is invisible to this gate by construction — `distill` is on
/// both sides of the comparison. The canonical-DAG oracle exists and is genuinely
/// independent, but it runs over five hand-built layers in
/// `bwd_coeff_parity.rs::semantic_coefficients_match_canonical_dag_on_synthetic_rows`;
/// this file's job is real cones at scale, not oracle independence.
///
/// Coverage is therefore split, exactly as the module doc says:
///
///   * `acc_c2` — value-compared on every layer x regime x row;
///   * `acc_c0` — value-compared in the `Ext` regime only; and
///   * R0's `acc_c0` — NOT value-compared here, only counted non-zero
///     (`r0_acc_c0_nonzero_rows`). It reads materialized OUTPUT columns, which
///     needs a witness-consistent oracle (`read(output) == cone(0)`) across
///     layers; this file's `read_pair` is a deliberately independent FNV model
///     that cannot supply that. Its independent anchor is
///     `bwd_coeff_parity.rs`'s synthetic layers, and §12.4's own gate for R0 on
///     real cones is the COST pin below
///     (`terms[R0][C0Linear] == claim_root_sinks["Inner"] == 1959`) — value parity
///     alone is insufficient for the output shortcut, which is why the design asks
///     for the cost identity instead.
#[test]
fn corpus_lowers_and_matches_the_distilled_spine_with_a_pinned_census() {
    let c = census();

    assert_eq!(
        c.lowering_errors,
        Vec::<String>::new(),
        "every corpus layer must lower"
    );
    assert_eq!(
        c.layers, 57,
        "layers with backward roots across the 12 pinned fixtures"
    );
    assert_eq!(c.lowerings, 114, "57 layers x 2 regimes");

    // Parity against the distilled-spine oracle.
    assert_eq!(
        c.parity_failures,
        Vec::<String>::new(),
        "coefficient parity"
    );
    assert_eq!(
        c.parity_c2_ok,
        114 * ROWS,
        "acc_c2 checked on every layer x regime x row"
    );
    assert_eq!(
        c.parity_c0_ok_ext,
        57 * ROWS,
        "acc_c0 checked on every Ext layer x row"
    );
    // NOT a value comparison — see the doc comment. This only proves R0's `acc_c0`
    // is live on every layer, i.e. the output shortcut is not silently zero.
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
    assert_eq!(
        c.duals_with_identical_factors, 402,
        "A*A duals are still native duals"
    );

    // Zero degree-three rejections corpus-wide (the `lowering_errors` assertion
    // above covers it; this states the intent).
    assert!(
        !c.lowering_errors
            .iter()
            .any(|e| e.contains("DegreeTooHigh")),
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
    assert_eq!(
        c.source_fields[&("Ext", "Ext")],
        4159,
        "no Ext-regime source stays Base"
    );
    assert!(!c.source_fields.contains_key(&("Ext", "Base")));

    // c_init: R0 always drops it, even though 26 of the 57 R0 layers have a
    // structurally non-empty spine `c_init` (design §5.3's migration assert would
    // have rejected all 26 — see `lower_c_init` for the parity explanation).
    assert_eq!(c.r0_layers_with_spine_c_init, 26);
    assert_eq!(c.c_init_layers, BTreeMap::from([("Ext", 27)]));
    assert!(
        !c.c_init_layers.contains_key("R0"),
        "R0 never emits a c_init"
    );

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
    assert_eq!(
        c.static_one_spellings, 0,
        "Static(1) is canonicalized to One"
    );
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
    assert_eq!(
        max.lower_bound_program_bytes,
        in_scope::MAX_LOWER_BOUND_PROGRAM_BYTES
    );
    assert_eq!(
        max.upper_bound_program_bytes,
        in_scope::MAX_UPPER_BOUND_PROGRAM_BYTES
    );
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
    let overflowing: Vec<_> = rows
        .iter()
        .filter(|row| !row.census.lower_bound_fits())
        .map(|r| r.sort_key())
        .collect();
    assert_eq!(
        overflowing,
        Vec::new(),
        "a lower-bound overflow cannot be repaired by any later codec"
    );
    let inconclusive: Vec<_> = rows
        .iter()
        .filter(|row| row.census.inconclusive())
        .map(|r| r.sort_key())
        .collect();
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
        let sink = if row.regime == BwdRegime::R0 {
            &mut live_r0
        } else {
            &mut live_ext
        };
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
                if row.regime == BwdRegime::R0 {
                    "R0"
                } else {
                    "continuation"
                }
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
    assert_eq!(
        sum(|c| c.cont_c0_linear_bf),
        0,
        "every continuation source is an Ext fold leaf"
    );
    assert_eq!(
        rows.iter().filter(|r| r.census.has_c_init).count(),
        27,
        "only the Ext regime emits a c_init"
    );
    assert!(
        rows.iter()
            .filter(|r| r.regime == BwdRegime::R0)
            .all(|r| !r.census.has_c_init),
        "R0 drops the spine c_init (design §5.3)"
    );

    // Claim roots materialize ONLY to Inner sinks on this corpus, so
    // `sink_read_place`'s Cache/Scratch arms are covered synthetically only.
    let r0 = || rows.iter().filter(|r| r.regime == BwdRegime::R0);
    assert_eq!(r0().map(|r| r.census.sinks_inner).sum::<usize>(), 1959);
    assert_eq!(r0().map(|r| r.census.sinks_cache).sum::<usize>(), 0);
    assert_eq!(r0().map(|r| r.census.sinks_scratch).sum::<usize>(), 0);
    assert_eq!(r0().map(|r| r.census.sinks_export).sum::<usize>(), 0);
    assert_eq!(
        r0().map(|r| r.census.constraint_only_roots).sum::<usize>(),
        901
    );
}

/// The conditional-scope bookkeeping this crate can state on its own (design
/// §3.1): `blake2_with_compression` has no committed `_layout_gkr.json`, so the
/// in-scope maxima above are exactly the 12 mandatory layouts, and the diagnostic
/// set differs from them only by that one conditional circuit.
///
/// **Every maximum is compared against a MEASUREMENT, never against its own
/// `in_scope` counterpart.** `limits.rs`'s diagnostic maxima are literally defined
/// as aliases (`MAX_TERMS: usize = in_scope::MAX_TERMS`), so `>=` or `==` against
/// those counterparts is a tautology that cannot fail — which would make
/// `limits.rs`'s claim that "this module is where a divergence shows up" false.
/// Comparing the diagnostic constants to the maxima this file censuses instead
/// makes the ALIASING itself the thing under test: replacing an alias with a
/// literal, which is the edit that would let the two sets drift, trips here.
///
/// What still cannot be checked from this crate is whether the delegation wrapper
/// really compiles the same circuit — that needs the conditional setup, which has
/// no committed layout. The GPU crate's `bwd_coeff_complete_corpus_census` is the
/// empirical proof.
#[test]
fn conditional_blake2_scope_is_recorded_separately() {
    let rows = committed_rows();
    let mut measured = CoeffCensus::default();
    for row in rows {
        measured.merge_max(&row.census);
    }

    assert_eq!(in_scope::CIRCUITS, FIXTURES.len());
    // Exact deltas, not `>`: the conditional circuit contributes 8 layers x 2
    // regimes and one circuit, and those three literals are the whole difference
    // between the two sets.
    assert_eq!(with_conditional_blake2::CIRCUITS, in_scope::CIRCUITS + 1);
    assert_eq!(with_conditional_blake2::LAYERS, in_scope::LAYERS + 8);
    assert_eq!(
        with_conditional_blake2::COORDINATES,
        in_scope::COORDINATES + 16
    );
    assert_eq!(
        with_conditional_blake2::COORDINATES,
        2 * with_conditional_blake2::LAYERS,
        "every layer is censused in both regimes"
    );

    // The diagnostic maxima against the MEASURED in-scope ones. Equality is the
    // claim: `get_blake2_with_compression_circuit_setup` compiles
    // `define_blake2_with_extended_control_delegation_circuit` at the same
    // `DOMAIN_SIZE_LOG2` with caches on, which is byte-for-byte the call that
    // generated the committed `blake2_with_extended_control_layout_gkr.json`, so
    // the conditional circuit is the SAME GKR circuit as an already-mandatory one.
    // No format is sized from these, which is why equality is allowed at all.
    assert_eq!(
        with_conditional_blake2::MAX_COEFFICIENT_RECIPES,
        measured.coefficient_recipes
    );
    assert_eq!(with_conditional_blake2::MAX_TERMS, measured.terms);
    assert_eq!(with_conditional_blake2::MAX_SOURCES, measured.sources);
    assert_eq!(
        with_conditional_blake2::MAX_PROJECTIONS,
        measured.projections
    );
    assert_eq!(
        with_conditional_blake2::MAX_LOWER_BOUND_PROGRAM_BYTES,
        measured.lower_bound_program_bytes
    );
    assert_eq!(
        with_conditional_blake2::MAX_UPPER_BOUND_PROGRAM_BYTES,
        measured.upper_bound_program_bytes
    );
    // A superset census may never report a SMALLER maximum than the subset it
    // contains, which is the invariant the equalities above happen to satisfy.
    assert!(with_conditional_blake2::MAX_TERMS >= in_scope::MAX_TERMS);
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

// ── The grouping transform on real banks ──────────────────────────────────────

/// Design §6.1 on real cones: the coefficient GROUPING transform is
/// structure-preserving on every `Ext` coordinate of the pinned corpus.
///
/// Structural, not numeric, and deliberately so — `imm x core == recipe` is checked
/// as an equality of NORMALIZED RECIPES, which is strictly stronger than equality
/// of their evaluations at one challenge assignment: it holds for every resolver at
/// once and needs none. `field::inverse` and `from_terms`'s re-canonicalization are
/// the only arithmetic involved, so a mismatch is a real bug in the factoring, never
/// a tolerance.
///
/// Three claims:
///
///   (a) EVERY original bank recipe — not just the ones that end up realized as
///       group members — either factors with an exact structural rescale back to
///       itself, or is a bare scalar (the one shape §4.1 excludes from grouping).
///   (b) Every realized group member's ORIGINAL recipe, captured before the
///       transform, equals its group's core rescaled by the member's immediate.
///   (c) The transform's own invariants: chop bound, ascending disjoint members,
///       member coefficients rewritten to the core, non-members and `c_init` left
///       with their own recipes, and both tables sorted and within their caps.
#[test]
fn grouped_corpus_layers_factor_exactly() {
    #[derive(Default)]
    struct Tally {
        coordinates: usize,
        recipes: usize,
        factored: usize,
        bare: usize,
        groups: usize,
        members: usize,
        with_groups: usize,
        l0_without_groups: Vec<String>,
        max_members: usize,
        max_immediates: usize,
        bank_before: usize,
        bank_after: usize,
    }

    let tallies: Vec<Tally> = FIXTURES
        .par_iter()
        .map(|name| {
            let mut t = Tally::default();
            for (li, layer, cross) in layers_with_bwd_roots(name) {
                let where_ = format!("{name} L{li} Ext");
                let d = distill(&layer, BwdRegime::Ext, &cross, None);
                let lowered =
                    lower_coeff_layer(&layer, &d).unwrap_or_else(|e| panic!("[{where_}] {e:?}"));
                t.coordinates += 1;
                t.bank_before += lowered.coefficients.len();

                // (a) Every ORIGINAL bank recipe, realized as a group member or not.
                for recipe in &lowered.coefficients {
                    t.recipes += 1;
                    match factor(recipe) {
                        Some((immediate, core)) => {
                            assert_eq!(
                                core.terms[0].scalar, 1,
                                "[{where_}] a core's leading scalar must be one"
                            );
                            assert_eq!(
                                &rescale(&core, immediate),
                                recipe,
                                "[{where_}] immediate x core must be the recipe exactly"
                            );
                            t.factored += 1;
                        }
                        None => {
                            assert_eq!(
                                recipe.terms.len(),
                                1,
                                "[{where_}] only a bare scalar may refuse to factor: {recipe:?}"
                            );
                            assert!(
                                recipe.terms[0].challenges.is_empty(),
                                "[{where_}] only a bare scalar may refuse to factor: {recipe:?}"
                            );
                            t.bare += 1;
                        }
                    }
                }

                // Captured BEFORE the transform rewrites any coefficient id.
                let originals: BTreeMap<TermId, NormalizedCoefficientRecipe> = lowered
                    .terms
                    .iter()
                    .filter_map(|term| {
                        lowered
                            .banked_recipe(term.coefficient())
                            .map(|r| (term.id(), r.clone()))
                    })
                    .collect();
                let literals: BTreeMap<TermId, CoefficientRecipeId> = lowered
                    .terms
                    .iter()
                    .filter(|term| term.coefficient().bank_index().is_none())
                    .map(|term| (term.id(), term.coefficient()))
                    .collect();
                let c_init_recipe = lowered
                    .c_init
                    .and_then(|id| lowered.banked_recipe(id).cloned());
                let ids_before: Vec<TermId> = lowered.terms.iter().map(|t| t.id()).collect();
                let sources_before = lowered.sources.clone();

                let grouped =
                    group_coeff_layer(lowered).unwrap_or_else(|e| panic!("[{where_}] {e:?}"));

                // (c) Shape preserved: same terms, same ids, same sources.
                assert_eq!(
                    grouped.terms.iter().map(|t| t.id()).collect::<Vec<_>>(),
                    ids_before,
                    "[{where_}] grouping never adds, drops or reorders a term"
                );
                assert_eq!(
                    grouped.sources, sources_before,
                    "[{where_}] sources are untouched"
                );
                assert_eq!(grouped.regime, BwdRegime::Ext);
                assert!(
                    grouped.coefficients.windows(2).all(|w| w[0] < w[1]),
                    "[{where_}] the rebuilt bank must stay sorted and deduplicated"
                );
                assert!(
                    grouped.immediates.windows(2).all(|w| w[0] < w[1]),
                    "[{where_}] the immediate table must be ascending and deduplicated"
                );
                assert!(
                    grouped.immediates.len() <= LEAN_MAX_IMMEDIATES,
                    "[{where_}] immediate table over the wire cap"
                );
                assert!(
                    grouped.coefficients.len() + CoefficientRecipeId::RESERVED as usize
                        <= gkr_eval_isa::bwd::coeff::MAX_COEFFICIENT_ENCODINGS,
                    "[{where_}] rebuilt bank over the 13-bit coefficient field"
                );
                t.bank_after += grouped.coefficients.len();
                t.max_immediates = t.max_immediates.max(grouped.immediates.len());

                // (b) + (c) per group.
                let mut member_terms: BTreeMap<TermId, usize> = BTreeMap::new();
                for (index, group) in grouped.groups.iter().enumerate() {
                    assert!(
                        group.members.len() >= 2,
                        "[{where_}] group {index} has {} members, below the \
                         two-member floor",
                        group.members.len()
                    );
                    assert!(
                        group.members.windows(2).all(|w| w[0].term < w[1].term),
                        "[{where_}] group {index} members must be ascending by TermId"
                    );
                    assert!(
                        group.has_c0 || group.has_c2,
                        "[{where_}] group {index} feeds no side"
                    );
                    let core = grouped
                        .banked_recipe(group.core)
                        .unwrap_or_else(|| panic!("[{where_}] group {index} core id dangles"));
                    for member in &group.members {
                        assert!(
                            member_terms.insert(member.term, index).is_none(),
                            "[{where_}] {:?} is a member of two groups",
                            member.term
                        );
                        let term = grouped
                            .terms
                            .iter()
                            .find(|t| t.id() == member.term)
                            .unwrap_or_else(|| panic!("[{where_}] {:?} not in terms", member.term));
                        assert_eq!(
                            term.coefficient(),
                            group.core,
                            "[{where_}] a member's coefficient must be its group's core id"
                        );
                        let immediate = immediate_value(&grouped, member.immediate)
                            .unwrap_or_else(|| panic!("[{where_}] immediate id out of range"));
                        let original = originals
                            .get(&member.term)
                            .unwrap_or_else(|| panic!("[{where_}] a member had no bank recipe"));
                        assert_eq!(
                            &rescale(core, immediate),
                            original,
                            "[{where_}] core x immediate must reproduce {:?}'s original recipe",
                            member.term
                        );
                        // Group members are exactly the terms whose recipe was NOT
                        // a bare scalar and NOT a literal.
                        assert!(
                            factor(original).is_some(),
                            "[{where_}] a bare scalar must never become a member"
                        );
                    }
                    t.members += group.members.len();
                    t.max_members = t.max_members.max(group.members.len());
                }
                t.groups += grouped.groups.len();
                // Groups are MAXIMAL: one core is one group, never several atoms.
                let mut cores_seen: BTreeSet<CoefficientRecipeId> = BTreeSet::new();
                for group in &grouped.groups {
                    assert!(
                        cores_seen.insert(group.core),
                        "[{where_}] core {:?} appears in two groups — groups must be maximal",
                        group.core
                    );
                }
                if grouped.groups.is_empty() {
                    if li == 0 {
                        t.l0_without_groups.push(where_.clone());
                    }
                } else {
                    t.with_groups += 1;
                }

                // (c) Non-members keep their OWN recipe; literals stay literals.
                for term in &grouped.terms {
                    if member_terms.contains_key(&term.id()) {
                        continue;
                    }
                    match literals.get(&term.id()) {
                        Some(literal) => assert_eq!(
                            term.coefficient(),
                            *literal,
                            "[{where_}] a literal coefficient must not be rewritten"
                        ),
                        None => assert_eq!(
                            grouped.banked_recipe(term.coefficient()),
                            originals.get(&term.id()),
                            "[{where_}] a singleton must keep its own recipe"
                        ),
                    }
                }
                // §4.1: c_init is excluded from grouping, so its recipe survives.
                assert_eq!(
                    grouped
                        .c_init
                        .and_then(|id| grouped.banked_recipe(id).cloned()),
                    c_init_recipe,
                    "[{where_}] c_init must keep its own recipe"
                );
            }
            t
        })
        .collect();

    let sum = |f: fn(&Tally) -> usize| tallies.iter().map(f).sum::<usize>();
    let coordinates = sum(|t| t.coordinates);
    let groups = sum(|t| t.groups);
    let members = sum(|t| t.members);
    let max_members = tallies.iter().map(|t| t.max_members).max().unwrap_or(0);
    let max_immediates = tallies.iter().map(|t| t.max_immediates).max().unwrap_or(0);
    let l0_without_groups: Vec<String> = tallies
        .iter()
        .flat_map(|t| t.l0_without_groups.clone())
        .collect();
    println!(
        "grouping: {coordinates} Ext coordinates, {} bank recipes ({} factored / {} bare), \
         {groups} groups over {members} members (max {max_members} members, max \
         {max_immediates} immediates), bank {} -> {}, {} coordinates group",
        sum(|t| t.recipes),
        sum(|t| t.factored),
        sum(|t| t.bare),
        sum(|t| t.bank_before),
        sum(|t| t.bank_after),
        sum(|t| t.with_groups),
    );

    // Non-vacuity: the walk really ran, really factored, and really grouped.
    assert_eq!(
        coordinates,
        in_scope::LAYERS,
        "every layer with backward roots, Ext regime"
    );
    assert!(
        sum(|t| t.recipes) > 0,
        "the corpus must yield bank recipes to factor"
    );
    assert!(
        sum(|t| t.factored) > 0,
        "recipes with a non-trivial core must exist"
    );
    assert!(groups > 0, "the corpus must realize coefficient groups");
    assert!(
        members >= 2 * groups,
        "every group has at least two members"
    );
    assert_eq!(
        l0_without_groups,
        Vec::<String>::new(),
        "every L0 coordinate groups"
    );
    assert!(
        max_immediates <= LEAN_MAX_IMMEDIATES,
        "the immediate cap holds corpus-wide"
    );
    assert!(
        sum(|t| t.bank_after) < sum(|t| t.bank_before),
        "grouping collapses member recipes onto shared cores"
    );
}

// ── Grouped semantics ─────────────────────────────────────────────────────────

/// The four raw base-field limbs of an `Ext`, canonically reduced — what
/// "bit-identical" means for this field. Compared instead of the `Ext` values
/// themselves so a failure prints the diverging COORDINATE rather than an opaque
/// `Ext`, and so the claim is visibly about the representation and not about some
/// tolerance.
fn limbs(v: Ext) -> [u32; 4] {
    <Ext as FieldExtension<Bf>>::into_coeffs(v).map(|c| c.as_u32_reduced())
}

/// Design §4.6 on real cones: GROUPING IS VALUE-NEUTRAL. On every `Ext` coordinate
/// of the pinned corpus the group-aware interpreter reproduces the ungrouped
/// interpreter's `(acc_c0, acc_c2)` limb for limb.
///
/// This is the whole point of the grouped form. A group replaces one `Ext`
/// coefficient multiplication per member with one per GROUP plus a base-field
/// immediate per member — `k_m * v_m` summed becomes `core * Σ imm_m * v_m` — which
/// is the same field element only because field arithmetic is exact and
/// distributive. There is no rounding to absorb a mistake here: a dropped
/// immediate, a member evaluated twice (once plain, once in its group), a member
/// skipped without being served, or an accumulator side gated off by a wrong
/// `has_c0` / `has_c2` all show up as a different limb.
///
/// Both sides run the SAME resolver construction (`Pairs`): it evaluates whatever
/// recipe the layer's bank holds at the id it is asked for, and the grouped layer's
/// bank IS the rebuilt one, so the core ids resolve to their core recipes with no
/// special-casing. The recipes changed; the resolver contract did not.
///
/// Non-vacuity is asserted explicitly: the corpus must really produce groups, must
/// exercise BOTH immediate paths (the `±1` fast path and the banked-multiply path),
/// and must produce non-zero accumulators — `(0, 0) == (0, 0)` would prove nothing.
#[test]
fn grouped_semantics_match_ungrouped_bit_for_bit() {
    /// Rows sampled per coordinate: the two rows an affine source model treats as
    /// boundaries, plus one that is neither. `read_pair` is a pure function of
    /// `(place, row)` with no row bound, so the last row of a 2^20 trace is just
    /// another sample — what matters is that it is a different one.
    const SAMPLED: [usize; 3] = [0, 1, (1 << 20) - 1];

    #[derive(Default)]
    struct Tally {
        coordinates: usize,
        rows: usize,
        groups: usize,
        members: usize,
        /// Members whose immediate is `±1` — the add/sub fast path.
        literal_members: usize,
        /// Members whose immediate is a banked table entry — the multiply path.
        banked_members: usize,
        nonzero_c0: usize,
        nonzero_c2: usize,
    }

    let tallies: Vec<Tally> = FIXTURES
        .par_iter()
        .map(|name| {
            let mut t = Tally::default();
            for (li, layer, cross) in layers_with_bwd_roots(name) {
                let where_ = format!("{name} L{li} Ext");
                let d = distill(&layer, BwdRegime::Ext, &cross, None);
                let plain =
                    lower_coeff_layer(&layer, &d).unwrap_or_else(|e| panic!("[{where_}] {e:?}"));
                let grouped = group_coeff_layer(plain.clone())
                    .unwrap_or_else(|e| panic!("[{where_}] grouping: {e:?}"));
                t.coordinates += 1;
                t.groups += grouped.groups.len();
                for group in &grouped.groups {
                    t.members += group.members.len();
                    for member in &group.members {
                        match member.immediate.bank_index() {
                            None => t.literal_members += 1,
                            Some(_) => t.banked_members += 1,
                        }
                    }
                }

                let plain_pairs = Pairs { layer: &plain };
                let grouped_pairs = Pairs { layer: &grouped };
                for row in SAMPLED {
                    let (want_c0, want_c2) = interpret_coeff_layer(&plain, row, &plain_pairs)
                        .unwrap_or_else(|e| panic!("[{where_} row {row}] ungrouped: {e:?}"));
                    let (got_c0, got_c2) = interpret_coeff_layer(&grouped, row, &grouped_pairs)
                        .unwrap_or_else(|e| panic!("[{where_} row {row}] grouped: {e:?}"));
                    assert_eq!(
                        limbs(got_c0),
                        limbs(want_c0),
                        "[{where_} row {row}] acc_c0 diverges from the ungrouped layer"
                    );
                    assert_eq!(
                        limbs(got_c2),
                        limbs(want_c2),
                        "[{where_} row {row}] acc_c2 diverges from the ungrouped layer"
                    );
                    t.rows += 1;
                    t.nonzero_c0 += usize::from(want_c0 != Ext::ZERO);
                    t.nonzero_c2 += usize::from(want_c2 != Ext::ZERO);
                }
            }
            t
        })
        .collect();

    let sum = |f: fn(&Tally) -> usize| tallies.iter().map(f).sum::<usize>();
    let coordinates = sum(|t| t.coordinates);
    println!(
        "grouped semantics: {coordinates} Ext coordinates x {} rows, {} groups over {} members \
         ({} +-1 / {} banked immediates), non-zero acc_c0 on {} rows, acc_c2 on {}",
        SAMPLED.len(),
        sum(|t| t.groups),
        sum(|t| t.members),
        sum(|t| t.literal_members),
        sum(|t| t.banked_members),
        sum(|t| t.nonzero_c0),
        sum(|t| t.nonzero_c2),
    );

    assert_eq!(
        coordinates,
        in_scope::LAYERS,
        "every layer with backward roots, Ext regime"
    );
    assert_eq!(
        sum(|t| t.rows),
        coordinates * SAMPLED.len(),
        "every coordinate x row compared"
    );
    assert!(
        sum(|t| t.groups) > 0,
        "the corpus must realize groups, or this proves nothing"
    );
    assert!(
        sum(|t| t.literal_members) > 0,
        "the +-1 immediate fast path must be exercised by the corpus"
    );
    assert!(
        sum(|t| t.banked_members) > 0,
        "the banked-immediate multiply path must be exercised by the corpus"
    );
    assert_eq!(
        sum(|t| t.nonzero_c0),
        sum(|t| t.rows),
        "every sampled Ext row must carry a non-zero acc_c0"
    );
    assert_eq!(
        sum(|t| t.nonzero_c2),
        sum(|t| t.rows),
        "every sampled Ext row must carry a non-zero acc_c2"
    );
}

// ── The structural mul-count cross-check ──────────────────────────────────────

/// The two coefficient multiplications the eval loop pays, per `Ext` coordinate:
/// FULL `E4 x E4` and `BF x E4`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct MulCounts {
    full: u64,
    bf_imm: u64,
}

/// Full `E4 x E4` muls a SINGLETON record of `class` pays: its source products plus
/// its own coefficient mul, one per accumulator side it feeds (`C0LinearE4` 0 + 1,
/// `DualProductE4` 2 + 2). This is also the TERM-form cost of a grouped member, so
/// it is the denominator the grouping saving is measured against.
fn singleton_full_muls(class: u8) -> u64 {
    match class {
        0 => 1, // C0LinearE4: no product, one coefficient mul
        1 => 4, // DualProductE4: two products, two coefficient muls
        other => panic!("class {other} is not a live continuation term class"),
    }
}

/// Accumulator sides a member's immediate multiplies into — one `BF x E4` each,
/// and also the number of source products the member still pays in FULL width
/// minus one for `C0Linear`. Kept as its own function because the two counts read
/// it for different reasons.
fn active_sides(class: u8) -> u64 {
    match class {
        0 => 1, // C0LinearE4 feeds acc_c0 only
        1 => 2, // DualProductE4 feeds both
        other => panic!("class {other} is not a live continuation term class"),
    }
}

/// Full `E4 x E4` muls a grouped MEMBER record still pays: its source products
/// only — the coefficient mul moved to the group's header.
fn member_full_muls(class: u8) -> u64 {
    match class {
        0 => 0, // C0LinearE4 reads one projection, no product
        1 => 2, // DualProductE4 multiplies two projections, twice
        other => panic!("class {other} is not a live continuation term class"),
    }
}

/// Count the two mul columns off the WIRE: the committed program, walked by
/// [`decode_atoms`] exactly as the kernel's decoder walks it.
///
/// Header-driven, and deliberately so — this reads the same words the GPU reads,
/// so it cannot agree with the model by sharing a bug with it. A member's thirteen
/// coefficient bits are an [`ImmediateId`], and `±1` is the two reserved ids, which
/// is the only thing that decides whether a member pays a `BF x E4` at all.
fn wire_mul_counts(program: &LeanProgram) -> MulCounts {
    let atoms = decode_atoms(program, BwdRegime::Ext).expect("the committed program decodes");
    let mut counts = MulCounts::default();
    for atom in &atoms {
        match atom {
            LeanAtom::Term(term) => counts.full += singleton_full_muls(term.class),
            LeanAtom::Group {
                has_c0,
                has_c2,
                members,
                ..
            } => {
                counts.full += u64::from(*has_c0) + u64::from(*has_c2);
                for member in members {
                    counts.full += member_full_muls(member.class);
                    if ImmediateId(member.coeff).bank_index().is_some() {
                        counts.bf_imm += active_sides(member.class);
                    }
                }
            }
        }
    }
    counts
}

/// The same two numbers from the MODEL: `layer.groups` plus the terms no group
/// claims. Independent of the wire — no encode, no decode, no class numbering; it
/// reads `CoeffTerm` variants and `CoeffGroupMember::immediate` directly.
fn model_mul_counts(layer: &CoeffLayer) -> MulCounts {
    let class_of = |term: &CoeffTerm| -> u8 {
        match term {
            CoeffTerm::C0Linear { .. } => 0,
            CoeffTerm::DualProduct { .. } => 1,
            CoeffTerm::C2Product { .. } => {
                panic!("C2Product has no live continuation class, so an Ext layer has none")
            }
        }
    };
    let mut grouped = vec![false; layer.terms.len()];
    let mut counts = MulCounts::default();
    for group in &layer.groups {
        counts.full += u64::from(group.has_c0) + u64::from(group.has_c2);
        for member in &group.members {
            grouped[member.term.0 as usize] = true;
            let class = class_of(&layer.terms[member.term.0 as usize]);
            counts.full += member_full_muls(class);
            if member.immediate.bank_index().is_some() {
                counts.bf_imm += active_sides(class);
            }
        }
    }
    for term in &layer.terms {
        if !grouped[term.id().0 as usize] {
            counts.full += singleton_full_muls(class_of(term));
        }
    }
    counts
}

/// The TERM-form cost of the same layer: every term pays its products plus its own
/// coefficient mul, which is what the pre-grouping wire encoded. The denominator of
/// the saving, and the reason the ratio below is a magnitude check rather than a
/// tautology.
fn term_form_full_muls(layer: &CoeffLayer) -> u64 {
    layer
        .terms
        .iter()
        .map(|term| match term {
            CoeffTerm::C0Linear { .. } => 1,
            CoeffTerm::DualProduct { .. } => 4,
            CoeffTerm::C2Product { .. } => {
                panic!("C2Product has no live continuation class, so an Ext layer has none")
            }
        })
        .sum()
}

/// Design §6.5: the STRUCTURAL census cross-check. The mul work the committed
/// `Ext` wire realizes is the mul work the production grouping pass predicts, per
/// coordinate, and the numbers are golden-pinned.
///
/// Two independent counts of the same two quantities:
///
///   * [`wire_mul_counts`] walks the committed program with [`decode_atoms`] — the
///     bytes the GPU kernel decodes, header records and reinterpreted member
///     coefficient fields included; and
///   * [`model_mul_counts`] reads the grouped [`CoeffLayer`]'s `groups` and terms.
///
/// They agree only if the encoder placed every atom the transform formed, gave each
/// header the accumulator flags its members' classes imply, and reinterpreted
/// exactly the member records' coefficient fields — the three things a "the wire
/// says what the model meant" claim consists of. The golden pins then make it a
/// DRIFT detector: a lowering change that moves a coordinate's mul work shows up as
/// a specific coordinate and a specific delta rather than as a silent perf shift.
///
/// The archived fragment CSV (`seg_report.rs`'s `bwd_seg_fragment_coefficient_census`)
/// is motivation, NOT the oracle: it did not model the singleton rule (a
/// one-member core does not group), so its numbers are optimistic. The corpus
/// ratio asserted below is a band, not an equality, for exactly that reason — it
/// is a same-magnitude sanity check on the census that motivated the work, and a
/// wild ratio is a defect signal. (The wire censused here is the ARTIFACT's:
/// groups are maximal, one per core; `seg_lower`'s deal-time chop repays cores
/// per chunk at launch time and is deliberately outside this census.)
#[test]
fn grouped_wire_realizes_predicted_mul_counts() {
    /// `(circuit, layer, full E4xE4, BF x E4)` for every `Ext` coordinate, in
    /// `(circuit, layer)` order. Golden — from one instrumented run.
    ///
    /// The shape to read off it: `BF x E4` is concentrated at L0 and is ZERO on
    /// every deeper layer of every circuit but `unsigned_mul_div` L1. That is a
    /// measurement, and what it says is that outside L0 every member's immediate
    /// factors out as `±1` — the reserved-literal path (§4.4), which costs no
    /// multiply at all, so those coordinates' grouping is pure saving.
    #[rustfmt::skip]
    const GOLDEN: &[(&str, usize, u64, u64)] = &[
        ("add_sub_lui_auipc_mop_layout_gkr.json", 0, 336, 56),
        ("add_sub_lui_auipc_mop_layout_gkr.json", 1, 53, 0),
        ("add_sub_lui_auipc_mop_layout_gkr.json", 2, 33, 0),
        ("add_sub_lui_auipc_mop_layout_gkr.json", 3, 18, 0),
        ("bigint_with_extended_control_layout_gkr.json", 0, 3691, 568),
        ("bigint_with_extended_control_layout_gkr.json", 1, 385, 0),
        ("bigint_with_extended_control_layout_gkr.json", 2, 213, 0),
        ("bigint_with_extended_control_layout_gkr.json", 3, 113, 0),
        ("bigint_with_extended_control_layout_gkr.json", 4, 61, 0),
        ("bigint_with_extended_control_layout_gkr.json", 5, 39, 0),
        ("blake2_g_function_layout_gkr.json", 0, 266, 10),
        ("blake2_g_function_layout_gkr.json", 1, 121, 0),
        ("blake2_g_function_layout_gkr.json", 2, 63, 0),
        ("blake2_g_function_layout_gkr.json", 3, 33, 0),
        ("blake2_g_function_layout_gkr.json", 4, 29, 0),
        ("blake2_with_extended_control_layout_gkr.json", 0, 3200, 111),
        ("blake2_with_extended_control_layout_gkr.json", 1, 833, 0),
        ("blake2_with_extended_control_layout_gkr.json", 2, 417, 0),
        ("blake2_with_extended_control_layout_gkr.json", 3, 217, 0),
        ("blake2_with_extended_control_layout_gkr.json", 4, 111, 0),
        ("blake2_with_extended_control_layout_gkr.json", 5, 53, 0),
        ("blake2_with_extended_control_layout_gkr.json", 6, 39, 0),
        ("blake2_with_extended_control_layout_gkr.json", 7, 16, 0),
        ("inits_and_teardowns_preprocessed_layout_gkr.json", 0, 878, 0),
        ("inits_and_teardowns_preprocessed_layout_gkr.json", 1, 32, 0),
        ("inits_and_teardowns_preprocessed_layout_gkr.json", 2, 16, 0),
        ("inits_and_teardowns_preprocessed_layout_gkr.json", 3, 8, 0),
        ("jump_branch_slt_layout_gkr.json", 0, 316, 38),
        ("jump_branch_slt_layout_gkr.json", 1, 55, 0),
        ("jump_branch_slt_layout_gkr.json", 2, 41, 0),
        ("jump_branch_slt_layout_gkr.json", 3, 18, 0),
        ("keccak_special5_layout_gkr.json", 0, 3378, 718),
        ("keccak_special5_layout_gkr.json", 1, 215, 0),
        ("keccak_special5_layout_gkr.json", 2, 109, 0),
        ("keccak_special5_layout_gkr.json", 3, 59, 0),
        ("keccak_special5_layout_gkr.json", 4, 31, 0),
        ("keccak_special5_layout_gkr.json", 5, 16, 0),
        ("mem_subword_only_layout_gkr.json", 0, 202, 24),
        ("mem_subword_only_layout_gkr.json", 1, 92, 0),
        ("mem_subword_only_layout_gkr.json", 2, 41, 0),
        ("mem_subword_only_layout_gkr.json", 3, 18, 0),
        ("mem_word_only_layout_gkr.json", 0, 149, 24),
        ("mem_word_only_layout_gkr.json", 1, 62, 0),
        ("mem_word_only_layout_gkr.json", 2, 41, 0),
        ("mem_word_only_layout_gkr.json", 3, 18, 0),
        ("shift_binop_layout_gkr.json", 0, 271, 12),
        ("shift_binop_layout_gkr.json", 1, 61, 0),
        ("shift_binop_layout_gkr.json", 2, 35, 0),
        ("shift_binop_layout_gkr.json", 3, 26, 0),
        ("unified_reduced_machine_layout_gkr.json", 0, 1324, 136),
        ("unified_reduced_machine_layout_gkr.json", 1, 93, 0),
        ("unified_reduced_machine_layout_gkr.json", 2, 55, 0),
        ("unified_reduced_machine_layout_gkr.json", 3, 36, 0),
        ("unsigned_mul_div_layout_gkr.json", 0, 252, 12),
        ("unsigned_mul_div_layout_gkr.json", 1, 175, 34),
        ("unsigned_mul_div_layout_gkr.json", 2, 45, 0),
        ("unsigned_mul_div_layout_gkr.json", 3, 34, 0),
    ];

    let measured: Vec<(&str, usize, u64, u64, u64)> = FIXTURES
        .par_iter()
        .flat_map_iter(|name| {
            layers_with_bwd_roots(name).map(move |(li, canonical, cross)| {
                let where_ = format!("{name} L{li} Ext");
                // The PRODUCTION chain, both sides: the artifact's program is the
                // committed wire, and `lower_lean_layer` is the grouped model it
                // was encoded from.
                let artifact =
                    compile_lean_coordinate(name, li, &canonical, &cross, BwdRegime::Ext)
                        .unwrap_or_else(|e| panic!("[{where_}] compile: {e:?}"));
                let (layer, _) = lower_lean_layer(&canonical, &cross, BwdRegime::Ext)
                    .unwrap_or_else(|e| panic!("[{where_}] lower: {e:?}"));

                let wire = wire_mul_counts(&artifact.program);
                let model = model_mul_counts(&layer);
                assert_eq!(
                    wire, model,
                    "[{where_}] the committed wire's mul work is not the grouped model's",
                );
                assert!(
                    !layer.groups.is_empty() || wire.bf_imm == 0,
                    "[{where_}] a group-free coordinate cannot pay a BF immediate",
                );
                (
                    *name,
                    li,
                    wire.full,
                    wire.bf_imm,
                    term_form_full_muls(&layer),
                )
            })
        })
        .collect();

    let mut rows = measured.clone();
    rows.sort_by_key(|(name, layer, ..)| (*name, *layer));
    let corpus_full: u64 = rows.iter().map(|(.., full, _, _)| full).sum();
    let corpus_bf: u64 = rows.iter().map(|(.., bf, _)| bf).sum();
    let corpus_term: u64 = rows.iter().map(|(.., term)| term).sum();
    let ratio = corpus_full as f64 / corpus_term as f64;
    println!(
        "[mul cross-check] {} Ext coordinates: full E4xE4 {corpus_term} (term form) -> \
         {corpus_full} grouped ({:.4} of term form) plus {corpus_bf} BFxE4",
        rows.len(),
        ratio,
    );

    assert_eq!(
        rows.len(),
        in_scope::LAYERS,
        "every layer with backward roots, Ext regime"
    );
    assert_eq!(
        rows.iter()
            .map(|(n, l, f, b, _)| (*n, *l, *f, *b))
            .collect::<Vec<_>>(),
        GOLDEN.to_vec(),
        "a coordinate's realized mul work drifted from its pin",
    );
    // Census-magnitude sanity (§6.5): the grouped form's full-mul count lands where
    // the motivating census said it would. A band, not an equality — the singleton
    // rule costs muls the archived CSV did not model.
    assert!(
        (0.72..=0.76).contains(&ratio),
        "corpus full-mul ratio {ratio:.4} is outside the censused 0.72-0.76 band; investigate \
         before re-pinning",
    );
    assert!(
        corpus_bf > 0,
        "the BF-immediate column must be live, or the grouping saved nothing"
    );
}
