//! The coverage proof cutover blocker 4 asks for, and the device-vs-host gate.
//!
//! [`super::seg_coeff_eval`] can only exist if no compiled coefficient recipe needs
//! more than the device monomial holds: two challenge factors with `u8` exponents,
//! times a `u16` batching power. Those are empirical properties of the corpus, not of
//! any type, so they are measured here over every coordinate of all twelve committed
//! layouts — and the numbers are printed, so a future compiler change that moves them
//! is visible rather than merely non-fatal.
//!
//! [`seg_coeff_eval_batching_shape_survey`] is the measurement that decided the
//! format: it is what showed the flat lineage's monomial one factor short, which is
//! why the seg lineage has its own evaluator.
//!
//! The parity gate is the other half: the translated tables, evaluated by the seg
//! evaluator writing through the bank symbol's own address, must reproduce
//! `NormalizedCoefficientRecipe::evaluate` exactly. Anything less makes the bank a
//! source of wrong proofs that no other gate would catch — the parity ladder stages
//! SYNTHETIC bank values, so it cannot see a translation error at all.

use era_cudart::memory::{memory_copy, memory_copy_async};
use era_cudart::slice::DeviceSlice;
use gkr_eval_isa::bwd::coeff::model::{CoefficientRecipeId, NormalizedCoefficientRecipe};

use super::seg::bwd_seg_coeff_bank_device_ptr;
use super::seg_coeff_eval::{
    build_seg_coeff_eval_tables, schedule_bwd_seg_coeff_bank_fill, SegChallengeSlab,
    BWD_SEG_CHALLENGE_SLOTS, BWD_SEG_COEFF_MAX_MONOMIALS,
};
use super::seg_compile::{
    lean_layer, seg_coordinate_layers, seg_ext, short_name, SEG_CORPUS_LAYOUTS,
};
use super::seg_desc::BWD_SEG_CONST_BANK;
use crate::allocator::tracker::AllocationPlacement;
use crate::primitives::field::E4;
use crate::prover::test_utils::make_test_context;
use crate::prover::{ProverContext, ProverContextConfig};
use crate::upstream::{BwdRegime, Field};

/// A deterministic, non-degenerate slab: four independent base digits per slot, so a
/// slot confusion or a BF/E4 width error cannot pass by coincidence.
fn census_slab() -> SegChallengeSlab {
    let mut slab = SegChallengeSlab::default();
    for (index, value) in slab.values.iter_mut().enumerate() {
        *value = seg_ext(0xc4a1, index as u32, 0);
    }
    slab
}

/// Every coordinate of the corpus: `(circuit, layer, regime)`.
fn corpus_coordinates() -> Vec<(&'static str, usize, BwdRegime)> {
    let mut out = Vec::new();
    for circuit in SEG_CORPUS_LAYOUTS {
        for layer in seg_coordinate_layers(circuit) {
            for regime in [BwdRegime::R0, BwdRegime::Ext] {
                out.push((circuit, layer, regime));
            }
        }
    }
    out
}

/// THE coverage proof: every compiled coefficient recipe in the corpus fits the
/// device evaluator's monomial, and by how much margin.
///
/// Not `#[ignore]`d and not GPU-bound: it is the gate that says the translation is
/// total over the corpus, and a cutover rests on it.
#[test]
fn seg_coeff_eval_covers_the_corpus() {
    let coordinates = corpus_coordinates();
    assert!(
        coordinates.len() >= 100,
        "the corpus census must walk the whole corpus, not a subset: {} coordinates",
        coordinates.len()
    );

    let mut max_distinct = 0usize;
    let mut max_exponent = 0u32;
    let mut max_batch_power = 0u32;
    let mut max_monomials_per_recipe = 0usize;
    let mut max_bank = 0usize;
    let mut max_monomial_table = 0usize;
    let mut total_bank = 0usize;
    let mut slots_seen = [false; BWD_SEG_CHALLENGE_SLOTS];
    let mut widest = String::new();

    for (circuit, layer, regime) in &coordinates {
        let compiled = lean_layer(circuit, *layer, *regime);
        let label = format!("{} L{layer} {regime:?}", short_name(circuit));
        let tables = build_seg_coeff_eval_tables(&compiled.coefficients).unwrap_or_else(|error| {
            panic!(
                "{label}: {} coefficient recipes do not fit the device evaluator: {error:?}",
                compiled.coefficients.len()
            )
        });
        let census = &tables.census;
        if census.max_distinct_challenges > max_distinct {
            max_distinct = census.max_distinct_challenges;
            widest = label.clone();
        }
        max_exponent = max_exponent.max(census.max_exponent);
        max_batch_power = max_batch_power.max(census.max_batch_power);
        max_monomials_per_recipe = max_monomials_per_recipe.max(census.max_monomials_per_recipe);
        max_bank = max_bank.max(census.coefficients);
        max_monomial_table = max_monomial_table.max(census.monomials);
        total_bank += census.coefficients;
        for slot in &census.referenced_slots {
            slots_seen[usize::from(*slot)] = true;
        }
    }

    let referenced: Vec<usize> = (0..BWD_SEG_CHALLENGE_SLOTS)
        .filter(|slot| slots_seen[*slot])
        .collect();
    eprintln!(
        "[seg-coeff-eval census] {} coordinates / {} layouts | bank slots: max {max_bank}, \
         total {total_bank} | max distinct challenges per product: {max_distinct} (at {widest}) | \
         max non-batching exponent: {max_exponent} | max batching power: {max_batch_power} | \
         max monomials per recipe: {max_monomials_per_recipe} | max monomial table: \
         {max_monomial_table} | referenced slab slots: {referenced:?}",
        coordinates.len(),
        SEG_CORPUS_LAYOUTS.len(),
    );

    // The coverage property itself. A future compiler change that emits a
    // three-challenge product fails HERE, at the census, rather than at whichever
    // coordinate a cutover happens to compile first.
    assert!(
        max_distinct <= 2,
        "the device monomial holds two challenge factors; the corpus needs {max_distinct} \
         (widest at {widest}). The translation would have to grow a split, and the CUDA \
         monomial an extra factor pair."
    );
    assert!(
        max_exponent <= u32::from(u8::MAX),
        "non-batching monomial exponents are u8; the corpus needs {max_exponent}. The \
         batching power has its own u16 field — an exponent this large is a DIFFERENT \
         challenge needing the same treatment."
    );
    assert!(
        max_batch_power <= u32::from(u16::MAX),
        "the batching power is u16; the corpus needs {max_batch_power}"
    );
    assert!(
        max_monomials_per_recipe <= usize::from(u16::MAX),
        "a recipe's monomial count is u16; the corpus needs {max_monomials_per_recipe}"
    );
    assert!(
        max_bank <= BWD_SEG_CONST_BANK,
        "the constant bank holds {BWD_SEG_CONST_BANK} slots; the corpus needs {max_bank}"
    );
    assert!(
        max_monomial_table <= BWD_SEG_COEFF_MAX_MONOMIALS,
        "the inline descriptor's monomial array holds {BWD_SEG_COEFF_MAX_MONOMIALS}; the \
         corpus needs {max_monomial_table}. The tables ride the by-value parameter space, so \
         the array cannot simply grow — the answer would be the device-pointer companion."
    );
    eprintln!(
        "[seg-coeff-eval census] inline capacity: {max_monomial_table} of \
         {BWD_SEG_COEFF_MAX_MONOMIALS} monomials ({:.0}% headroom), {max_bank} of \
         {BWD_SEG_CONST_BANK} bank slots",
        100.0 * (BWD_SEG_COEFF_MAX_MONOMIALS - max_monomial_table) as f64
            / BWD_SEG_COEFF_MAX_MONOMIALS as f64,
    );
}

/// Diagnostic: the batching-power shape the translation has to hold.
#[test]
fn seg_coeff_eval_batching_shape_survey() {
    use crate::upstream::{ChallengeKey, ChallengePower};
    let mut max_total = 0u32;
    let mut max_residual = 0u32;
    let mut max_others = 0usize;
    let mut max_others_with_residual = 0usize;
    let mut worst = String::new();
    let mut residual_buckets = [0usize; 5];
    for (circuit, layer, regime) in corpus_coordinates() {
        let label = format!("{} L{layer} {regime:?}", short_name(circuit));
        for recipe in &lean_layer(circuit, layer, regime).coefficients {
            let mut per_product = Vec::new();
            for product in &recipe.terms {
                let mut beta = 0u32;
                let mut others = std::collections::BTreeSet::new();
                for challenge in &product.challenges {
                    let power = match challenge.0.power {
                        ChallengePower::One => 1u32,
                        ChallengePower::Static(p) => p,
                    };
                    if challenge.0.key == ChallengeKey::ClaimBatching {
                        beta += power;
                    } else {
                        others.insert(format!("{:?}", challenge.0.key));
                    }
                }
                per_product.push((beta, others.len()));
            }
            let min_beta = per_product.iter().map(|(b, _)| *b).min().unwrap_or(0);
            for (beta, others) in &per_product {
                let residual = beta - min_beta;
                max_total = max_total.max(*beta);
                max_others = max_others.max(*others);
                if residual > max_residual {
                    max_residual = residual;
                    worst = label.clone();
                }
                if residual > 0 {
                    max_others_with_residual = max_others_with_residual.max(*others);
                }
                let bucket = match residual {
                    0 => 0,
                    1..=255 => 1,
                    256..=510 => 2,
                    511..=65535 => 3,
                    _ => 4,
                };
                residual_buckets[bucket] += 1;
            }
        }
    }
    eprintln!(
        "[seg-coeff-eval survey] max total beta exponent {max_total} | max residual after the \
         per-recipe min lift {max_residual} (at {worst}) | max distinct non-beta challenges per \
         product {max_others} | max non-beta challenges alongside a nonzero residual \
         {max_others_with_residual} | residual buckets [0, 1..255, 256..510, 511..65535, more] = \
         {residual_buckets:?}"
    );
}

/// Which challenge KINDS the corpus's coefficient recipes actually name.
///
/// The slab has a slot per kind, but a production caller only owes a VALUE for the
/// slots that are read. This is how it knows which — and it is a pin: a kind that
/// starts appearing (or stops) changes the staging contract, so it should change
/// this list rather than pass silently.
#[test]
fn seg_coeff_eval_names_the_challenge_kinds_the_corpus_uses() {
    let mut seen = std::collections::BTreeSet::new();
    for (circuit, layer, regime) in corpus_coordinates() {
        for recipe in &lean_layer(circuit, layer, regime).coefficients {
            for product in &recipe.terms {
                for challenge in &product.challenges {
                    seen.insert(format!("{:?}", challenge.0.key));
                }
            }
        }
    }
    eprintln!("[seg-coeff-eval census] challenge kinds in corpus coefficient recipes: {seen:?}");
    assert!(
        !seen.is_empty(),
        "the corpus's coefficient recipes must reference challenges at all, or the whole \
         device-evaluation path is unnecessary"
    );
}

// ── The device gate ──────────────────────────────────────────────────────────

const SEG_COEFF_ARENA_BYTES: usize = 1 << 30;

fn make_coeff_context() -> ProverContext {
    let block_log = ProverContextConfig::default().allocator_block_log_size;
    make_test_context((SEG_COEFF_ARENA_BYTES >> block_log).max(1), 64)
}

/// The production fill path, end to end, against the CPU oracle.
///
/// Fills the REAL `ab_gkr_bwd_seg_coeff_bank` through its symbol address — the same
/// write the incumbent's `schedule_flat_eval_recipes` performs on its own bank — so
/// the gate covers the symbol write, not just the arithmetic. Every constant-mode
/// launch in this suite re-stages the bank before it reads it, so leaving values
/// behind here cannot affect another test.
#[test]
#[ignore = "GPU"]
fn seg_coeff_eval_matches_the_host_oracle() {
    let context = make_coeff_context();
    let stream = context.get_exec_stream();
    let slab = census_slab();

    let mut device_slab = context
        .alloc::<E4>(BWD_SEG_CHALLENGE_SLOTS, AllocationPlacement::BestFit)
        .expect("challenge slab");
    memory_copy_async(&mut device_slab[..], slab.as_slice(), stream).expect("slab H2D");

    // Four shapes on purpose: an R0 coordinate, an Ext coordinate (whose bank is the
    // grouped form's core recipes), a wide delegation bank, and — last, because it is
    // the shape that broke every narrower format — blake2 L0 Ext, which carries the
    // corpus's widest batching polynomial (297 monomials) and its largest bank.
    let cases: [(&'static str, usize, BwdRegime); 4] = [
        (SEG_CORPUS_LAYOUTS[0], 0, BwdRegime::R0),
        (SEG_CORPUS_LAYOUTS[0], 0, BwdRegime::Ext),
        (SEG_CORPUS_LAYOUTS[1], 0, BwdRegime::Ext),
        (SEG_CORPUS_LAYOUTS[3], 0, BwdRegime::Ext),
    ];

    for (circuit, layer, regime) in cases {
        let label = format!("{} L{layer} {regime:?}", short_name(circuit));
        let compiled = lean_layer(circuit, layer, regime);
        let tables =
            build_seg_coeff_eval_tables(&compiled.coefficients).expect("the corpus census passed");
        let payload = tables.census.coefficients;
        assert!(
            payload <= BWD_SEG_CONST_BANK,
            "{label}: {payload} bank slots exceed the constant bank"
        );

        // No upload and no device allocation: the tables ride the parameter space.
        schedule_bwd_seg_coeff_bank_fill(
            &tables,
            device_slab.as_ptr(),
            bwd_seg_coeff_bank_device_ptr(),
            stream,
        )
        .expect("bank fill launch");

        let mut got = vec![E4::ZERO; payload];
        // SAFETY: the bank symbol is provisioned for `BWD_SEG_CONST_BANK` E4s and
        // `payload` of them were just written; this is a synchronous read-back of
        // exactly that prefix, after the fill on the same stream.
        let bank =
            unsafe { DeviceSlice::from_raw_parts_mut(bwd_seg_coeff_bank_device_ptr(), payload) };
        stream.synchronize().expect("fill completion");
        memory_copy(&mut got, bank).expect("bank D2H");

        let expected = host_bank(&compiled.coefficients, &slab);
        assert_eq!(
            got.len(),
            expected.len(),
            "{label}: bank length must be reserved-inclusive"
        );
        for (index, (got, expected)) in got.iter().zip(expected.iter()).enumerate() {
            assert_eq!(
                got, expected,
                "{label}: bank slot {index} diverged — the device evaluation of the \
                 translated recipe must be bit-identical to NormalizedCoefficientRecipe::evaluate"
            );
        }
        eprintln!(
            "[seg-coeff-eval] {label}: {payload} bank slots bit-identical ({} monomials)",
            tables.census.monomials
        );
    }
}

/// The CPU oracle: the reserved literals then every recipe, evaluated by the model's
/// own `evaluate` against the slab resolver. Deliberately not a reimplementation —
/// the whole point is that the device reproduces THIS.
fn host_bank(recipes: &[NormalizedCoefficientRecipe], slab: &SegChallengeSlab) -> Vec<E4> {
    let mut out = Vec::with_capacity(2 + recipes.len());
    for literal in [CoefficientRecipeId::ONE, CoefficientRecipeId::NEG_ONE] {
        out.push(literal.literal().expect("a reserved literal"));
    }
    out.extend(recipes.iter().map(|recipe| recipe.evaluate(slab)));
    out
}

// ── publish-backing census (cutover blocker 3) ───────────────────────────────

/// Which sources the seg VM PUBLISHES, and whether production storage already
/// has fold backing for each — the measurement cutover blocker 3 needs.
///
/// `assign_class` (`seg_lower.rs`) is the policy: a `Bf` origin publishes at
/// delta >= 3 (or at 2 under `D2Policy::Materialize`), an `E4` origin at any
/// delta > 0, and a `Procedural` origin at delta >= `BWD_COEFF_PUBLISH_TARGET_DEPTH`
/// — the same depth as the BF folds, which is what makes "publish procedural
/// alongside BF" already true rather than a change.
///
/// The census question is therefore not *whether* procedural sources publish
/// (they do) but whether production has somewhere to put them. It does, and by
/// the same mechanism as for real columns: `storage/ops.rs`'s
/// `plan_base_source_for_round_{1,2}` allocate a fold buffer keyed by the
/// address for `GKRAddress::VirtualSetup` too, with a NULL read pointer and a
/// `GpuBaseFieldSourceKind` tag telling the kernel to synthesize. So this
/// counts what has to be bound, per origin family, rather than what is missing.
#[test]
fn seg_publish_backing_census() {
    use gkr_eval_isa::bwd::source::OriginLeaf;
    use crate::upstream::ReadPlace;

    let coordinates = corpus_coordinates();
    assert!(
        coordinates.len() >= 100,
        "must walk the whole corpus: {} coordinates",
        coordinates.len()
    );

    let mut virtual_sources = 0usize;
    let mut real_sources = 0usize;
    let mut by_place = std::collections::BTreeMap::<&str, usize>::new();
    let mut by_vs_kind = std::collections::BTreeMap::<String, usize>::new();
    let mut max_virtual_in_one = 0usize;
    let mut coords_with_virtual = 0usize;
    let mut widest_virtual = String::new();

    for (circuit, layer, regime) in &coordinates {
        let compiled = lean_layer(circuit, *layer, *regime);
        let label = format!("{} L{layer} {regime:?}", short_name(circuit));
        let mut virtual_here = 0usize;
        for source in &compiled.sources {
            match &source.origin {
                OriginLeaf::VirtualSetup { kind } => {
                    virtual_sources += 1;
                    virtual_here += 1;
                    *by_vs_kind.entry(format!("{kind:?}")).or_default() += 1;
                }
                OriginLeaf::Read(place) => {
                    real_sources += 1;
                    let name = match place {
                        ReadPlace::BaseLayerMemory { .. } => "BaseLayerMemory",
                        ReadPlace::BaseLayerWitness { .. } => "BaseLayerWitness",
                        ReadPlace::Setup { .. } => "Setup",
                        ReadPlace::Scratch { .. } => "Scratch",
                        ReadPlace::LayerOutput { .. } => "LayerOutput",
                        ReadPlace::CacheOutput { .. } => "CacheOutput",
                    };
                    *by_place.entry(name).or_default() += 1;
                }
            }
        }
        if virtual_here > 0 {
            coords_with_virtual += 1;
        }
        if virtual_here > max_virtual_in_one {
            max_virtual_in_one = virtual_here;
            widest_virtual = label;
        }
    }

    eprintln!(
        "[publish-census] {} coordinates: {real_sources} real + {virtual_sources} virtual sources",
        coordinates.len()
    );
    eprintln!("[publish-census] real by ReadPlace: {by_place:?}");
    eprintln!("[publish-census] virtual by kind:   {by_vs_kind:?}");
    eprintln!(
        "[publish-census] coordinates with >=1 virtual source: {coords_with_virtual} of {}; \
         widest = {widest_virtual} ({max_virtual_in_one})",
        coordinates.len()
    );

    // The policy constant this census is about. If the publish depth ever moves,
    // the census's framing moves with it.
    assert_eq!(
        gkr_eval_isa::bwd::source::VIRTUAL_SETUP_MATERIALIZE_DEPTH,
        super::seg_desc::BWD_COEFF_PUBLISH_TARGET_DEPTH,
        "procedural and BF-origin publishes must share one depth"
    );
}
