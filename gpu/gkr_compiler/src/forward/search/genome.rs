//! Genome representation for the offline forward search.
//!
//! A `Genome` is a flat pair of real-valued "gene" vectors the search mutates
//! and [`super::decode`] turns into a concrete `(order, SiteDecisions)`
//! candidate for [`super::scorer::score`] to compile-and-measure. Shape is
//! See [`super::structure`] for the DAG-native genome shape.

/// One real-valued key per relation unit ([`super::structure::relation_units`]) —
/// decoded to a unit execution order by [`super::decode::decode_unit_order`].
/// One real-valued priority gene per structural demand site
/// ([`super::structure::enumerate_sites`]), read by the emitter via
/// `fwd::compile::decisions::SiteDecisions`.
#[derive(Clone, Debug, PartialEq)]
pub struct Genome {
    pub root_order_key: Vec<f64>,
    pub cache_priority: Vec<f64>,
}

impl Genome {
    /// The "do nothing clever" seed genome: units keyed by ascending index (so
    /// [`super::decode::decode_unit_order`] returns the identity permutation —
    /// units decode in first-occurrence order, matching `relation_units`'
    /// documented order), every cache-priority gene at the neutral bias `0.0`.
    pub fn neutral(n_units: usize, n_sites: usize) -> Self {
        let denom = n_units.max(1) as f64;
        Self {
            root_order_key: (0..n_units).map(|i| i as f64 / denom).collect(),
            cache_priority: vec![0.0; n_sites],
        }
    }
}

/// Cache-priority genes are symmetric biases in `[-1, 1]`.
pub const CACHE_PRIORITY_BOUND: f64 = 1.0;

pub(crate) fn clamp_bias(value: f64) -> f64 {
    value.clamp(-CACHE_PRIORITY_BOUND, CACHE_PRIORITY_BOUND)
}

/// Normalization invariant maintained by the search: finite order keys in
/// `[0, 1]` and finite bias genes in `[-1, 1]`. Panics on violation.
pub fn assert_normalized_genome(genome: &Genome) {
    for &key in &genome.root_order_key {
        assert!(
            key.is_finite() && (0.0..=1.0).contains(&key),
            "root_order_key must be finite and in [0, 1], got {key}"
        );
    }
    for &gene in &genome.cache_priority {
        assert!(
            gene.is_finite() && (-CACHE_PRIORITY_BOUND..=CACHE_PRIORITY_BOUND).contains(&gene),
            "bias genes must be finite and in [-1, 1], got {gene}"
        );
    }
}
