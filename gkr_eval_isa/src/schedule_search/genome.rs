//! Genome representation (Task 6 promotion of the test-only metaheuristic
//! prototype's `Genome`, `gkr_eval_isa/tests/s3_planner/metaheuristic.rs:198`).
//!
//! A `Genome` is a flat pair of real-valued "gene" vectors the search mutates
//! and [`super::decode`] turns into a concrete `(order, SiteDecisions)`
//! candidate for [`super::scorer::score`] to compile-and-measure. Shape is
//! unchanged from the prototype; only the surrounding machinery (OracleInstance,
//! demand-site simulation) is gone — see `super::structure` for the DagLayer-
//! native replacement of "how many genes do I need".

/// One real-valued key per relation unit ([`super::structure::relation_units`]) —
/// decoded to a unit execution order by [`super::decode::decode_order`].
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

    /// A single gene perturbed by `delta`: `index` addresses `root_order_key`
    /// first (clamped to `[0,1]`), then `cache_priority` (clamped to
    /// `[-CACHE_PRIORITY_BOUND, CACHE_PRIORITY_BOUND]`) — mirrors the
    /// prototype's `perturb_one_gene` (metaheuristic.rs:1748).
    pub fn perturb_one_gene(&self, index: usize, delta: f64) -> Genome {
        let mut out = self.clone();
        if index < out.root_order_key.len() {
            out.root_order_key[index] = (out.root_order_key[index] + delta).clamp(0.0, 1.0);
            return out;
        }
        let index = index - out.root_order_key.len();
        if index < out.cache_priority.len() {
            out.cache_priority[index] = clamp_bias(out.cache_priority[index] + delta);
            return out;
        }
        panic!("gene index {index} out of range for genome with {} order keys + {} sites",
            out.root_order_key.len(), out.cache_priority.len());
    }

    /// Total gene count (`root_order_key.len() + cache_priority.len()`) — the
    /// valid range for `perturb_one_gene`'s `index`.
    pub fn gene_count(&self) -> usize {
        self.root_order_key.len() + self.cache_priority.len()
    }
}

/// Cache-priority genes are symmetric biases in `[-1, 1]` (mirrors the
/// prototype's `clamp_bias`, metaheuristic.rs:1744, and its
/// `assert_normalized_genome` bound — the search's `LOCAL_BIAS_STEP` gradations
/// are calibrated against this range).
pub const CACHE_PRIORITY_BOUND: f64 = 1.0;

pub(crate) fn clamp_bias(value: f64) -> f64 {
    value.clamp(-CACHE_PRIORITY_BOUND, CACHE_PRIORITY_BOUND)
}

/// Normalization invariant the search maintains (prototype's
/// `assert_normalized_genome`, metaheuristic.rs:1729): order keys finite in
/// `[0, 1]`, bias genes finite in `[-1, 1]`. Panics on violation.
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn neutral_produces_ascending_keys_and_zero_priorities() {
        let g = Genome::neutral(3, 2);
        assert_eq!(g.root_order_key.len(), 3);
        assert!(g.root_order_key.windows(2).all(|w| w[0] < w[1]));
        assert_eq!(g.cache_priority, vec![0.0, 0.0]);
    }

    #[test]
    fn neutral_with_zero_units_does_not_divide_by_zero() {
        let g = Genome::neutral(0, 0);
        assert!(g.root_order_key.is_empty());
        assert!(g.cache_priority.is_empty());
    }

    #[test]
    fn perturb_one_gene_walks_order_then_cache_priority() {
        let g = Genome::neutral(2, 2);
        let a = g.perturb_one_gene(0, 0.1);
        assert_eq!(a.root_order_key[0], g.root_order_key[0] + 0.1);
        assert_eq!(a.cache_priority, g.cache_priority);

        let b = g.perturb_one_gene(2, 0.5);
        assert_eq!(b.root_order_key, g.root_order_key);
        assert_eq!(b.cache_priority[0], 0.5);
    }

    #[test]
    fn perturb_one_gene_clamps_bias_to_symmetric_unit_range() {
        let g = Genome::neutral(1, 1);
        let a = g.perturb_one_gene(1, 5.0);
        assert_eq!(a.cache_priority[0], CACHE_PRIORITY_BOUND);
        let b = g.perturb_one_gene(1, -5.0);
        assert_eq!(b.cache_priority[0], -CACHE_PRIORITY_BOUND);
        assert_normalized_genome(&a);
        assert_normalized_genome(&b);
    }

    #[test]
    #[should_panic(expected = "must be finite")]
    fn assert_normalized_rejects_nan_order_key() {
        let mut g = Genome::neutral(1, 0);
        g.root_order_key[0] = f64::NAN;
        assert_normalized_genome(&g);
    }

    #[test]
    fn perturb_one_gene_clamps_order_key_to_unit_interval() {
        let g = Genome::neutral(1, 0);
        let a = g.perturb_one_gene(0, 10.0);
        assert_eq!(a.root_order_key[0], 1.0);
        let b = g.perturb_one_gene(0, -10.0);
        assert_eq!(b.root_order_key[0], 0.0);
    }

    #[test]
    #[should_panic(expected = "out of range")]
    fn perturb_one_gene_panics_out_of_range() {
        let g = Genome::neutral(1, 1);
        let _ = g.perturb_one_gene(2, 1.0);
    }
}
