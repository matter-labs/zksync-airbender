//! Genome representation for the offline forward search.
//!
//! A `Genome` is a pair of real-valued vectors that the search decodes into a
//! relation order and per-site cache priorities.

#[derive(Clone, Debug, PartialEq)]
pub(super) struct Genome {
    pub root_order_key: Vec<f64>,
    pub cache_priority: Vec<f64>,
}

impl Genome {
    pub(super) fn neutral(n_units: usize, n_sites: usize) -> Self {
        let denom = n_units.max(1) as f64;
        Self {
            root_order_key: (0..n_units).map(|i| i as f64 / denom).collect(),
            cache_priority: vec![0.0; n_sites],
        }
    }
}

/// Cache-priority genes are symmetric biases in `[-1, 1]`.
pub(super) const CACHE_PRIORITY_BOUND: f64 = 1.0;

pub(crate) fn clamp_bias(value: f64) -> f64 {
    value.clamp(-CACHE_PRIORITY_BOUND, CACHE_PRIORITY_BOUND)
}

pub(super) fn decode_unit_order(unit_key: &[f64]) -> Vec<usize> {
    let mut order: Vec<usize> = (0..unit_key.len()).collect();
    order.sort_by(|&a, &b| unit_key[a].total_cmp(&unit_key[b]).then(a.cmp(&b)));
    order
}
