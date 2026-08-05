//! Genome-to-order decoding for the offline forward search.
//!
//! `relation_units` ([`super::structure::relation_units`]) always partitions a
//! layer's atom-root set exactly (every atom root belongs to exactly one unit,
//! singleton units for roots that aren't part of a multi-output relation) — so
//! decoding is always unit-grouped:
//! `Genome.root_order_key` has exactly one key per unit.

/// Sort unit indices `0..unit_key.len()` by their key (finite `f64`,
/// `total_cmp` so `NaN`/`-0.0` never panic or silently mis-tie), ties broken by
/// unit index for determinism.
pub fn decode_unit_order(unit_key: &[f64]) -> Vec<usize> {
    let mut order: Vec<usize> = (0..unit_key.len()).collect();
    order.sort_by(|&a, &b| unit_key[a].total_cmp(&unit_key[b]).then(a.cmp(&b)));
    order
}
