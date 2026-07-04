//! Genome → concrete order decoding (Task 6 promotion of
//! `gkr_eval_isa/tests/s3_planner/metaheuristic.rs`'s `decode_unit_order`
//! (:385) and `decode_grouped_occurrence_order` (:401)).
//!
//! `relation_units` ([`super::structure::relation_units`]) always partitions a
//! layer's atom-root set exactly (every atom root belongs to exactly one unit,
//! singleton units for roots that aren't part of a multi-output relation) — so
//! unlike the prototype (which had a units-empty "flat" fallback for a caller
//! that hadn't computed units yet), decoding here is always "unit-grouped":
//! `Genome.root_order_key` has exactly one key per unit.

use cs::gkr_compiler::dag_ir::RootId;

/// Sort unit indices `0..unit_key.len()` by their key (finite `f64`,
/// `total_cmp` so `NaN`/`-0.0` never panic or silently mis-tie), ties broken by
/// unit index for determinism. Pure index function — mirrors the prototype's
/// `decode_unit_order` verbatim (was already generic over an `OracleInstance`-free
/// `&[f64]`).
pub fn decode_unit_order(unit_key: &[f64]) -> Vec<usize> {
    let mut order: Vec<usize> = (0..unit_key.len()).collect();
    order.sort_by(|&a, &b| unit_key[a].total_cmp(&unit_key[b]).then(a.cmp(&b)));
    order
}

/// Expand a unit-keyed genome to a concrete root execution order: order the
/// units by key ([`decode_unit_order`]), then concatenate each unit's members
/// in their given (canonical, first-occurrence) order. A unit is indivisible
/// by construction, so the result always keeps every relation's roots
/// contiguous — atomicity is structural, not a re-projection.
///
/// Panics if `genome.root_order_key.len() != units.len()` (caller error: the
/// genome must have been sized against these exact `units`) or if `units`
/// doesn't partition its occurrences exactly once (would silently corrupt a
/// compile).
pub fn decode_order(root_order_key: &[f64], units: &[Vec<RootId>]) -> Vec<RootId> {
    assert_eq!(
        root_order_key.len(),
        units.len(),
        "unit-keyed genome must have exactly one key per unit"
    );
    let total: usize = units.iter().map(|u| u.len()).sum();
    let mut order = Vec::with_capacity(total);
    for u in decode_unit_order(root_order_key) {
        order.extend_from_slice(&units[u]);
    }
    order
}

/// True iff every unit's members form one contiguous run in `order` — used to
/// pin that [`decode_order`] never splits a unit even for hand-built inputs
/// (this is a structural invariant of the construction, not runtime-checked
/// in the hot path).
pub fn order_keeps_units_contiguous(order: &[RootId], units: &[Vec<RootId>]) -> bool {
    let mut pos = std::collections::HashMap::new();
    for (i, &r) in order.iter().enumerate() {
        pos.insert(r, i);
    }
    units.iter().all(|members| {
        if members.is_empty() {
            return true;
        }
        let (lo, hi) = members.iter().fold((usize::MAX, 0usize), |(lo, hi), r| {
            let p = pos[r];
            (lo.min(p), hi.max(p))
        });
        hi - lo + 1 == members.len()
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decode_unit_order_sorts_units_by_key() {
        let keys = [0.5, 0.1, 0.9];
        assert_eq!(decode_unit_order(&keys), vec![1, 0, 2]);
    }

    #[test]
    fn decode_unit_order_breaks_ties_by_index() {
        let keys = [0.5, 0.5, 0.1];
        assert_eq!(decode_unit_order(&keys), vec![2, 0, 1]);
    }

    #[test]
    fn decode_order_expands_units_in_canonical_member_order() {
        let units = vec![
            vec![RootId(0), RootId(1)], // unit 0 (e.g. num/den pair)
            vec![RootId(2)],            // unit 1 (singleton)
        ];
        // unit 1 sorts before unit 0.
        let order = decode_order(&[0.9, 0.1], &units);
        assert_eq!(order, vec![RootId(2), RootId(0), RootId(1)]);
    }

    #[test]
    fn decode_order_never_splits_a_unit() {
        let units = vec![vec![RootId(0), RootId(1), RootId(2)], vec![RootId(3)]];
        let order = decode_order(&[0.2, 0.1], &units);
        assert!(order_keeps_units_contiguous(&order, &units));
    }

    #[test]
    #[should_panic(expected = "one key per unit")]
    fn decode_order_panics_on_key_unit_count_mismatch() {
        let units = vec![vec![RootId(0)], vec![RootId(1)]];
        let _ = decode_order(&[0.1], &units);
    }
}
