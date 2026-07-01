use super::*;

pub fn evaluate_init_and_teardown_memory_witness<
    F: PrimeField,
    A: Allocator + Clone,
    B: Allocator + Clone,
>(
    dumped_inits_and_teardowns: Vec<([Vec<F, A>; 2], [Vec<F, A>; 2])>,
    compiled_circuit: &GKRCircuitArtifact<F>,
    inner_allocator: A,
    outer_allocator: B,
) -> Vec<Vec<F, A>, B> {
    let mut result =
        Vec::with_capacity_in(compiled_circuit.memory_layout.total_width, outer_allocator);
    for _ in 0..compiled_circuit.memory_layout.total_width {
        result.push(Vec::new_in(inner_allocator.clone()));
    }

    populate_inline_inits_and_teardowns_columns(
        &mut result,
        dumped_inits_and_teardowns,
        &compiled_circuit.memory_layout.teardown_sets,
        true,
    );

    for el in result.iter() {
        assert!(el.is_empty() == false);
    }

    result
}

pub(crate) fn populate_inline_inits_and_teardowns_columns<F: PrimeField, A, B>(
    column_major_trace: &mut Vec<Vec<F, A>, B>,
    dumped_inits_and_teardowns: Vec<([Vec<F, A>; 2], [Vec<F, A>; 2])>,
    teardown_sets: &[([GKRAddress; 2], [GKRAddress; 2])],
    require_target_empty: bool,
) where
    A: Allocator + Clone,
    B: Allocator + Clone,
{
    assert_eq!(
        teardown_sets.len(),
        dumped_inits_and_teardowns.len(),
        "inline i/t dumped data must have one entry per teardown_set in memory_layout"
    );
    for (set, desc) in dumped_inits_and_teardowns
        .into_iter()
        .zip(teardown_sets.iter())
    {
        let ([a_src, b_src], [c_src, d_src]) = set;
        let ([a, b], [c, d]) = desc;
        for (src, dest) in [(a_src, *a), (b_src, *b), (c_src, *c), (d_src, *d)] {
            let GKRAddress::BaseLayerMemory(dest) = dest else {
                unreachable!()
            };
            if require_target_empty {
                assert!(
                    column_major_trace[dest].is_empty(),
                    "standalone i/t population: destination column {} was not empty",
                    dest
                );
            } else {
                debug_assert!(column_major_trace[dest].iter().all(|v| v.is_zero()),);
            }
            let _prev = core::mem::replace(&mut column_major_trace[dest], src);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use field::baby_bear::base::BabyBearField;
    use field::Field;
    use std::alloc::Global;
    use std::vec;
    use std::vec::Vec;

    /// Build a synthetic `teardown_sets` with one pair (= 2 sets, 4 columns each)
    /// pointing at column indices [0..8). Mirrors what
    /// `allocate_inline_inits_and_teardowns_sets` produces, but hand-rolled so the
    /// test doesn't depend on the cs-side compiler.
    fn synth_teardown_sets() -> Vec<([GKRAddress; 2], [GKRAddress; 2])> {
        let bl = |i| GKRAddress::BaseLayerMemory(i);
        // 2 sets × (timestamps[2] + values[2]) = 8 BaseLayerMemory columns.
        vec![
            ([bl(0), bl(1)], [bl(2), bl(3)]), // set 0
            ([bl(4), bl(5)], [bl(6), bl(7)]), // set 1
        ]
    }

    fn marker(set_idx: u32, limb: u32, row: u32) -> BabyBearField {
        // Distinguishable per-(set, limb, row) value to spot-check placement.
        BabyBearField::from_u32_with_reduction(
            (set_idx * 1_000_000) + (limb * 10_000) + row,
        )
    }

    fn synth_dumped_data(
        teardown_sets: &[([GKRAddress; 2], [GKRAddress; 2])],
        trace_len: usize,
    ) -> Vec<([Vec<BabyBearField>; 2], [Vec<BabyBearField>; 2])> {
        teardown_sets
            .iter()
            .enumerate()
            .map(|(set_idx, _)| {
                let mk = |limb: u32| -> Vec<BabyBearField> {
                    (0..trace_len)
                        .map(|r| marker(set_idx as u32, limb, r as u32))
                        .collect()
                };
                ([mk(0), mk(1)], [mk(2), mk(3)])
            })
            .collect()
    }

    /// Standalone (i/t-circuit) path: targets start empty, helper moves Vecs in,
    /// every destination column ends populated to length `trace_len`.
    #[test]
    fn standalone_path_places_each_set_at_recorded_indices() {
        let trace_len = 16usize;
        let teardown_sets = synth_teardown_sets();
        let total_width = 8;

        let mut column_major_trace: Vec<Vec<BabyBearField, Global>, Global> =
            (0..total_width).map(|_| Vec::new_in(Global)).collect();

        let dumped = synth_dumped_data(&teardown_sets, trace_len);
        populate_inline_inits_and_teardowns_columns(
            &mut column_major_trace,
            dumped,
            &teardown_sets,
            true,
        );

        // Every destination column has trace_len entries with the right marker.
        for set_idx in 0..teardown_sets.len() {
            let ([ts0, ts1], [v0, v1]) = teardown_sets[set_idx];
            for (limb_idx, addr) in [ts0, ts1, v0, v1].iter().enumerate() {
                let GKRAddress::BaseLayerMemory(col) = *addr else {
                    panic!("not BaseLayerMemory");
                };
                assert_eq!(
                    column_major_trace[col].len(),
                    trace_len,
                    "set {} limb {} (col {}) wrong length",
                    set_idx,
                    limb_idx,
                    col
                );
                for row in 0..trace_len {
                    assert_eq!(
                        column_major_trace[col][row],
                        marker(set_idx as u32, limb_idx as u32, row as u32),
                        "set {} limb {} row {} wrong value",
                        set_idx,
                        limb_idx,
                        row
                    );
                }
            }
        }
    }

    /// Two teardown_sets pointing at the same column trip the empty-target
    /// assert on the second write. Documents the cs-side allocator's
    /// no-overlap contract.
    #[test]
    #[should_panic(expected = "destination column 0 was not empty")]
    fn overlapping_destinations_caught_by_empty_check() {
        let trace_len = 4usize;
        let bl = |i| GKRAddress::BaseLayerMemory(i);
        // Set 1's first timestamp limb collides with set 0's.
        let teardown_sets = vec![
            ([bl(0), bl(1)], [bl(2), bl(3)]),
            ([bl(0), bl(5)], [bl(6), bl(7)]),
        ];
        let total_width = 8;
        let mut column_major_trace: Vec<Vec<BabyBearField, Global>, Global> =
            (0..total_width).map(|_| Vec::new_in(Global)).collect();
        let dumped = synth_dumped_data(&teardown_sets, trace_len);
        populate_inline_inits_and_teardowns_columns(
            &mut column_major_trace,
            dumped,
            &teardown_sets,
            true,
        );
    }

    /// Mirrors `evaluate_init_and_teardown_memory_witness`'s post-condition:
    /// when `total_width` exceeds the columns reachable from `teardown_sets`,
    /// some result columns stay empty and the final assertion fires. The
    /// wrapper requires a `GKRCircuitArtifact` so we inline its two relevant
    /// ops here rather than mock the artifact.
    #[test]
    #[should_panic]
    fn unpopulated_columns_violate_wrapper_postcondition() {
        let trace_len = 4usize;
        let teardown_sets = synth_teardown_sets(); // covers cols 0..8
        let total_width = 10; // 2 cols nothing writes to

        let mut column_major_trace: Vec<Vec<BabyBearField, Global>, Global> =
            (0..total_width).map(|_| Vec::new_in(Global)).collect();
        let dumped = synth_dumped_data(&teardown_sets, trace_len);
        populate_inline_inits_and_teardowns_columns(
            &mut column_major_trace,
            dumped,
            &teardown_sets,
            true,
        );
        for el in column_major_trace.iter() {
            assert!(!el.is_empty());
        }
    }

    /// Teardown sets must address only `BaseLayerMemory` columns — the helper
    /// `unreachable!()`s on any other `GKRAddress` variant. Pins the contract
    /// since `GKRAddress` has 7 variants that the type system doesn't narrow.
    #[test]
    #[should_panic]
    fn non_base_layer_memory_address_unreachable() {
        let trace_len = 4usize;
        let bl = |i| GKRAddress::BaseLayerMemory(i);
        // Swap one valid address for BaseLayerWitness — not a valid target here.
        let teardown_sets = vec![([GKRAddress::BaseLayerWitness(0), bl(1)], [bl(2), bl(3)])];
        let total_width = 4;
        let mut column_major_trace: Vec<Vec<BabyBearField, Global>, Global> =
            (0..total_width).map(|_| Vec::new_in(Global)).collect();
        let dumped = synth_dumped_data(&teardown_sets, trace_len);
        populate_inline_inits_and_teardowns_columns(
            &mut column_major_trace,
            dumped,
            &teardown_sets,
            true,
        );
    }
}
