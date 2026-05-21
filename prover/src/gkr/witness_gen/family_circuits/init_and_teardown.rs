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
        BabyBearField::from_u64_with_reduction(
            ((set_idx as u64) * 1_000_000) + ((limb as u64) * 10_000) + (row as u64),
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

    /// Standalone path asserts that destination columns are empty before the swap.
    /// Pre-fill column 0 with garbage and confirm we get a panic.
    #[test]
    #[should_panic(expected = "standalone i/t population: destination column 0 was not empty")]
    fn standalone_path_panics_if_target_non_empty() {
        let trace_len = 4usize;
        let teardown_sets = synth_teardown_sets();
        let total_width = 8;

        let mut column_major_trace: Vec<Vec<BabyBearField, Global>, Global> =
            (0..total_width).map(|_| Vec::new_in(Global)).collect();
        // Pre-fill column 0 (the first destination of set 0) with junk.
        column_major_trace[0].push(BabyBearField::ZERO);

        let dumped = synth_dumped_data(&teardown_sets, trace_len);
        populate_inline_inits_and_teardowns_columns(
            &mut column_major_trace,
            dumped,
            &teardown_sets,
            /* require_target_empty = */ true,
        );
    }

    /// Inline path (= require_target_empty = false): destinations have prior
    /// length (simulating `set_len(trace_len)` having run on them, exposing
    /// uninit data). Helper resets len to 0 before the swap, then places the
    /// dumped data. Verify the resulting columns have exactly the dumped data,
    /// not the prior contents.
    #[test]
    fn inline_path_overwrites_set_len_uninit_data() {
        let trace_len = 8usize;
        let teardown_sets = synth_teardown_sets();
        let total_width = 8;

        // Pre-allocate columns with capacity=trace_len and set_len(trace_len)
        // to simulate the inline-i/t entry conditions. Values are zeroed (Global
        // allocator), but the contract is they're treated as uninit — the helper
        // must NOT read them.
        let mut column_major_trace: Vec<Vec<BabyBearField, Global>, Global> = (0..total_width)
            .map(|_| {
                let mut v = Vec::with_capacity_in(trace_len, Global);
                for _ in 0..trace_len {
                    v.push(BabyBearField::from_u64_with_reduction(0xdead_beef));
                }
                v
            })
            .collect();

        let dumped = synth_dumped_data(&teardown_sets, trace_len);
        populate_inline_inits_and_teardowns_columns(
            &mut column_major_trace,
            dumped,
            &teardown_sets,
            false,
        );

        // Every destination now holds the dumped data — no trace of the 0xdead_beef sentinel.
        for set_idx in 0..teardown_sets.len() {
            let ([ts0, ts1], [v0, v1]) = teardown_sets[set_idx];
            for (limb_idx, addr) in [ts0, ts1, v0, v1].iter().enumerate() {
                let GKRAddress::BaseLayerMemory(col) = *addr else {
                    panic!("not BaseLayerMemory");
                };
                assert_eq!(column_major_trace[col].len(), trace_len);
                for row in 0..trace_len {
                    let expected = marker(set_idx as u32, limb_idx as u32, row as u32);
                    assert_eq!(
                        column_major_trace[col][row], expected,
                        "set {} limb {} row {} should be marker, not sentinel",
                        set_idx, limb_idx, row,
                    );
                }
            }
        }
    }

    /// Length-mismatch between dumped data and teardown_sets is a hard error.
    #[test]
    #[should_panic(expected = "inline i/t dumped data must have one entry per teardown_set")]
    fn length_mismatch_panics() {
        let teardown_sets = synth_teardown_sets(); // 2 sets
        let total_width = 8;
        let mut column_major_trace: Vec<Vec<BabyBearField, Global>, Global> =
            (0..total_width).map(|_| Vec::new_in(Global)).collect();

        // Only 1 dumped entry vs 2 expected.
        let dumped = synth_dumped_data(&teardown_sets[..1], 4);
        populate_inline_inits_and_teardowns_columns(
            &mut column_major_trace,
            dumped,
            &teardown_sets,
            true,
        );
    }
}
