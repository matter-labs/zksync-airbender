use std::collections::BTreeMap;

use gpu_core::primitives::field::{BF, E4};
use prover::gkr::prover::dimension_reduction::lsb_backward::{
    lsb_dim_reducing_sumcheck_prove, LsbDimReducingRelation,
};

use crate::upstream::{Field, FieldExtension, GKRAddress, PrimeField, Seed};

use super::capacity::{portable_entry, DrTailCapacityRejection, DrTailCapacityRequest};
use super::census::{address_order, corpus_census};
use super::dr_tail_first_order_mismatch;
use super::reference::{
    run_reference, set_consistent_initial_claim, synthetic_two_group_eq, DrTailMutation,
    DrTailReferenceInput, DrTailReferenceSlot, DrTailSlotKind,
};

fn lift(value: u32) -> E4 {
    <E4 as FieldExtension<BF>>::from_base(BF::from_u32_with_reduction(value))
}

fn request(cap: usize) -> DrTailCapacityRequest {
    DrTailCapacityRequest {
        folding_steps: 23,
        entry_round: 15,
        canonical_sources: 8,
        static_smem_bytes: 8_192,
        device_cap_bytes: cap,
    }
}

#[test]
fn cpu_dr_tail_capacity_matches_the_portable_worst_case() {
    let entry_round = portable_entry(23).unwrap();
    let decision = request(101_376).decide().unwrap();
    assert_eq!(entry_round, 15);
    assert_eq!(decision.entry_round, 15);
    assert_eq!(decision.remaining_rounds, 8);
    assert_eq!(decision.entry_cells_per_source, 512);
    assert_eq!(decision.state_bytes, 65_536);
    assert_eq!(decision.eq_suffix_offset, 16);
    assert_eq!(decision.eq_suffix_bits, 7);
    assert_eq!(decision.eq_group_count, 1);
    assert_eq!(decision.factored_eq_bytes, 4_096);
    assert_eq!(decision.dynamic_smem_bytes, 69_632);
    assert_eq!(decision.static_smem_bytes, 8_192);
    assert_eq!(decision.total_smem_bytes, 77_824);
}

#[test]
fn cpu_dr_tail_capacity_checks_boundaries_domains_and_overflow() {
    let total = request(usize::MAX).decide().unwrap().total_smem_bytes;
    assert!(matches!(
        request(total - 1).decide(),
        Err(DrTailCapacityRejection::DeviceCapacityExceeded { .. })
    ));
    assert_eq!(request(total).decide().unwrap().total_smem_bytes, total);
    assert_eq!(request(total + 1).decide().unwrap().total_smem_bytes, total);

    for (entry_round, expected) in [
        (2, DrTailCapacityRejection::EntryBeforeFirstWindow),
        (4, DrTailCapacityRejection::EntryNotWidthThreeBoundary),
        (24, DrTailCapacityRejection::EntryAtOrAfterFinalRound),
    ] {
        let mut invalid = request(usize::MAX);
        invalid.entry_round = entry_round;
        assert_eq!(invalid.decide().unwrap_err(), expected);
    }
    for canonical_sources in [0, 11] {
        let mut invalid = request(usize::MAX);
        invalid.canonical_sources = canonical_sources;
        assert_eq!(
            invalid.decide().unwrap_err(),
            DrTailCapacityRejection::CanonicalSourceCountOutOfRange
        );
    }
    let mut too_wide = request(usize::MAX);
    too_wide.folding_steps = 41;
    too_wide.entry_round = 15;
    assert_eq!(
        too_wide.decide().unwrap_err(),
        DrTailCapacityRejection::EqSuffixExceedsStrictThreeSlotGeometry
    );
    let mut overflow = DrTailCapacityRequest {
        folding_steps: 4,
        entry_round: 3,
        canonical_sources: 10,
        static_smem_bytes: usize::MAX,
        device_cap_bytes: usize::MAX,
    };
    assert_eq!(
        overflow.decide().unwrap_err(),
        DrTailCapacityRejection::ArithmeticOverflow
    );
    overflow.static_smem_bytes = 0;
    assert!(overflow.decide().is_ok());
    assert_eq!(
        portable_entry(3).unwrap_err(),
        DrTailCapacityRejection::FoldingStepsTooSmall
    );
}

#[test]
fn cpu_dr_tail_portable_entries_cover_every_production_bucket() {
    for (range, expected) in [
        (4..=6, 3),
        (7..=9, 6),
        (10..=12, 9),
        (13..=15, 12),
        (16..=23, 15),
    ] {
        for folding_steps in range {
            assert_eq!(portable_entry(folding_steps).unwrap(), expected);
        }
    }
}

#[test]
fn cpu_dr_tail_census_pins_capacity_alias_and_order_contracts() {
    let census = corpus_census();
    assert_eq!(census.rows.len(), 229);
    assert_eq!(census.mismatch_layers, 9);
    assert_eq!(census.merge_layers, 0);
    assert_eq!(census.rewritten_occurrences, 42);
    assert_eq!(
        census.mask_counts.keys().copied().collect::<Vec<_>>(),
        [1, 13, 15, 31]
    );
    assert_eq!(
        census.source_counts.keys().copied().collect::<Vec<_>>(),
        [2, 6, 8, 10]
    );
    for row in &census.rows {
        assert_eq!(row.legal_capacities.len(), (row.folding_steps - 1) / 3);
        assert_eq!(
            row.legal_capacities
                .iter()
                .find(|(entry, _)| *entry == row.capacity.entry_round)
                .unwrap()
                .1,
            Ok(row.capacity),
        );
    }
    let worst = census
        .rows
        .iter()
        .max_by_key(|row| row.capacity.total_smem_bytes)
        .unwrap();
    assert_eq!(
        (
            worst.folding_steps,
            worst.order.sorted_canonical.len(),
            worst.capacity.entry_round,
            worst.capacity.total_smem_bytes,
        ),
        (23, 8, 15, 77_824),
    );
    let (layout, layer, canonical, raw_lookup) = dr_tail_first_order_mismatch();
    assert!(!layout.is_empty());
    assert!(census
        .rows
        .iter()
        .any(|row| row.layout_name == layout && row.layer_idx == layer));
    assert_ne!(canonical, raw_lookup);
}

#[test]
fn cpu_dr_tail_alias_dedup_is_explicit_and_order_preserving() {
    let raw0 = GKRAddress::ScratchSpace(0);
    let raw1 = GKRAddress::ScratchSpace(1);
    let canonical = GKRAddress::InnerLayer {
        layer: 7,
        offset: 3,
    };
    let aliases = BTreeMap::from([(raw0, canonical), (raw1, canonical)]);
    let order = address_order([raw1, raw0, raw1], &aliases);
    assert_eq!(order.raw_sorted, [raw0, raw1]);
    assert_eq!(order.sorted_canonical, [canonical]);
    assert_eq!(order.raw_address_canonical_lookup, [0, 0]);
    assert_eq!(order.rewritten_occurrences, 3);
    assert_eq!(order.canonical_merges, 1);
}

fn reference_input(remaining_rounds: usize, raw_lookup: Vec<usize>) -> DrTailReferenceInput {
    let entry_round = 3;
    let folding_steps = entry_round + remaining_rounds;
    let source_len = 1usize << (remaining_rounds + 4);
    let canonical_sources = (0..4)
        .map(|source| {
            (0..source_len)
                .map(|index| lift(17 + source as u32 * 101 + index as u32 * 7))
                .collect()
        })
        .collect();
    let mut input = DrTailReferenceInput {
        folding_steps,
        entry_round,
        canonical_sources,
        slots: [
            Some(DrTailReferenceSlot {
                kind: DrTailSlotKind::Pairwise,
                source_indices: [0, 1],
                batch_weights: [lift(3), lift(5)],
            }),
            Some(DrTailReferenceSlot {
                kind: DrTailSlotKind::Lookup,
                source_indices: [2, 3],
                batch_weights: [lift(7), lift(11)],
            }),
            None,
            None,
            None,
        ],
        entry_challenges: [lift(13), lift(17), lift(19)],
        tau: (0..folding_steps)
            .map(|index| lift(23 + index as u32 * 2))
            .collect(),
        seed: Seed([0x1020_3040; 8]),
        initial_claim: E4::ZERO,
        initial_eq_prefactor: lift(29),
        raw_address_canonical_lookup: raw_lookup,
    };
    set_consistent_initial_claim(&mut input);
    input
}

fn upstream_relations() -> Vec<LsbDimReducingRelation<E4>> {
    vec![
        LsbDimReducingRelation::PairwiseProduct {
            input: GKRAddress::ScratchSpace(0),
            output: GKRAddress::ScratchSpace(100),
            alpha: lift(3),
        },
        LsbDimReducingRelation::PairwiseProduct {
            input: GKRAddress::ScratchSpace(1),
            output: GKRAddress::ScratchSpace(101),
            alpha: lift(5),
        },
        LsbDimReducingRelation::LogupPair {
            num: GKRAddress::ScratchSpace(2),
            den: GKRAddress::ScratchSpace(3),
            num_output: GKRAddress::ScratchSpace(102),
            den_output: GKRAddress::ScratchSpace(103),
            alpha_num: lift(7),
            alpha_den: lift(11),
        },
    ]
}

#[test]
fn cpu_dr_tail_reference_covers_the_fixed_five_slot_max_mask() {
    let mut input = reference_input(2, (0..10).collect());
    let source_len = input.canonical_sources[0].len();
    input.canonical_sources.extend((4..10).map(|source| {
        (0..source_len)
            .map(|index| lift(41 + source as u32 * 103 + index as u32 * 11))
            .collect()
    }));
    input.slots = [
        Some(DrTailReferenceSlot {
            kind: DrTailSlotKind::Pairwise,
            source_indices: [0, 1],
            batch_weights: [lift(3), lift(5)],
        }),
        Some(DrTailReferenceSlot {
            kind: DrTailSlotKind::Lookup,
            source_indices: [2, 3],
            batch_weights: [lift(7), lift(11)],
        }),
        Some(DrTailReferenceSlot {
            kind: DrTailSlotKind::Lookup,
            source_indices: [4, 5],
            batch_weights: [lift(13), lift(17)],
        }),
        Some(DrTailReferenceSlot {
            kind: DrTailSlotKind::Lookup,
            source_indices: [6, 7],
            batch_weights: [lift(19), lift(23)],
        }),
        Some(DrTailReferenceSlot {
            kind: DrTailSlotKind::Pairwise,
            source_indices: [8, 9],
            batch_weights: [lift(29), lift(31)],
        }),
    ];
    set_consistent_initial_claim(&mut input);
    let output = run_reference(&input, DrTailMutation::None).unwrap();
    assert_eq!(output.final_canonical_cells.len(), 10);
    assert_eq!(output.epilogue_raw_cells.len(), 10);
}

#[test]
fn cpu_dr_tail_recursive_reference_matches_upstream_for_required_round_counts() {
    for remaining_rounds in [1, 2, 3, 4, 6, 8] {
        let input = reference_input(remaining_rounds, (0..4).collect());
        let output = run_reference(&input, DrTailMutation::None).unwrap();
        assert_eq!(output.entry_source_levels.len(), 3);
        assert_eq!(output.rounds.len(), remaining_rounds);
        let entry_sources = output.entry_source_levels.last().unwrap();
        let addresses: Vec<_> = (0..4).map(GKRAddress::ScratchSpace).collect();
        let polys: BTreeMap<_, _> = addresses
            .iter()
            .zip(entry_sources)
            .map(|(address, source)| (*address, source.as_slice()))
            .collect();
        let challenges: Vec<_> = output.rounds.iter().map(|round| round.challenge).collect();
        let upstream = lsb_dim_reducing_sumcheck_prove::<BF, E4>(
            &polys,
            &upstream_relations(),
            &input.tau[input.entry_round..],
            output.initial_normalized_claim,
            &challenges,
            &worker::Worker::new(),
        );
        assert_eq!(
            output
                .rounds
                .iter()
                .map(|round| round.coefficients)
                .collect::<Vec<_>>(),
            upstream.round_coefficients,
        );
        assert_eq!(output.rounds.last().unwrap().claim, upstream.final_claim);
        assert_eq!(
            output.rounds.last().unwrap().eq_prefactor,
            upstream.eq_factor
        );
        for (source, address) in addresses.iter().enumerate() {
            assert_eq!(
                output.epilogue_raw_cells[source],
                upstream.final_values[address]
            );
        }
    }
}

#[test]
fn cpu_dr_tail_eq_is_rebuilt_from_the_exact_tau_suffix_and_drained_once() {
    let input = reference_input(8, (0..4).collect());
    let output = run_reference(&input, DrTailMutation::None).unwrap();
    for (round_index, transition) in output.rounds.iter().enumerate() {
        let suffix = &input.tau[input.entry_round + round_index + 1..input.folding_steps];
        let expected: Vec<_> = (0..1usize << suffix.len())
            .map(|row| {
                suffix
                    .iter()
                    .enumerate()
                    .fold(E4::ONE, |mut value, (bit, challenge)| {
                        value.mul_assign(&if (row >> bit) & 1 == 0 {
                            let mut zero = E4::ONE;
                            zero.sub_assign(challenge);
                            zero
                        } else {
                            *challenge
                        });
                        value
                    })
            })
            .collect();
        assert_eq!(transition.eq_before.per_row_values, expected);
        if round_index + 1 == output.rounds.len() {
            assert!(transition.eq_after.is_none());
            assert_eq!(transition.eq_before.sizes, [0, 0, 0]);
        } else {
            assert_eq!(
                transition.eq_after.as_ref().unwrap(),
                &output.rounds[round_index + 1].eq_before
            );
        }
    }
}

#[test]
fn cpu_dr_tail_two_group_eq_drains_low_before_high_zero() {
    let challenges: Vec<_> = (0..9).map(|index| lift(31 + index)).collect();
    let snapshots = synthetic_two_group_eq(&challenges);
    assert_eq!(snapshots[0].sizes, [8, 0, 1]);
    assert_eq!(snapshots[0].group_tables.len(), 2);
    assert_eq!(snapshots[0].group_tables[0].len(), 256);
    assert_eq!(snapshots[0].group_tables[1].len(), 2);
    assert_eq!(snapshots[1].sizes, [8, 0, 0]);
    assert_eq!(snapshots[2].sizes, [7, 0, 0]);
    assert_eq!(snapshots.last().unwrap().sizes, [0, 0, 0]);
}

#[test]
fn cpu_dr_tail_mutations_are_non_vacuous_including_mismatch_epilogue_order() {
    let input = reference_input(4, vec![1, 0, 3, 2]);
    let baseline = run_reference(&input, DrTailMutation::None).unwrap();
    for mutation in [
        DrTailMutation::ReverseEntryChallengeOrder,
        DrTailMutation::GateMajorInsteadOfTwoYPlusB,
        DrTailMutation::FlipFirstSlotKind,
        DrTailMutation::SkipFirstSlot,
        DrTailMutation::ReverseCanonicalPublication,
        DrTailMutation::DirectCanonicalEpilogue,
    ] {
        let mutated = run_reference(&input, mutation).unwrap();
        assert_ne!(mutated, baseline, "{mutation:?} was vacuous");
    }
    assert!(run_reference(&input, DrTailMutation::FoldEqAfterFinalRound).is_err());
    let direct = run_reference(&input, DrTailMutation::DirectCanonicalEpilogue).unwrap();
    assert_ne!(direct.epilogue_raw_cells, baseline.epilogue_raw_cells);

    let mut changed_tau = input.clone();
    changed_tau.tau[input.entry_round + 1].add_assign(&E4::ONE);
    assert_ne!(
        run_reference(&changed_tau, DrTailMutation::None).unwrap(),
        baseline,
        "tau mutation was vacuous"
    );
    let mut changed_prefactor = input.clone();
    changed_prefactor.initial_eq_prefactor.add_assign(&E4::ONE);
    assert_ne!(
        run_reference(&changed_prefactor, DrTailMutation::None).unwrap(),
        baseline,
        "eq-prefactor mutation was vacuous"
    );
}
