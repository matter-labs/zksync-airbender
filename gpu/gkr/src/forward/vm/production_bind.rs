//! Binds compiled forward layers to prover storage and runtime challenge data.

use std::ptr::null_mut;

use crate::{
    forward::{
        dimension_reducing::{
            LoweredSlotInitialInput, LoweredSlotOutput, PreparedDimensionReductionForward,
        },
        vm::desc::{
            FwdVmReductionPair, FUSED_REDUCTION_ROUNDS, REDUCTION_PAIR_CAP, REDUCTION_PAIR_LOOKUP,
            REDUCTION_PAIR_PAIRWISE2,
        },
    },
    upstream::{
        ChallengeRef, PermutationSlot, PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
        PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
        PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
        PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
        PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
        PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
    },
};

#[derive(Debug)]
pub(crate) enum BindError {
    /// An `ArgDerivedE4` ref is not host-known at scheduling time, so it
    /// cannot ride the by-value descriptor.
    NonScheduleTimeArgDerivedE4(ChallengeRef),
}

impl std::fmt::Display for BindError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BindError::NonScheduleTimeArgDerivedE4(r) => write!(
                f,
                "arg-derived-E4 {r:?} is not known to the host at scheduling time, so it cannot \
                 ride the by-value descriptor"
            ),
        }
    }
}

/// Map a `PermutationSlot` to its index in
/// `GKRExternalChallenges::permutation_argument_linearization_challenges`.
pub(crate) fn permutation_linearization_index(slot: &PermutationSlot) -> usize {
    match slot {
        PermutationSlot::AddressLow => PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
        PermutationSlot::AddressHigh => PERMUTATION_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
        PermutationSlot::TimestampLow => PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX,
        PermutationSlot::TimestampHigh => PERMUTATION_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
        PermutationSlot::ValueLow => PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
        PermutationSlot::ValueHigh => PERMUTATION_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
    }
}

pub(crate) fn write_fused_reduction_prefix<F: Copy>(
    count: u32,
    pairs: &mut [FwdVmReductionPair<F>; REDUCTION_PAIR_CAP],
    pair_count: &mut u32,
    prepared: &PreparedDimensionReductionForward<F>,
) {
    assert!(count > 0 && count.is_multiple_of(128));
    assert_eq!(count.trailing_zeros(), prepared.initial_trace_log_2);
    assert_eq!(
        prepared.per_round_slot_outputs.len(),
        prepared.total_rounds as usize
    );
    assert_eq!(
        prepared.slot_initial_inputs.len(),
        prepared.slot_output_types.len()
    );
    assert!(!prepared.slot_initial_inputs.is_empty());
    assert!(
        prepared
            .slot_output_types
            .windows(2)
            .all(|pair| pair[0] <= pair[1]),
        "reduction slots must follow OutputType order"
    );
    for outputs in &prepared.per_round_slot_outputs {
        assert_eq!(outputs.len(), prepared.slot_initial_inputs.len());
    }

    let mut slot = 0usize;
    let mut pair = 0usize;
    while slot < prepared.slot_output_types.len() {
        assert!(pair < REDUCTION_PAIR_CAP);
        let output_type = prepared.slot_output_types[slot];
        let range_end = prepared.slot_output_types[slot..]
            .iter()
            .position(|kind| *kind != output_type)
            .map(|offset| slot + offset)
            .unwrap_or(prepared.slot_output_types.len());
        let arity = range_end - slot;
        let record = match output_type {
            crate::upstream::OutputType::PermutationProduct
            | crate::upstream::OutputType::InitsAndTeardownsProduct => {
                assert_eq!(arity, 2);
                let input = [slot, slot + 1].map(|slot| {
                    let LoweredSlotInitialInput::PairwiseProduct { input } =
                        prepared.slot_initial_inputs[slot]
                    else {
                        panic!("pairwise reduction input changed kind")
                    };
                    assert!(!input.is_null());
                    input
                });
                let mut round_outputs = [[null_mut(); 2]; FUSED_REDUCTION_ROUNDS];
                for (round, outputs) in round_outputs.iter_mut().enumerate() {
                    for (output, slot) in outputs.iter_mut().zip([slot, slot + 1]) {
                        let LoweredSlotOutput::PairwiseProduct { output: pointer } =
                            prepared.per_round_slot_outputs[round][slot]
                        else {
                            panic!("pairwise reduction output changed kind")
                        };
                        assert!(!pointer.is_null());
                        *output = pointer;
                    }
                }
                FwdVmReductionPair {
                    input,
                    round_outputs,
                    kind: REDUCTION_PAIR_PAIRWISE2,
                    reserved: 0,
                }
            }
            crate::upstream::OutputType::Lookup16Bits
            | crate::upstream::OutputType::LookupTimestamps
            | crate::upstream::OutputType::GenericLookup => {
                assert_eq!(arity, 1);
                let LoweredSlotInitialInput::LookupPair { num, den } =
                    prepared.slot_initial_inputs[slot]
                else {
                    panic!("lookup reduction input changed kind")
                };
                assert!(!num.is_null() && !den.is_null());
                let mut round_outputs = [[null_mut(); 2]; FUSED_REDUCTION_ROUNDS];
                for (round, outputs) in round_outputs.iter_mut().enumerate() {
                    let LoweredSlotOutput::LookupPair {
                        output_num,
                        output_den,
                    } = prepared.per_round_slot_outputs[round][slot]
                    else {
                        panic!("lookup reduction output changed kind")
                    };
                    assert!(!output_num.is_null() && !output_den.is_null());
                    *outputs = [output_num, output_den];
                }
                FwdVmReductionPair {
                    input: [num, den],
                    round_outputs,
                    kind: REDUCTION_PAIR_LOOKUP,
                    reserved: 0,
                }
            }
        };
        pairs[pair] = record;
        pair += 1;
        slot = range_end;
    }
    *pair_count = pair as u32;
}
