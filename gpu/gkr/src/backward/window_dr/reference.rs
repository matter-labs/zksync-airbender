//! Independent CPU model of the dimension-reducing width-3 R0 tensor.

use std::collections::BTreeMap;

use gpu_core::primitives::field::E4;
use gpu_gkr_compiler::DrWindowProgram;

use crate::upstream::{Field, GKRAddress};

const DR_SLOT_COUNT: usize = 5;
const DR_OPERANDS_PER_SLOT: usize = 4;
const DR_INPUTS_PER_SLOT: usize = 2;
const DR_OUTPUTS_PER_SLOT: usize = 2;
const DR_TENSOR_CELLS: usize = 27;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct DrTensorOracleLane {
    pub(super) dense_slot: usize,
    pub(super) operand: usize,
    pub(super) source_id: u16,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct DrTensorOracleSlot {
    pub(super) slot: usize,
    pub(super) source_ids: [u16; DR_OPERANDS_PER_SLOT],
    pub(super) batch_exponents: [u16; DR_OUTPUTS_PER_SLOT],
}

/// Pointer-free snapshot of every producer input that can change tensor
/// semantics. It is copied from the production compiler program so tests can
/// mutate one wire fact at a time without requiring a second lowering path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct DrTensorOracleProgram {
    pub(super) enabled_mask: u32,
    pub(super) section_endpoints: [u32; DR_SLOT_COUNT],
    pub(super) slots: Vec<DrTensorOracleSlot>,
    pub(super) sources: Vec<GKRAddress>,
    pub(super) source_lanes: Vec<DrTensorOracleLane>,
}

impl DrTensorOracleProgram {
    pub(super) fn from_production(program: &DrWindowProgram) -> Self {
        Self {
            enabled_mask: program.enabled_mask(),
            section_endpoints: *program.section_endpoints(),
            slots: program
                .slots()
                .iter()
                .map(|slot| DrTensorOracleSlot {
                    slot: slot.slot(),
                    source_ids: *slot.source_ids(),
                    batch_exponents: *slot.batch_exponents(),
                })
                .collect(),
            sources: program.sources().to_vec(),
            source_lanes: program
                .source_lanes()
                .iter()
                .map(|lane| DrTensorOracleLane {
                    dense_slot: lane.dense_slot(),
                    operand: lane.operand(),
                    source_id: lane.source_id(),
                })
                .collect(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum DrTensorOracleError {
    ZeroMask,
    UndefinedMaskBits {
        bits: u32,
    },
    EnabledMaskMismatch {
        expected: u32,
        observed: u32,
    },
    InvalidSlot {
        dense_slot: usize,
        slot: usize,
    },
    SectionEndpointMismatch {
        section: usize,
        expected: u32,
        observed: u32,
    },
    SourceLaneMismatch {
        lane: usize,
        expected: Option<DrTensorOracleLane>,
        observed: Option<DrTensorOracleLane>,
    },
    InvalidSourceId {
        dense_slot: usize,
        operand: usize,
        source_id: u16,
        source_count: usize,
    },
    MissingSource {
        address: GKRAddress,
    },
    SourceLengthMismatch {
        address: GKRAddress,
        expected: usize,
        observed: usize,
    },
    SuffixPointTooWide {
        coordinates: usize,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum DrTensorMismatch {
    Cell {
        index: usize,
        expected: E4,
        observed: E4,
    },
}

pub(super) fn compare_dr_tensors(
    expected: &[E4; DR_TENSOR_CELLS],
    observed: &[E4; DR_TENSOR_CELLS],
) -> Result<(), DrTensorMismatch> {
    for (index, (expected, observed)) in expected.iter().zip(observed).enumerate() {
        if observed != expected {
            return Err(DrTensorMismatch::Cell {
                index,
                expected: *expected,
                observed: *observed,
            });
        }
    }
    Ok(())
}

/// Build the equality-contracted 27-cell DR R0 tensor in tail order
/// `9 * low + 3 * middle + high`.
///
/// Input columns use the production `2 * Y + b` layout; output columns are
/// materialized on `Y`. `suffix_point` contains the coordinates above the
/// three peeled Y bits, low variable first.
pub(super) fn dr_r0_tensor_reference(
    program: &DrTensorOracleProgram,
    columns: &BTreeMap<GKRAddress, Vec<E4>>,
    batch_challenge_base: E4,
    suffix_point: &[E4],
) -> Result<[E4; DR_TENSOR_CELLS], DrTensorOracleError> {
    validate_program(program)?;

    let suffix_coordinates =
        u32::try_from(suffix_point.len()).map_err(|_| DrTensorOracleError::SuffixPointTooWide {
            coordinates: suffix_point.len(),
        })?;
    let suffix_rows =
        1usize
            .checked_shl(suffix_coordinates)
            .ok_or(DrTensorOracleError::SuffixPointTooWide {
                coordinates: suffix_point.len(),
            })?;
    let input_len = suffix_rows
        .checked_mul(16)
        .ok_or(DrTensorOracleError::SuffixPointTooWide {
            coordinates: suffix_point.len(),
        })?;
    let output_len = suffix_rows
        .checked_mul(8)
        .ok_or(DrTensorOracleError::SuffixPointTooWide {
            coordinates: suffix_point.len(),
        })?;
    validate_columns(program, columns, input_len, output_len)?;

    let mut tensor = [E4::ZERO; DR_TENSOR_CELLS];
    for low in 0..3 {
        for middle in 0..3 {
            for high in 0..3 {
                let outer_infinity = middle == 2 || high == 2;
                let mut contracted = E4::ZERO;
                for suffix_row in 0..suffix_rows {
                    let suffix_weight = suffix_point.iter().enumerate().fold(
                        E4::ONE,
                        |mut weight, (bit, coordinate)| {
                            weight.mul_assign(&eq_weight((suffix_row >> bit) & 1, *coordinate));
                            weight
                        },
                    );
                    let mut row_value = E4::ZERO;
                    for slot in &program.slots {
                        let addresses = slot
                            .source_ids
                            .map(|source_id| program.sources[usize::from(source_id)]);
                        let inputs = [&columns[&addresses[0]], &columns[&addresses[1]]];
                        let outputs = [&columns[&addresses[2]], &columns[&addresses[3]]];
                        let weights = slot
                            .batch_exponents
                            .map(|exponent| batch_challenge_power(batch_challenge_base, exponent));

                        if is_pairwise_slot(slot.slot) {
                            for tower in 0..DR_OUTPUTS_PER_SLOT {
                                let gate_zero =
                                    input_pair(inputs[tower], suffix_row, high, middle, 0);
                                let gate_one =
                                    input_pair(inputs[tower], suffix_row, high, middle, 1);
                                let mut value =
                                    product_cell(gate_zero, gate_one, low, outer_infinity);
                                if low < 2 && !outer_infinity {
                                    value.add_assign(
                                        &outputs[tower]
                                            [(suffix_row << 3) | (high << 2) | (middle << 1) | low],
                                    );
                                }
                                value.mul_assign(&weights[tower]);
                                row_value.add_assign(&value);
                            }
                        } else {
                            let numerator_zero = input_pair(inputs[0], suffix_row, high, middle, 0);
                            let numerator_one = input_pair(inputs[0], suffix_row, high, middle, 1);
                            let denominator_zero =
                                input_pair(inputs[1], suffix_row, high, middle, 0);
                            let denominator_one =
                                input_pair(inputs[1], suffix_row, high, middle, 1);
                            let mut numerator =
                                product_cell(numerator_zero, denominator_one, low, outer_infinity);
                            numerator.add_assign(&product_cell(
                                numerator_one,
                                denominator_zero,
                                low,
                                outer_infinity,
                            ));
                            let mut denominator = product_cell(
                                denominator_zero,
                                denominator_one,
                                low,
                                outer_infinity,
                            );
                            if low < 2 && !outer_infinity {
                                let output_index =
                                    (suffix_row << 3) | (high << 2) | (middle << 1) | low;
                                numerator.add_assign(&outputs[0][output_index]);
                                denominator.add_assign(&outputs[1][output_index]);
                            }
                            numerator.mul_assign(&weights[0]);
                            denominator.mul_assign(&weights[1]);
                            row_value.add_assign(&numerator);
                            row_value.add_assign(&denominator);
                        }
                    }
                    row_value.mul_assign(&suffix_weight);
                    contracted.add_assign(&row_value);
                }
                tensor[9 * low + 3 * middle + high] = contracted;
            }
        }
    }
    Ok(tensor)
}

pub(super) fn batch_challenge_power(base: E4, exponent: u16) -> E4 {
    if exponent == 0 {
        return E4::ONE;
    }
    let mut result = E4::ONE;
    for _ in 0..exponent {
        result.mul_assign(&base);
    }
    result
}

fn validate_program(program: &DrTensorOracleProgram) -> Result<(), DrTensorOracleError> {
    if program.enabled_mask == 0 {
        return Err(DrTensorOracleError::ZeroMask);
    }
    let undefined = program.enabled_mask & !0x1f;
    if undefined != 0 {
        return Err(DrTensorOracleError::UndefinedMaskBits { bits: undefined });
    }

    let mut expected_mask = 0u32;
    let mut previous_slot = None;
    for (dense_slot, slot) in program.slots.iter().enumerate() {
        if slot.slot >= DR_SLOT_COUNT || previous_slot.is_some_and(|previous| previous >= slot.slot)
        {
            return Err(DrTensorOracleError::InvalidSlot {
                dense_slot,
                slot: slot.slot,
            });
        }
        previous_slot = Some(slot.slot);
        expected_mask |= 1u32 << slot.slot;
        for (operand, source_id) in slot.source_ids.iter().copied().enumerate() {
            if usize::from(source_id) >= program.sources.len() {
                return Err(DrTensorOracleError::InvalidSourceId {
                    dense_slot,
                    operand,
                    source_id,
                    source_count: program.sources.len(),
                });
            }
        }
    }
    if program.enabled_mask != expected_mask {
        return Err(DrTensorOracleError::EnabledMaskMismatch {
            expected: expected_mask,
            observed: program.enabled_mask,
        });
    }

    for section in 0..DR_SLOT_COUNT {
        let expected = program
            .slots
            .iter()
            .filter(|slot| slot.slot <= section)
            .count() as u32;
        let observed = program.section_endpoints[section];
        if observed != expected {
            return Err(DrTensorOracleError::SectionEndpointMismatch {
                section,
                expected,
                observed,
            });
        }
    }

    let expected_lanes = program
        .slots
        .iter()
        .enumerate()
        .flat_map(|(dense_slot, slot)| {
            slot.source_ids
                .iter()
                .copied()
                .enumerate()
                .map(move |(operand, source_id)| DrTensorOracleLane {
                    dense_slot,
                    operand,
                    source_id,
                })
        })
        .collect::<Vec<_>>();
    let lane_count = expected_lanes.len().max(program.source_lanes.len());
    for lane in 0..lane_count {
        let expected = expected_lanes.get(lane).copied();
        let observed = program.source_lanes.get(lane).copied();
        if observed != expected {
            return Err(DrTensorOracleError::SourceLaneMismatch {
                lane,
                expected,
                observed,
            });
        }
    }
    Ok(())
}

fn validate_columns(
    program: &DrTensorOracleProgram,
    columns: &BTreeMap<GKRAddress, Vec<E4>>,
    input_len: usize,
    output_len: usize,
) -> Result<(), DrTensorOracleError> {
    for slot in &program.slots {
        for (operand, source_id) in slot.source_ids.iter().copied().enumerate() {
            let address = program.sources[usize::from(source_id)];
            let column = columns
                .get(&address)
                .ok_or(DrTensorOracleError::MissingSource { address })?;
            let expected = if operand < DR_INPUTS_PER_SLOT {
                input_len
            } else {
                output_len
            };
            if column.len() != expected {
                return Err(DrTensorOracleError::SourceLengthMismatch {
                    address,
                    expected,
                    observed: column.len(),
                });
            }
        }
    }
    Ok(())
}

fn is_pairwise_slot(slot: usize) -> bool {
    slot == 0 || slot == 4
}

fn eq_weight(bit: usize, coordinate: E4) -> E4 {
    if bit == 0 {
        let mut result = E4::ONE;
        result.sub_assign(&coordinate);
        result
    } else {
        coordinate
    }
}

fn selector_weight(selector: usize, bit: usize) -> E4 {
    match (selector, bit) {
        (0, 0) | (1, 1) | (2, 1) => E4::ONE,
        (0, 1) | (1, 0) => E4::ZERO,
        (2, 0) => {
            let mut result = E4::ZERO;
            result.sub_assign(&E4::ONE);
            result
        }
        _ => unreachable!("selector and bit are ternary/Boolean"),
    }
}

/// The pair of low-Y endpoints for one retained gate bit after taking the
/// requested finite/difference endpoints on the middle and high Y axes.
fn input_pair(
    column: &[E4],
    suffix_row: usize,
    high: usize,
    middle: usize,
    gate_bit: usize,
) -> [E4; 2] {
    core::array::from_fn(|low| {
        let mut result = E4::ZERO;
        for high_bit in 0..2 {
            for middle_bit in 0..2 {
                let mut weight = selector_weight(high, high_bit);
                weight.mul_assign(&selector_weight(middle, middle_bit));
                let y_index = (suffix_row << 3) | (high_bit << 2) | (middle_bit << 1) | low;
                let mut value = column[2 * y_index + gate_bit];
                value.mul_assign(&weight);
                result.add_assign(&value);
            }
        }
        result
    })
}

fn product_cell(left: [E4; 2], right: [E4; 2], low: usize, outer_infinity: bool) -> E4 {
    if low < 2 {
        if outer_infinity {
            let mut result = left[low];
            result.mul_assign(&right[low]);
            result
        } else {
            E4::ZERO
        }
    } else {
        let mut left_delta = left[1];
        left_delta.sub_assign(&left[0]);
        let mut right_delta = right[1];
        right_delta.sub_assign(&right[0]);
        left_delta.mul_assign(&right_delta);
        left_delta
    }
}
