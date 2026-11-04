use ::field::*;
use cs::definitions::*;
use fft::GoodAllocator;
use riscv_transpiler::cycle::state::NUM_REGISTERS;
use trace_holder::RowMajorTrace;

use super::*;

#[inline(always)]
pub fn read_field_element_at_row_and_offset<const N: usize, A: GoodAllocator>(
    trace: &RowMajorTrace<Mersenne31Field, N, A>,
    row_idx: usize,
    offset: usize,
) -> Mersenne31Field {
    let mut view = trace.column_view(offset, 1);
    view.advance_many(row_idx);
    let row = view.current_row();
    row[0]
}

pub fn produce_register_contribution_into_memory_accumulator(
    register_final_data: &[RamShuffleMemStateRecord; NUM_REGISTERS],
    memory_argument_linearization_challenges: [Mersenne31Quartic;
        NUM_MEM_ARGUMENT_LINEARIZATION_CHALLENGES],
    memory_argument_gamma: Mersenne31Quartic,
) -> Mersenne31Quartic {
    let input =
        register_final_data.map(|el| (el.current_value, split_timestamp(el.last_access_timestamp)));
    use crate::definitions::produce_register_contribution_into_memory_accumulator_raw;

    produce_register_contribution_into_memory_accumulator_raw(
        &input,
        memory_argument_linearization_challenges,
        memory_argument_gamma,
    )
}
