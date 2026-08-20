use super::*;

use crate::gkr::witness_gen::column_major_proxy::ColumnMajorWitnessProxy;
use crate::gkr::witness_gen::witness_proxy::WitnessProxy;
use common_constants::{TimestampScalar, INITIAL_TIMESTAMP, TIMESTAMP_STEP};
use cs::definitions::gkr::NoFieldLinearRelation;
use cs::definitions::GKRAddress;
use cs::gkr_compiler::GKRCircuitArtifact;
use cs::oracle::Oracle;
use cs::utils::split_timestamp;
use field::PrimeField;

mod init_and_teardown;
mod memory;
mod unified;
pub(crate) mod witness;

pub use self::init_and_teardown::evaluate_init_and_teardown_memory_witness;
pub use self::memory::evaluate_gkr_memory_witness_for_executor_family;
pub use self::unified::build_unified_table_driver;
pub use self::witness::evaluate_gkr_witness_for_executor_family;

pub use self::memory::GKRMemoryOnlyWitnessTrace;
pub use self::witness::GKRFullWitnessTrace;

pub(crate) fn evaluate_linear_relation<'a, F: PrimeField, O: Oracle<F> + 'a>(
    relation: &NoFieldLinearRelation<F>,
    proxy: &ColumnMajorWitnessProxy<'a, O, F>,
) -> F {
    let mut result = relation.constant;
    for (c, addr) in relation.linear_terms.iter() {
        let el = match *addr {
            GKRAddress::BaseLayerMemory(offset) => proxy.get_memory_place(offset),
            GKRAddress::BaseLayerWitness(offset) => proxy.get_witness_place(offset),
            GKRAddress::ScratchSpace(offset) => proxy.get_scratch_place(offset),
            _ => {
                unreachable!()
            }
        };
        let mut t = *c;
        t.mul_assign(&el);
        result.add_assign(&t);
    }
    result
}

pub fn non_trivial_padding_convention_for_executor_circuit_memory<
    F: PrimeField,
    A: Allocator + Clone,
>(
    trace: &mut [Vec<F, A>],
    compiled_circuit: &GKRCircuitArtifact<F>,
    num_cycles: usize,
) {
    const PADDING_INITIAL_TS: TimestampScalar = INITIAL_TIMESTAMP;
    let (low_start, _) = split_timestamp(PADDING_INITIAL_TS);

    const PADDING_FINAL_TS: TimestampScalar = INITIAL_TIMESTAMP + TIMESTAMP_STEP;
    let (low_end, _) = split_timestamp(PADDING_FINAL_TS);

    let machine_state = compiled_circuit
        .memory_layout
        .machine_state
        .as_ref()
        .expect("is present");
    trace[machine_state.initial_state.timestamp[0]][num_cycles..]
        .fill(F::from_u32_unchecked(low_start));
    trace[machine_state.final_state.timestamp[0]][num_cycles..]
        .fill(F::from_u32_unchecked(low_end));
}
