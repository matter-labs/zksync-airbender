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
use worker::WorkerGeometry;

// mod init_and_teardown;
mod memory;
// mod unified;
pub(crate) mod witness;

// pub use self::init_and_teardown::{
//     evaluate_init_and_teardown_memory_witness, evaluate_init_and_teardown_witness,
// };
pub use self::memory::evaluate_gkr_memory_witness_for_executor_family;
// pub use self::unified::{
//     evaluate_memory_witness_for_unified_executor, evaluate_witness_for_unified_executor,
// };
pub use self::witness::evaluate_gkr_witness_for_executor_family;

pub use self::memory::GKRMemoryOnlyWitnessTrace;
pub use self::witness::GKRFullWitnessTrace;

pub(crate) fn chunk_vec_capacity_for_geometry<'a, T: Sized + 'static, A: Allocator>(
    backing: &'a mut Vec<T, A>,
    geometry: WorkerGeometry,
    total_size: usize,
) -> Vec<*mut T> {
    assert!(total_size <= backing.capacity());
    let mut result = Vec::with_capacity(geometry.len());
    let mut ptr = backing.as_mut_ptr();
    let mut total_chunked = 0;
    for i in 0..geometry.len() {
        unsafe {
            result.push(ptr);
            let chunk_size = geometry.get_chunk_size(i);
            ptr = ptr.add(chunk_size);
            total_chunked += chunk_size;
        }
    }
    assert_eq!(total_chunked, total_size);

    result
}

pub(crate) fn chunk_vec_vec_capacity_for_geometry<
    'a,
    T: Sized + 'static,
    A: Allocator,
    B: Allocator,
>(
    backing: &'a mut Vec<Vec<T, A>, B>,
    geometry: WorkerGeometry,
    total_size: usize,
) -> Vec<Box<[*mut T]>> {
    let mut result = Vec::with_capacity(geometry.len());

    let mut total_chunked = 0;
    let mut start_pointers: Vec<_> = backing
        .iter_mut()
        .map(|el| {
            assert!(total_size <= el.capacity());

            el.as_mut_ptr()
        })
        .collect();

    for chunk_idx in 0..geometry.len() {
        let chunk_size = geometry.get_chunk_size(chunk_idx);
        result.push(start_pointers.clone().into_boxed_slice());

        for el in start_pointers.iter_mut() {
            unsafe {
                *el = el.add(chunk_size);
            }
        }

        total_chunked += chunk_size;
    }

    assert_eq!(total_chunked, total_size);

    result
}

pub(crate) fn evaluate_linear_relation<'a, F: PrimeField, O: Oracle<F> + 'a>(
    relation: &NoFieldLinearRelation,
    proxy: &ColumnMajorWitnessProxy<'a, O, F>,
) -> F {
    let mut result = F::from_u32_unchecked(relation.constant);
    for (c, addr) in relation.linear_terms.iter() {
        let el = match *addr {
            GKRAddress::BaseLayerMemory(offset) => proxy.get_memory_place(offset),
            GKRAddress::BaseLayerWitness(offset) => proxy.get_witness_place(offset),
            GKRAddress::ScratchSpace(offset) => proxy.get_scratch_place(offset),
            _ => {
                unreachable!()
            }
        };
        let mut t = F::from_u32_unchecked(*c);
        t.mul_assign(&el);
        result.add_assign(&t);
    }
    result
}

pub fn non_trivial_padding_convention_for_executor_circuit_memory<
    F: PrimeField,
    A: Allocator + Clone,
    B: Allocator + Clone,
>(
    trace: &mut Vec<Vec<F, A>, B>,
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
        .fill(F::from_u32_unchecked(low_start as u32));
    trace[machine_state.final_state.timestamp[0]][num_cycles..]
        .fill(F::from_u32_unchecked(low_end as u32));
}
