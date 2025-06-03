use crate::definitions::LazyInitAndTeardown;
use ::field::*;
use core::u32;
use cs::cs::oracle::Oracle;
use cs::cs::placeholder::Placeholder;
use cs::definitions::ColumnAddress;
use cs::definitions::LookupExpression;
use cs::machine::machine_configurations::*;
use cs::machine::Machine;
use cs::one_row_compiler::*;
use cs::tables::LookupWrapper;
use cs::tables::TableDriver;
use cs::utils::split_u32_into_pair_u16;
use fft::*;
use memory_witness::delegation_circuit::evaluate_indirect_memory_accesses;
use memory_witness::delegation_circuit::process_delegation_requests_execution;
use memory_witness::main_circuit::process_delegation_requests;
use memory_witness::main_circuit::process_lazy_init_work;
use memory_witness::main_circuit::process_shuffle_ram_accesses;
use risc_v_simulator::abstractions::non_determinism::*;
use risc_v_simulator::cycle::state::NUM_REGISTERS;
use std::alloc::Allocator;
use std::alloc::Global;
use std::collections::HashMap;
use trace_holder::*;
use worker::Worker;

mod new;

mod ext_calls;
mod ext_calls_with_gpu_tracers;
mod memory_witness;
pub mod witness_proxy;

pub use self::new::{evaluate_witness, SimpleWitnessProxy};

pub(crate) mod utils;
use utils::*;

#[cfg(feature = "profiling")]
thread_local! {
    pub(crate) static PROFILING_TABLE: std::cell::RefCell<std::collections::BTreeMap<&'static str, std::time::Duration>> = std::cell::RefCell::new(std::collections::BTreeMap::new());
}

pub use self::memory_witness::{evaluate_delegation_memory_witness, evaluate_memory_witness};

pub use self::ext_calls::*;
pub use self::ext_calls_with_gpu_tracers::*;
use super::*;

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct WitnessEvaluationAuxData {
    pub first_row_public_inputs: Vec<Mersenne31Field>,
    pub one_before_last_row_public_inputs: Vec<Mersenne31Field>,
    pub lazy_init_first_row: [Mersenne31Field; REGISTER_SIZE],
    pub teardown_value_first_row: [Mersenne31Field; REGISTER_SIZE],
    pub teardown_timestamp_first_row: [Mersenne31Field; REGISTER_SIZE],
    pub lazy_init_one_before_last_row: [Mersenne31Field; REGISTER_SIZE],
    pub teardown_value_one_before_last_row: [Mersenne31Field; REGISTER_SIZE],
    pub teardown_timestamp_one_before_last_row: [Mersenne31Field; REGISTER_SIZE],
}

#[derive(Clone, Copy, Debug)]
pub struct RegisterFinalData {
    pub last_write_timestamp: u32,
    pub final_value: u32,
}

#[derive(Clone, Debug)]
pub struct WitnessEvaluationData<const N: usize, A: Allocator + Clone> {
    pub aux_data: WitnessEvaluationAuxData,
    pub exec_trace: RowMajorTrace<Mersenne31Field, N, A>,
    pub num_witness_columns: usize,
    // we will use it for stage 2 - we can map (for free) every lookup tuple into the
    // corresponding index of the lookup tables (and more precisely - in the concatenation of all the tables)
    pub lookup_mapping: RowMajorTrace<u32, N, A>,
}

#[derive(Clone, Debug)]
pub struct MemoryOnlyWitnessEvaluationData<const N: usize, A: Allocator + Clone> {
    pub aux_data: WitnessEvaluationAuxData,
    pub memory_trace: RowMajorTrace<Mersenne31Field, N, A>,
}

#[derive(Clone, Debug)]
pub struct DelegationMemoryOnlyWitnessEvaluationData<const N: usize, A: Allocator + Clone> {
    pub memory_trace: RowMajorTrace<Mersenne31Field, N, A>,
}

unsafe fn count_special_range_check_multiplicities(
    witness_trace_view_row: &mut [Mersenne31Field],
    memory_trace_view_row: &mut [Mersenne31Field],
    setup_trace_view_row: &[Mersenne31Field],
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    absolute_row_idx: usize,
    range_check_16_multiplicieties: &mut [u32],
    timestamp_range_check_multiplicieties: &mut [u32],
    timestamp_high_contribution_if_shuffle_ram: Mersenne31Field,
    trace_len: usize,
) {
    assert!(trace_len.is_power_of_two());
    // range check 16 are special-cased in the lookup argument, and we do not need to compute mapping for them
    let num_trivial_relations = compiled_circuit
        .witness_layout
        .range_check_16_columns
        .num_elements();

    #[cfg(feature = "profiling")]
    let t = std::time::Instant::now();

    // here we do NOT need extra mapping - we can just use a value!
    for range_check_expression in compiled_circuit
        .witness_layout
        .range_check_16_lookup_expressions[..num_trivial_relations]
        .iter()
    {
        let LookupExpression::Variable(place) = range_check_expression else {
            unreachable!()
        };
        let ColumnAddress::WitnessSubtree(offset) = place else {
            unreachable!()
        };
        let value = *witness_trace_view_row.get_unchecked(*offset);
        assert!(
            value.to_reduced_u32() <= u16::MAX as u32,
            "invalid value {:?} in range check 16 trivial expression {:?} at row {}",
            value,
            range_check_expression,
            absolute_row_idx,
        );
        let index = value.to_reduced_u32() as usize;
        *range_check_16_multiplicieties.get_unchecked_mut(index) += 1;
    }

    let nontrivial_range_check_16_relations = &compiled_circuit
        .witness_layout
        .range_check_16_lookup_expressions[num_trivial_relations..];
    assert!(nontrivial_range_check_16_relations.len() % 2 == 0);

    for range_check_expression in nontrivial_range_check_16_relations.iter() {
        let value = match range_check_expression {
            LookupExpression::Variable(place) => {
                let ColumnAddress::WitnessSubtree(offset) = place else {
                    unreachable!()
                };
                *witness_trace_view_row.get_unchecked(*offset)
            }
            LookupExpression::Expression(constraint) => constraint
                .evaluate_at_row_on_main_domain(&*witness_trace_view_row, &*memory_trace_view_row),
        };
        assert!(
            value.to_reduced_u32() <= u16::MAX as u32,
            "invalid value {:?} in range check 16 expression {:?} at row {}",
            absolute_row_idx,
            range_check_expression,
            value
        );
        let index = value.to_reduced_u32() as usize;
        *range_check_16_multiplicieties.get_unchecked_mut(index) += 1;
    }

    // special case for lazy init values
    if let Some(shuffle_ram_inits_and_teardowns) = compiled_circuit
        .memory_layout
        .shuffle_ram_inits_and_teardowns
    {
        let start = shuffle_ram_inits_and_teardowns
            .lazy_init_addresses_columns
            .start();
        for offset in start..(start + 2) {
            let value = *memory_trace_view_row.get_unchecked(offset);
            assert!(
                value.to_reduced_u32() <= u16::MAX as u32,
                "invalid value {:?} in range check 16 in lazy init addresses at row {}",
                absolute_row_idx,
                value
            );
            let index = value.to_reduced_u32() as usize;
            *range_check_16_multiplicieties.get_unchecked_mut(index) += 1;
        }
    }

    // now timestamp related relations - all are non-trivial

    let offset_for_special_shuffle_ram_timestamps_range_check_expressions = compiled_circuit
        .witness_layout
        .offset_for_special_shuffle_ram_timestamps_range_check_expressions;

    let timestamp_range_check_relations_without_ram = &compiled_circuit
        .witness_layout
        .timestamp_range_check_lookup_expressions
        [..offset_for_special_shuffle_ram_timestamps_range_check_expressions];
    assert!(timestamp_range_check_relations_without_ram.len() % 2 == 0);

    for range_check_expression in timestamp_range_check_relations_without_ram.iter() {
        let value = match range_check_expression {
            LookupExpression::Variable(place) => {
                let ColumnAddress::WitnessSubtree(offset) = place else {
                    unreachable!()
                };
                *witness_trace_view_row.get_unchecked(*offset)
            }
            LookupExpression::Expression(constraint) => constraint
                .evaluate_at_row_on_main_domain(&*witness_trace_view_row, &*memory_trace_view_row),
        };
        assert!(
            value.to_reduced_u32() < (1 << TIMESTAMP_COLUMNS_NUM_BITS),
            "invalid value {:?} in timestamp range check expression {:?} at row {}",
            value,
            range_check_expression,
            absolute_row_idx,
        );
        let index = value.to_reduced_u32() as usize;
        *timestamp_range_check_multiplicieties.get_unchecked_mut(index) += 1;
    }

    // then potentially shuffle ram related expressions
    let shuffle_ram_partial_expressions = &compiled_circuit
        .witness_layout
        .timestamp_range_check_lookup_expressions
        [offset_for_special_shuffle_ram_timestamps_range_check_expressions..];
    assert!(shuffle_ram_partial_expressions.len() % 2 == 0);

    for [low, high] in shuffle_ram_partial_expressions.array_chunks::<2>() {
        {
            let LookupExpression::Expression(constraint_low) = low else {
                unreachable!()
            };
            let low_value = constraint_low.evaluate_at_row_on_main_domain_ext(
                &*witness_trace_view_row,
                &*memory_trace_view_row,
                setup_trace_view_row,
            );
            if low_value.to_reduced_u32() >= (1 << TIMESTAMP_COLUMNS_NUM_BITS) {
                dbg!(absolute_row_idx);
                for (coeff, place) in constraint_low.linear_terms.iter() {
                    dbg!(coeff);
                    dbg!(place);
                    let value = read_value_with_setup_access(
                        *place,
                        &*witness_trace_view_row,
                        &*memory_trace_view_row,
                        setup_trace_view_row,
                    );
                    dbg!(value,);
                }
            }
            assert!(
                low_value.to_reduced_u32() < (1 << TIMESTAMP_COLUMNS_NUM_BITS),
                "invalid value {:?} in timestamp range check expression for shuffle RAM low timestamp {:?} at row {}",
                low_value,
                low,
                absolute_row_idx,
            );
            let index = low_value.to_reduced_u32() as usize;
            *timestamp_range_check_multiplicieties.get_unchecked_mut(index) += 1;
        }

        {
            // here we should consider contribution into high expression from circuit sequence
            let LookupExpression::Expression(constraint_high) = high else {
                unreachable!()
            };
            let mut high_value = constraint_high.evaluate_at_row_on_main_domain_ext(
                &*witness_trace_view_row,
                &*memory_trace_view_row,
                setup_trace_view_row,
            );
            // NOTE: subtraction here as we compare read timestamp - write timestamp, and circuit sequence is a part of write timestamp
            high_value.sub_assign(&timestamp_high_contribution_if_shuffle_ram);
            assert!(
                high_value.to_reduced_u32() < (1 << TIMESTAMP_COLUMNS_NUM_BITS),
                "invalid value {:?} in timestamp range check expression for shuffle RAM high timestamp {:?} at row {}. Circuit sequence contribution = {:?}",
                high_value,
                high,
                absolute_row_idx,
                timestamp_high_contribution_if_shuffle_ram,
            );
            let index = high_value.to_reduced_u32() as usize;
            *timestamp_range_check_multiplicieties.get_unchecked_mut(index) += 1;
        }
    }

    #[cfg(feature = "profiling")]
    PROFILING_TABLE.with_borrow_mut(|el| {
        *el.entry("Range check multiplicity counting").or_default() += t.elapsed();
    });
}

unsafe fn postprocess_multiplicities<const N: usize, A: Allocator + Clone>(
    exec_trace: &mut RowMajorTrace<Mersenne31Field, N, A>,
    num_witness_columns: usize,
    mut range_16_multiplicity_subcounters: Vec<Vec<u32>>,
    mut timestamp_range_check_multiplicity_subcounters: Vec<Vec<u32>>,
    mut general_purpose_multiplicity_subcounters: Vec<Vec<u32>>,
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    generic_lookup_multiplicities_total_len: usize,
    trace_len: usize,
    worker: &Worker,
) {
    // it's just fine to copy in the non-parallel manner for the range-check 16 and timestamp
    {
        #[cfg(feature = "profiling")]
        let t = std::time::Instant::now();

        let mut range_16_multiplicities = range_16_multiplicity_subcounters.pop().unwrap();
        for el in range_16_multiplicity_subcounters.into_iter() {
            assert_eq!(range_16_multiplicities.len(), el.len());

            for (dst, src) in range_16_multiplicities.iter_mut().zip(el.into_iter()) {
                *dst += src;
            }
        }

        // write them column_major
        unsafe {
            let offset = compiled_circuit
                .witness_layout
                .multiplicities_columns_for_range_check_16
                .start();
            let mut view = exec_trace.row_view(0..1 << 16);
            for absolute_row_idx in 0..(1 << 16) {
                let (row, _) = view.current_row_split(num_witness_columns);
                let multiplicity = *range_16_multiplicities.get_unchecked(absolute_row_idx);
                debug_assert!(multiplicity < Mersenne31Field::CHARACTERISTICS as u32);
                *row.get_unchecked_mut(offset) = Mersenne31Field(multiplicity as u32);

                view.advance_row();
            }
        }

        #[cfg(feature = "profiling")]
        PROFILING_TABLE.with_borrow_mut(|el| {
            *el.entry("Range check 16 multiplicity copy-back")
                .or_default() += t.elapsed();
        });
    }

    // add up and write timestamp multiplicities
    {
        #[cfg(feature = "profiling")]
        let t = std::time::Instant::now();

        let mut timestamp_range_check_multiplicities =
            timestamp_range_check_multiplicity_subcounters
                .pop()
                .unwrap();
        for el in timestamp_range_check_multiplicity_subcounters.into_iter() {
            assert_eq!(timestamp_range_check_multiplicities.len(), el.len());

            for (dst, src) in timestamp_range_check_multiplicities
                .iter_mut()
                .zip(el.into_iter())
            {
                *dst += src;
            }
        }

        // write them column_major
        unsafe {
            let offset = compiled_circuit
                .witness_layout
                .multiplicities_columns_for_timestamp_range_check
                .start();
            let mut view = exec_trace.row_view(0..1 << TIMESTAMP_COLUMNS_NUM_BITS);
            for absolute_row_idx in 0..(1 << TIMESTAMP_COLUMNS_NUM_BITS) {
                let (row, _) = view.current_row_split(num_witness_columns);
                let multiplicity =
                    *timestamp_range_check_multiplicities.get_unchecked(absolute_row_idx);
                debug_assert!(multiplicity < Mersenne31Field::CHARACTERISTICS as u32);
                *row.get_unchecked_mut(offset) = Mersenne31Field(multiplicity as u32);

                view.advance_row();
            }
        }

        #[cfg(feature = "profiling")]
        PROFILING_TABLE.with_borrow_mut(|el| {
            *el.entry("Timestamp range check multiplicity copy-back")
                .or_default() += t.elapsed();
        });
    }

    // now it's a little bit more tricky, we will walk over rows, and access semi-arbitrary indexes for lookups

    #[cfg(feature = "profiling")]
    let t = std::time::Instant::now();

    if generic_lookup_multiplicities_total_len > 0 {
        let mut general_purpose_multiplicity =
            general_purpose_multiplicity_subcounters.pop().unwrap();

        if worker.num_cores > 1 {
            worker.scope(general_purpose_multiplicity.len(), |scope, geometry| {
                let mut dst_slice = &mut general_purpose_multiplicity[..];
                for thread_idx in 0..geometry.len() {
                    let chunk_size = geometry.get_chunk_size(thread_idx);
                    let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                    let range = chunk_start..(chunk_start + chunk_size);

                    let (dst, rest) = dst_slice.split_at_mut(chunk_size);
                    dst_slice = rest;

                    if thread_idx == geometry.len() - 1 {
                        assert!(dst_slice.is_empty());
                    }

                    let sources = general_purpose_multiplicity_subcounters
                        .iter()
                        .map(move |el| &el[range.clone()]);

                    Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                        for src in sources {
                            assert_eq!(dst.len(), src.len());
                            for (dst, src) in dst.iter_mut().zip(src.iter()) {
                                *dst += *src;
                            }
                        }
                    });
                }
            });
        } else {
            // nothing
        }

        // and copy it back
        let encoding_capacity = trace_len - 1;
        let general_purpose_multiplicity_ref = &general_purpose_multiplicity;

        unsafe {
            worker.scope(trace_len - 1, |scope, geometry| {
                for thread_idx in 0..geometry.len() {
                    let chunk_size = geometry.get_chunk_size(thread_idx);
                    let chunk_start = geometry.get_chunk_start_pos(thread_idx);

                    let range = chunk_start..(chunk_start + chunk_size);
                    let mut exec_trace_view = exec_trace.row_view(range.clone());

                    let multiplicities_range = compiled_circuit
                        .witness_layout
                        .multiplicities_columns_for_generic_lookup
                        .full_range();

                    Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                        for i in 0..chunk_size {
                            let absolute_row_idx = chunk_start + i;
                            let witness_trace_view_row =
                                exec_trace_view.current_row_split(num_witness_columns).0;

                            let dst = &mut witness_trace_view_row[multiplicities_range.clone()];
                            for (column, dst) in dst.iter_mut().enumerate() {
                                let encoding_index = encoding_tuple_into_lookup_index(
                                    column as u32,
                                    absolute_row_idx as u32,
                                    encoding_capacity,
                                );
                                if encoding_index < general_purpose_multiplicity_ref.len() {
                                    // so it's used
                                    let multiplicity = *general_purpose_multiplicity_ref
                                        .get_unchecked(encoding_index);
                                    debug_assert!(
                                        multiplicity < Mersenne31Field::CHARACTERISTICS as u32
                                    );
                                    *dst = Mersenne31Field(multiplicity as u32);
                                }
                            }

                            // and go to the next row
                            exec_trace_view.advance_row();
                        }
                    });
                }
            });
        }
    }
    #[cfg(feature = "profiling")]
    PROFILING_TABLE.with_borrow_mut(|el| {
        *el.entry("Multiplicities copy-back took").or_default() += t.elapsed();
    });
}

pub(crate) unsafe fn evaluate_witness_inner_static_work<O: Oracle<Mersenne31Field>>(
    witness_row: &mut [Mersenne31Field],
    memory_row: &mut [Mersenne31Field],
    compiled_circuit: &CompiledCircuitArtifact<Mersenne31Field>,
    oracle: &O,
    absolute_row_idx: usize,
    is_last_cycle: bool,
    lazy_init_data: &[LazyInitAndTeardown],
    timestamp_high_from_circuit_sequence: TimestampScalar,
) {
    assert!(compiled_circuit
        .memory_layout
        .batched_ram_accesses
        .is_empty());
    assert!(compiled_circuit
        .batched_memory_access_timestamp_comparison_aux_vars
        .aux_borrow_vars
        .is_empty());

    process_lazy_init_work::<true>(
        witness_row,
        memory_row,
        compiled_circuit,
        absolute_row_idx,
        is_last_cycle,
        lazy_init_data,
    );

    process_delegation_requests(memory_row, compiled_circuit, oracle, absolute_row_idx);

    process_shuffle_ram_accesses::<O, true>(
        witness_row,
        memory_row,
        compiled_circuit,
        oracle,
        absolute_row_idx,
        timestamp_high_from_circuit_sequence,
    );

    process_delegation_requests_execution(memory_row, compiled_circuit, oracle, absolute_row_idx);

    evaluate_indirect_memory_accesses::<O, true>(
        witness_row,
        memory_row,
        compiled_circuit,
        oracle,
        absolute_row_idx,
    );
}
