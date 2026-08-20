use std::mem::{align_of, offset_of, size_of};

use super::*;
use crate::upstream::OutputType;
use gpu_core::primitives::field::E4;

const ALL_OUTPUT_TYPES: [OutputType; GKR_DIM_REDUCING_SLOTS] = [
    OutputType::PermutationProduct,
    OutputType::Lookup16Bits,
    OutputType::LookupTimestamps,
    OutputType::GenericLookup,
    OutputType::InitsAndTeardownsProduct,
];

/// Exponents are packed densely in slot order, while the generated verifier packs
/// them in `OutputType` `Ord` order. The two must agree, or a circuit that skips
/// an output type gets exponents the verifier does not expect.
#[test]
fn cpu_slot_index_follows_output_type_ord() {
    let mut by_ord = ALL_OUTPUT_TYPES;
    by_ord.sort();
    let mut by_slot = ALL_OUTPUT_TYPES;
    by_slot.sort_by_key(|output_type| dim_reducing_slot_index(*output_type));
    assert_eq!(by_ord, by_slot);
}

#[inline]
pub(crate) const fn unpack_source_u16(packed: u16) -> (bool, u8, u16) {
    let first_access = packed & (1 << 15) != 0;
    let ptr_idx = ((packed >> 11) & 0xF) as u8;
    let poly_idx = packed & 0x07FF;
    (first_access, ptr_idx, poly_idx)
}

#[test]
fn pack_source_u16_round_trips() {
    for first_access in [false, true] {
        for ptr_idx in 0u8..(GKR_DIM_REDUCING_BASE_SLOTS as u8) {
            for &poly_idx in &[0u16, 1, 2, 17, 255, 1024, 0x07FF] {
                let packed = pack_source_u16(first_access, ptr_idx, poly_idx);
                let (fa, p, q) = unpack_source_u16(packed);
                assert_eq!(fa, first_access);
                assert_eq!(p, ptr_idx);
                assert_eq!(q, poly_idx);
            }
        }
    }
}

#[test]
fn pack_source_u16_layout_bits() {
    // bit 15 = first_access, bits 14..11 = ptr_idx (4 bits, 16 slots),
    // bits 10..0 = poly_idx (11 bits, max 2048).
    assert_eq!(pack_source_u16(false, 0, 0), 0);
    assert_eq!(pack_source_u16(true, 0, 0), 0x8000);
    assert_eq!(pack_source_u16(false, 0xF, 0), 0x7800);
    assert_eq!(pack_source_u16(false, 0, 0x07FF), 0x07FF);
    assert_eq!(pack_source_u16(true, 0xF, 0x07FF), 0xFFFF);
}

#[test]
fn compact_descriptor_sizes_under_kernel_arg_ceiling() {
    const KERNEL_ARG_CEILING_BYTES: usize = gpu_gkr_compiler::KERNEL_ARGUMENT_CEILING_BYTES;
    let batch = size_of::<GpuGKRDimensionReducingBatch<E4>>();
    assert_eq!(batch, 336);
    // The continuation kernel carries the widest trailing scalars (acc_size, step).
    assert!(batch + 2 * size_of::<u32>() <= KERNEL_ARG_CEILING_BYTES);

    assert_eq!(size_of::<GkrEqSizes>(), 12);
    assert_eq!(align_of::<GkrEqSizes>(), 4);
    assert_eq!(offset_of!(GkrEqSizes, high), 0);
    assert_eq!(offset_of!(GkrEqSizes, low), 8);

    type Batch = GpuGKRDimensionReducingBatch<E4>;
    assert_eq!(align_of::<Batch>(), 8);
    assert_eq!(offset_of!(Batch, enabled_mask), 0);
    assert_eq!(offset_of!(Batch, _reserved0), 4);
    assert_eq!(offset_of!(Batch, eq_low), 8);
    assert_eq!(offset_of!(Batch, eq_sizes), 16);
    assert_eq!(offset_of!(Batch, _eq_sizes_pad), 28);
    assert_eq!(offset_of!(Batch, contributions), 32);
    assert_eq!(offset_of!(Batch, tables), 40);
    assert_eq!(offset_of!(Batch, slots), 232);
    assert_eq!(offset_of!(Batch, _slots_pad), 332);
}

#[test]
fn compact_slot_is_20_bytes() {
    assert_eq!(size_of::<GpuGKRDimensionReducingSlot>(), 20);
    assert_eq!(align_of::<GpuGKRDimensionReducingSlot>(), 2);
    assert_eq!(offset_of!(GpuGKRDimensionReducingSlot, io), 0);
    assert_eq!(offset_of!(GpuGKRDimensionReducingSlot, batch_exp), 16);

    assert_eq!(size_of::<GpuGKRDimensionReducingTables>(), 192);
    assert_eq!(align_of::<GpuGKRDimensionReducingTables>(), 8);
    assert_eq!(offset_of!(GpuGKRDimensionReducingTables, bases), 0);
    assert_eq!(offset_of!(GpuGKRDimensionReducingTables, log2_stride), 128);

    assert_eq!(size_of::<GpuGKRSourceRecord>(), 4);
    assert_eq!(align_of::<GpuGKRSourceRecord>(), 2);
    assert_eq!(offset_of!(GpuGKRSourceRecord, src), 0);
    assert_eq!(offset_of!(GpuGKRSourceRecord, cache), 2);
}

#[test]
fn compact_cuda_constants_match_rust() {
    let header = include_str!("../../../native/gkr/support/descriptors.cuh");
    for declaration in [
        "GKR_DIM_REDUCING_SLOTS = 5;",
        "GKR_DIM_REDUCING_INPUTS_PER_SLOT = 2;",
        "GKR_DIM_REDUCING_OUTPUTS_PER_SLOT = 2;",
        "GKR_DIM_REDUCING_BASE_SLOTS = 16;",
        "GKR_BACKWARD_MAX_TRACE_LEN_LOG2 = 24;",
        "GKR_DIM_REDUCING_LAYER_CLAIM_POINT_LEN = GKR_BACKWARD_MAX_TRACE_LEN_LOG2 + 2;",
        "GKR_MAIN_LAYER_CLAIM_POINT_LEN = GKR_BACKWARD_MAX_TRACE_LEN_LOG2 + 1;",
        "GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS = 10;",
        "GKR_EQ_GROUP_SIZE = 8;",
        "GKR_EQ_HIGH_SLOTS = 2;",
    ] {
        assert!(
            header.contains(declaration),
            "missing CUDA declaration: {declaration}"
        );
    }
    assert_eq!(GKR_DIM_REDUCING_SLOTS, 5);
    assert_eq!(GKR_DIM_REDUCING_INPUTS_PER_SLOT, 2);
    assert_eq!(GKR_DIM_REDUCING_OUTPUTS_PER_SLOT, 2);
    assert_eq!(GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN, 10);
    assert_eq!(GKR_DIM_REDUCING_BASE_SLOTS, 16);
    assert_eq!(GKR_BACKWARD_MAX_TRACE_LEN_LOG2, 24);
    assert_eq!(GKR_EQ_GROUP_SIZE, 8);
    assert_eq!(GKR_EQ_HIGH_SLOTS, 2);
    assert_eq!(
        crate::setup::kernels::GKR_FORWARD_SETUP_GENERIC_LOOKUP_MAX_COLUMNS,
        10
    );
    assert_eq!(MAX_DIM_REDUCING_LAYER_CLAIM_POINT_LEN, 26);
    assert_eq!(MAX_MAIN_LAYER_CLAIM_POINT_LEN, 25);
}

/// The shared one-shot eq builder must produce the LSB-first orientation:
/// `eq[i] = prod_b (bit_b(i) ? point[b] : 1 - point[b])`, i.e. claim
/// coordinate `b` pairs with table bit `b`. Oracle is the live CPU
/// `make_eq_table_lsb_first`. Challenge counts cover the group boundaries
/// (`GKR_EQ_GROUP_SIZE = 8`) and both chunk sizes inside a group; the
/// `challenge_offset = 1` cases pin that the reversal happens WITHIN
/// `[challenge_offset, challenge_offset + challenge_count)` — the factored-eq
/// callers in both sumcheck plans pass offset 1.
#[test]
#[cfg(not(no_cuda))]
fn eq_builder_matches_cpu_lsb_table() {
    use era_cudart::memory::memory_copy_async;
    use gpu_core::allocator::tracker::AllocationPlacement;
    use gpu_core::primitives::context::DeviceAllocation;
    use gpu_core::primitives::field::BF;
    use rand::rngs::StdRng;
    use rand::{Rng, SeedableRng};
    use worker::Worker;

    use crate::test_utils::make_test_context;
    use crate::upstream::{Field, PrimeField};

    let context = make_test_context(256, 64);
    let worker = Worker::new();
    let mut rng = StdRng::seed_from_u64(0x1b_5f_ab_20);

    for (challenge_offset, challenge_count) in [
        (0usize, 1usize),
        (0, 2),
        (0, 7),
        (0, 8),
        (0, 9),
        (0, 16),
        (0, 17),
        (1, 2),
        (1, 9),
    ] {
        let point: Vec<E4> = (0..challenge_offset + challenge_count)
            .map(|_| {
                E4::from_array_of_base(std::array::from_fn(|_| {
                    BF::from_u32_with_reduction(rng.random())
                }))
            })
            .collect();

        let acc_size = 1usize << challenge_count;
        let mut d_point: DeviceAllocation<E4> = context
            .alloc(point.len(), AllocationPlacement::BestFit)
            .unwrap();
        memory_copy_async(&mut d_point, &point, context.get_exec_stream()).unwrap();
        let mut d_group_tables: DeviceAllocation<E4> = context
            .alloc(
                eq_group_tables_len(challenge_count),
                AllocationPlacement::Top,
            )
            .unwrap();
        let mut d_eq_values: DeviceAllocation<E4> =
            context.alloc(acc_size, AllocationPlacement::Top).unwrap();

        launch_build_eq_values_from_point(
            d_point.as_ptr(),
            challenge_offset,
            challenge_count,
            d_group_tables.as_mut_ptr(),
            d_eq_values.as_mut_ptr(),
            acc_size,
            &context,
        )
        .unwrap();

        let mut from_gpu = vec![E4::ZERO; acc_size];
        memory_copy_async(&mut from_gpu, &d_eq_values, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();

        let expected = prover::gkr::sumcheck::eq_poly::make_eq_table_lsb_first::<E4>(
            &point[challenge_offset..],
            &worker,
        );
        assert_eq!(expected.len(), from_gpu.len());
        let first_divergence = from_gpu
            .iter()
            .zip(expected.iter())
            .position(|(gpu, cpu)| gpu != cpu);
        assert!(
            first_divergence.is_none(),
            "challenge_offset={challenge_offset} challenge_count={challenge_count}: \
             first divergent index {:?} (bits {:0width$b})",
            first_divergence,
            first_divergence.unwrap_or(0),
            width = challenge_count,
        );
    }
}
