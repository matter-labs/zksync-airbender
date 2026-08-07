use std::mem::{align_of, offset_of, size_of};

use super::*;
use gpu_core::primitives::field::E4;

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
    let r0 = size_of::<GpuGKRDimensionReducingRound0BatchCompact<E4>>();
    let cont = size_of::<GpuGKRDimensionReducingContinuationBatchCompact<E4>>();
    assert_eq!(r0, 456);
    assert_eq!(cont, 456);
    assert!(r0 + size_of::<u32>() <= KERNEL_ARG_CEILING_BYTES);
    assert!(cont + 2 * size_of::<u32>() <= KERNEL_ARG_CEILING_BYTES);

    assert_eq!(size_of::<GkrEqSizes>(), 12);
    assert_eq!(align_of::<GkrEqSizes>(), 4);
    assert_eq!(offset_of!(GkrEqSizes, high), 0);
    assert_eq!(offset_of!(GkrEqSizes, low), 8);

    macro_rules! assert_layout {
        ($ty:ty) => {
            assert_eq!(align_of::<$ty>(), 8);
            assert_eq!(offset_of!($ty, record_count), 0);
            assert_eq!(offset_of!($ty, _reserved0), 4);
            assert_eq!(offset_of!($ty, eq_low), 8);
            assert_eq!(offset_of!($ty, eq_sizes), 16);
            assert_eq!(offset_of!($ty, _eq_sizes_pad), 28);
            assert_eq!(offset_of!($ty, contributions), 32);
            assert_eq!(offset_of!($ty, tables), 40);
            assert_eq!(offset_of!($ty, records), 232);
            assert_eq!(offset_of!($ty, inline_payload), 344);
        };
    }
    assert_layout!(GpuGKRDimensionReducingRound0BatchCompact<E4>);
    assert_layout!(GpuGKRDimensionReducingContinuationBatchCompact<E4>);
}

#[test]
fn compact_record_is_16_bytes() {
    assert_eq!(size_of::<PayloadRange16>(), 4);
    assert_eq!(align_of::<PayloadRange16>(), 2);
    assert_eq!(offset_of!(PayloadRange16, offset), 0);
    assert_eq!(offset_of!(PayloadRange16, count), 2);

    assert_eq!(size_of::<GpuGKRDimensionReducingBatchRecordCompact>(), 16);
    assert_eq!(align_of::<GpuGKRDimensionReducingBatchRecordCompact>(), 4);
    assert_eq!(
        offset_of!(GpuGKRDimensionReducingBatchRecordCompact, kind),
        0
    );
    assert_eq!(
        offset_of!(GpuGKRDimensionReducingBatchRecordCompact, inputs),
        4
    );
    assert_eq!(
        offset_of!(GpuGKRDimensionReducingBatchRecordCompact, outputs),
        8
    );
    assert_eq!(
        offset_of!(
            GpuGKRDimensionReducingBatchRecordCompact,
            batch_challenge_offset
        ),
        12
    );
    assert_eq!(
        offset_of!(GpuGKRDimensionReducingBatchRecordCompact, _reserved),
        14
    );

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
        "GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER = 7;",
        "GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN = 10;",
        "GKR_DIM_REDUCING_INLINE_RECORD_CAP = 28;",
        "GKR_DIM_REDUCING_BASE_SLOTS = 16;",
        "GKR_DIM_REDUCING_MAX_INPUTS_PER_RECORD = 2;",
        "GKR_DIM_REDUCING_MAX_OUTPUTS_PER_RECORD = 2;",
        "GKR_BACKWARD_MAX_TRACE_LEN_LOG2 = 24;",
        "GKR_DIM_REDUCING_LAYER_CLAIM_POINT_LEN = GKR_BACKWARD_MAX_TRACE_LEN_LOG2 + 2;",
        "GKR_MAIN_LAYER_CLAIM_POINT_LEN = GKR_BACKWARD_MAX_TRACE_LEN_LOG2 + 1;",
        "GKR_EQ_GROUP_SIZE = 8;",
        "GKR_EQ_HIGH_SLOTS = 2;",
    ] {
        assert!(
            header.contains(declaration),
            "missing CUDA declaration: {declaration}"
        );
    }
    assert_eq!(GKR_DIM_REDUCING_MAX_RECORDS_PER_LAYER, 7);
    assert_eq!(GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN, 10);
    assert_eq!(GKR_DIM_REDUCING_INLINE_RECORD_CAP, 28);
    assert_eq!(GKR_DIM_REDUCING_BASE_SLOTS, 16);
    assert_eq!(GKR_DIM_REDUCING_MAX_INPUTS_PER_RECORD, 2);
    assert_eq!(GKR_DIM_REDUCING_MAX_OUTPUTS_PER_RECORD, 2);
    assert_eq!(GKR_BACKWARD_MAX_TRACE_LEN_LOG2, 24);
    assert_eq!(GKR_EQ_GROUP_SIZE, 8);
    assert_eq!(GKR_EQ_HIGH_SLOTS, 2);
    assert_eq!(MAX_DIM_REDUCING_LAYER_CLAIM_POINT_LEN, 26);
    assert_eq!(MAX_MAIN_LAYER_CLAIM_POINT_LEN, 25);
}
