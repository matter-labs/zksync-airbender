use std::mem::size_of;

use era_cudart::result::CudaResult;
use era_cudart::slice::DeviceSlice;

use super::*;
use crate::gkr_address_audit_helpers::{
    KERNEL_ARG_HARD_CEILING_BYTES, KERNEL_ARG_SOFT_TARGET_BYTES,
};
use crate::upstream::Field;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::device_structures::{DeviceVectorChunk, DeviceVectorChunkMut};
use gpu_core::primitives::field::E4;
use gpu_cub::cub::device_reduce::{reduce, Reduce, ReduceOperation};
use gpu_ops::simple::{mul_into_y, BinaryOp, Mul};
use gpu_prover_context::ProverContext;

#[inline]
pub(crate) const fn unpack_source_u16(packed: u16) -> (bool, u8, u16) {
    let first_access = packed & (1 << 15) != 0;
    let ptr_idx = ((packed >> 11) & 0xF) as u8;
    let poly_idx = packed & 0x07FF;
    (first_access, ptr_idx, poly_idx)
}

pub(crate) fn apply_eq_and_reduce_accumulator<E>(
    eq_values: &DeviceAllocation<E>,
    accumulator: &mut DeviceAllocation<E>,
    reduction_output: &mut DeviceAllocation<E>,
    reduction_temp_storage: &mut DeviceAllocation<u8>,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()>
where
    E: Field + Reduce,
    Mul: BinaryOp<E, E, E>,
{
    let stream = context.get_exec_stream();
    let eq_values = DeviceVectorChunk::new(eq_values, 0, acc_size);
    let reduction_temp = unsafe {
        DeviceSlice::from_raw_parts_mut(
            reduction_temp_storage.as_mut_ptr(),
            reduction_temp_storage.len(),
        )
    };

    {
        let mut low_half = DeviceVectorChunkMut::new(accumulator, 0, acc_size);
        mul_into_y(&eq_values, &mut low_half, stream)?;
        reduce(
            ReduceOperation::Sum,
            reduction_temp,
            &low_half,
            &mut reduction_output[0],
            stream,
        )?;
    }

    {
        let mut high_half = DeviceVectorChunkMut::new(accumulator, acc_size, acc_size);
        mul_into_y(&eq_values, &mut high_half, stream)?;
        reduce(
            ReduceOperation::Sum,
            reduction_temp,
            &high_half,
            &mut reduction_output[1],
            stream,
        )?;
    }

    Ok(())
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
    let r0 = size_of::<GpuGKRDimensionReducingRound0BatchCompact<E4>>();
    let cont = size_of::<GpuGKRDimensionReducingContinuationBatchCompact<E4>>();
    // Both must fit comfortably under the soft 16 KB target (and well
    // under the 32 KB hard ceiling enforced by `cudaLaunchKernelExC`).
    assert!(
        r0 <= KERNEL_ARG_SOFT_TARGET_BYTES,
        "round0 compact = {r0} B exceeds soft target {KERNEL_ARG_SOFT_TARGET_BYTES}"
    );
    assert!(
        cont <= KERNEL_ARG_SOFT_TARGET_BYTES,
        "continuation compact = {cont} B exceeds soft target {KERNEL_ARG_SOFT_TARGET_BYTES}"
    );
    assert!(r0 < KERNEL_ARG_HARD_CEILING_BYTES);
    assert!(cont < KERNEL_ARG_HARD_CEILING_BYTES);
}

#[test]
fn compact_record_is_16_bytes() {
    // Audit's projected post-compaction footprint depends on this size.
    assert_eq!(
        size_of::<GpuGKRDimensionReducingBatchRecordCompact>(),
        16,
        "compact batch record size must remain 16 bytes"
    );
}
