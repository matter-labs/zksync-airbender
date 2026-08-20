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

// ── Low-first factored-eq drain ─────────────────────────────────────────────

#[cfg(not(no_cuda))]
const EQ_DRAIN_CHALLENGE_COUNTS: [usize; 7] = [1, 2, 7, 8, 9, 16, 17];

/// Which fused-tail finalize launcher drives the fold.
#[cfg(not(no_cuda))]
#[derive(Clone, Copy, Debug)]
enum FinalizeVariant {
    /// Main-layer path: `launch_backward_dual_finalize_from_partials` over the
    /// warp-partial buffer (`main_layer/sumcheck_plan.rs`).
    FromPartials,
    /// Dimension-reducing single-launch path
    /// (`dual_reduce_num_stage1_blocks == 0`).
    FromAcc,
    /// Dimension-reducing two-stage path: blockwise reduce, then finalize.
    BlockwiseThenPartials,
}

#[cfg(not(no_cuda))]
struct EqSlabs {
    high: [Vec<E4>; GKR_EQ_HIGH_SLOTS],
    low: Vec<E4>,
}

/// Copies both factored-eq slot slabs back to the host. The high slabs are read
/// straight out of the `ab_gkr_eq_high` `__constant__` symbol through the
/// `cudaGetSymbolAddress` device pointer; the low slab is a plain global
/// `DeviceAllocation`.
#[cfg(not(no_cuda))]
fn read_eq_slabs(
    d_eq_low: &gpu_core::primitives::context::DeviceAllocation<E4>,
    context: &gpu_prover_context::ProverContext,
) -> EqSlabs {
    use era_cudart::memory::memory_copy_async;
    use era_cudart::slice::DeviceSlice;

    use crate::upstream::Field;

    let stream = context.get_exec_stream();
    let high_len = GKR_EQ_HIGH_SLOTS * GKR_EQ_GROUP_TABLE_LEN;
    let mut high_flat = vec![E4::ZERO; high_len];
    // SAFETY: `ab_gkr_eq_high` is exactly `high_len` E4 elements.
    let high_view = unsafe {
        DeviceSlice::from_raw_parts(get_eq_high_constant_device_ptr() as *const E4, high_len)
    };
    memory_copy_async(&mut high_flat, high_view, stream).unwrap();
    let mut low = vec![E4::ZERO; GKR_EQ_GROUP_TABLE_LEN];
    memory_copy_async(&mut low, d_eq_low, stream).unwrap();
    stream.synchronize().unwrap();

    EqSlabs {
        high: std::array::from_fn(|slot| {
            high_flat[slot * GKR_EQ_GROUP_TABLE_LEN..(slot + 1) * GKR_EQ_GROUP_TABLE_LEN].to_vec()
        }),
        low,
    }
}

/// Asserts the factored-eq state after `round` folds. `slice` is the eq
/// coordinate slice (`claim_point[1..]`), so the remaining suffix point is
/// `slice[round..]` with protocol coordinate `round + b` on physical row bit
/// `b`. Physical bit order is `[high[0] | high[1] | low]` from the top, so the
/// low slab owns the FIRST remaining coordinates.
#[cfg(not(no_cuda))]
fn assert_eq_state_matches_cpu(
    label: &str,
    round: usize,
    slice: &[E4],
    sizes: &GkrEqSizes,
    slabs: &EqSlabs,
    suffix_tables: &[Box<[E4]>],
    worker: &worker::Worker,
) {
    use crate::upstream::Field;

    let remaining = slice.len() - round;
    assert_eq!(
        sizes.low as usize + sizes.high[1] as usize + sizes.high[0] as usize,
        remaining,
        "{label} round {round}: slot widths {sizes:?} must sum to the {remaining} remaining coordinates",
    );

    let groups: [(&str, usize, &[E4]); 3] = [
        ("low", sizes.low as usize, &slabs.low),
        ("high[1]", sizes.high[1] as usize, &slabs.high[1]),
        ("high[0]", sizes.high[0] as usize, &slabs.high[0]),
    ];
    let mut consumed = round;
    for (name, size, slab) in groups {
        let coords = &slice[consumed..consumed + size];
        let expected =
            prover::gkr::sumcheck::eq_poly::make_eq_table_lsb_first::<E4>(coords, worker);
        let actual = &slab[..1usize << size];
        assert_eq!(expected.len(), actual.len());
        let divergence = actual
            .iter()
            .zip(expected.iter())
            .position(|(gpu, cpu)| gpu != cpu);
        assert!(
            divergence.is_none(),
            "{label} round {round}: {name} slab (width {size}, coordinates {consumed}..{}) \
             diverges from the CPU LSB table at entry {}",
            consumed + size,
            divergence.unwrap_or(0),
        );
        consumed += size;
    }

    // The three slabs must multiply back to the full remaining-suffix table
    // under exactly the index decomposition `gkr_compute_eq_inline` uses.
    let full = &suffix_tables[remaining];
    assert_eq!(full.len(), 1usize << remaining);
    let shift1 = sizes.low;
    let shift0 = sizes.low + sizes.high[1];
    for (gid, expected) in full.iter().enumerate() {
        let hi0 = (gid >> shift0) & ((1usize << sizes.high[0]) - 1);
        let hi1 = (gid >> shift1) & ((1usize << sizes.high[1]) - 1);
        let lo = gid & ((1usize << sizes.low) - 1);
        let mut product = slabs.high[0][hi0];
        product.mul_assign(&slabs.high[1][hi1]);
        product.mul_assign(&slabs.low[lo]);
        assert_eq!(
            product, *expected,
            "{label} round {round}: factored product disagrees with the CPU suffix table at gid {gid}",
        );
    }
}

/// Runs the real `gkr_eq_inline_reader` over the live slabs and compares the
/// weighted row sum against the CPU suffix table — the read-side half of the
/// contract (the slab checks cover the write side).
#[cfg(not(no_cuda))]
#[allow(clippy::too_many_arguments)]
fn assert_eq_inline_reads_match_cpu(
    label: &str,
    round: usize,
    remaining: usize,
    sizes: GkrEqSizes,
    eq_low: *const E4,
    raw_values: *const gpu_core::primitives::field::BF,
    weights: &[gpu_core::primitives::field::BF],
    d_block_partials: &mut gpu_core::primitives::context::DeviceAllocation<E4>,
    suffix_tables: &[Box<[E4]>],
    context: &gpu_prover_context::ProverContext,
) {
    use era_cudart::memory::memory_copy_async;

    use crate::upstream::{Field, FieldExtension};

    let trace_len = 1usize << remaining;
    launch_trace_holder_block_partials_eq_inline(
        raw_values,
        eq_low,
        sizes,
        d_block_partials.as_mut_ptr(),
        trace_len,
        0,
        1,
        1,
        context,
    )
    .unwrap();
    let mut from_gpu = vec![E4::ZERO; 1];
    memory_copy_async(&mut from_gpu, d_block_partials, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();

    let mut expected = E4::ZERO;
    for (eq, weight) in suffix_tables[remaining]
        .iter()
        .zip(weights[..trace_len].iter())
    {
        let mut term = *eq;
        term.mul_assign_by_base(weight);
        expected.add_assign(&term);
    }
    assert_eq!(
        from_gpu[0], expected,
        "{label} round {round}: inline-eq weighted row sum diverges (sizes {sizes:?})",
    );
}

/// Walks the whole simulated round loop for one `challenge_count` and one
/// finalize launcher, asserting EVERY intermediate eq state (including the
/// fresh build) against the CPU LSB oracle, that the dynamic drain matches the
/// static `drained_eq_sizes` mirror, and that un-drained high slabs stay
/// byte-identical in constant memory.
#[cfg(not(no_cuda))]
fn drive_low_first_eq_drain(
    challenge_count: usize,
    variant: FinalizeVariant,
    probe_eq_inline: bool,
) {
    use era_cudart::memory::memory_copy_async;
    use era_cudart::slice::DeviceSlice;
    use gpu_core::allocator::tracker::AllocationPlacement;
    use gpu_core::primitives::context::DeviceAllocation;
    use gpu_core::primitives::field::BF;
    use rand::rngs::StdRng;
    use rand::{Rng, SeedableRng};
    use worker::Worker;

    use crate::backward::vm::production_bind::drained_eq_sizes;
    use crate::test_utils::make_test_context;
    use crate::upstream::{Field, PrimeField};

    let label = &format!("{variant:?} challenge_count={challenge_count}");
    let context = make_test_context(256, 64);
    let stream = context.get_exec_stream();
    let worker = Worker::new();
    let mut rng = StdRng::seed_from_u64(0x4e71_d004 ^ challenge_count as u64);
    let mut random_e4 = move || {
        E4::from_array_of_base(std::array::from_fn(|_| {
            BF::from_u32_with_reduction(rng.random())
        }))
    };

    // `challenge_offset = 1` mirrors both production callers.
    let point: Vec<E4> = (0..challenge_count + 1).map(|_| random_e4()).collect();
    let slice = &point[1..];
    let suffix_tables =
        prover::gkr::sumcheck::eq_poly::make_eq_poly_in_full_lsb::<E4>(slice, &worker);
    assert_eq!(suffix_tables.len(), challenge_count + 1);

    let mut d_point: DeviceAllocation<E4> = context
        .alloc(point.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut d_point, &point, stream).unwrap();
    let mut d_eq_low: DeviceAllocation<E4> = context
        .alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::Top)
        .unwrap();

    let mut d_seed: DeviceAllocation<u32> = context.alloc(8, AllocationPlacement::Top).unwrap();
    let seed_host = vec![0x1234_5678u32; 8];
    memory_copy_async(&mut d_seed, &seed_host, stream).unwrap();
    let mut d_claim: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::Top).unwrap();
    let mut d_eq_prefactor: DeviceAllocation<E4> =
        context.alloc(1, AllocationPlacement::Top).unwrap();
    let mut d_coeffs: DeviceAllocation<E4> = context.alloc(4, AllocationPlacement::Top).unwrap();
    let mut d_challenge: DeviceAllocation<E4> = context.alloc(1, AllocationPlacement::Top).unwrap();
    let mut d_prev_coord: DeviceAllocation<E4> =
        context.alloc(1, AllocationPlacement::Top).unwrap();
    memory_copy_async(&mut d_prev_coord, &point[..1], stream).unwrap();
    let one = vec![E4::ONE];

    // Source pairs for the round-update reduction; the eq fold ignores them,
    // but they must be finite so `e4::inv(eq_prefactor)` stays defined.
    let (acc_size, num_partials) = match variant {
        FinalizeVariant::FromPartials => (0usize, 8usize),
        FinalizeVariant::FromAcc => (64usize, 0usize),
        FinalizeVariant::BlockwiseThenPartials => (1024usize, 0usize),
    };
    let source_len = 2 * acc_size.max(num_partials);
    let mut d_source: DeviceAllocation<E4> =
        context.alloc(source_len, AllocationPlacement::Top).unwrap();
    let source_host: Vec<E4> = (0..source_len).map(|_| random_e4()).collect();
    memory_copy_async(&mut d_source, &source_host, stream).unwrap();
    let stage1_blocks = dual_reduce_num_stage1_blocks(acc_size);
    let mut d_partials: DeviceAllocation<E4> = context
        .alloc(2 * stage1_blocks.max(1), AllocationPlacement::Top)
        .unwrap();

    // Inline-eq probe inputs: index-derived DISTINCT base-field weights, held
    // in an E4-aligned allocation for the kernel's 16-byte `bf4` loads.
    let probe_rows = 1usize << challenge_count;
    let weights: Vec<BF> = (0..probe_rows)
        .map(|row| {
            BF::from_u32_with_reduction((row as u32).wrapping_mul(2_654_435_761).wrapping_add(7))
        })
        .collect();
    let mut d_weights: DeviceAllocation<E4> = context
        .alloc((probe_rows / 4).max(1), AllocationPlacement::Top)
        .unwrap();
    // SAFETY: the E4 allocation covers `probe_rows` BF elements and is
    // 16-byte aligned.
    let d_weights_bf =
        unsafe { DeviceSlice::from_raw_parts_mut(d_weights.as_mut_ptr() as *mut BF, probe_rows) };
    memory_copy_async(d_weights_bf, &weights, stream).unwrap();
    let weights_ptr = d_weights_bf.as_ptr();
    let mut d_block_partials: DeviceAllocation<E4> =
        context.alloc(1, AllocationPlacement::Top).unwrap();

    launch_build_eq_high_and_low_groups_from_point(
        d_point.as_ptr(),
        1,
        challenge_count,
        get_eq_high_constant_device_ptr(),
        d_eq_low.as_mut_ptr(),
        &context,
    )
    .unwrap();
    let mut eq_sizes = make_eq_sizes(challenge_count);

    let mut previous: Option<(GkrEqSizes, EqSlabs)> = None;
    for round in 0..=challenge_count {
        if round > 0 {
            memory_copy_async(&mut d_claim, &one, stream).unwrap();
            memory_copy_async(&mut d_eq_prefactor, &one, stream).unwrap();
            let (slot_base, size_before) = resolve_active_eq_slot(&eq_sizes, d_eq_low.as_mut_ptr());
            assert!(
                size_before >= 1,
                "{label} round {round}: the active slot must still hold a coordinate",
            );
            match variant {
                FinalizeVariant::FromPartials => launch_backward_dual_finalize_from_partials(
                    d_source.as_ptr(),
                    num_partials,
                    d_prev_coord.as_ptr(),
                    d_seed.as_mut_ptr(),
                    d_claim.as_mut_ptr(),
                    d_eq_prefactor.as_mut_ptr(),
                    d_coeffs.as_mut_ptr(),
                    d_challenge.as_mut_ptr(),
                    slot_base,
                    size_before,
                    &context,
                )
                .unwrap(),
                FinalizeVariant::FromAcc => launch_backward_dual_finalize_from_acc(
                    d_source.as_ptr(),
                    acc_size,
                    d_prev_coord.as_ptr(),
                    d_seed.as_mut_ptr(),
                    d_claim.as_mut_ptr(),
                    d_eq_prefactor.as_mut_ptr(),
                    d_coeffs.as_mut_ptr(),
                    d_challenge.as_mut_ptr(),
                    slot_base,
                    size_before,
                    &context,
                )
                .unwrap(),
                FinalizeVariant::BlockwiseThenPartials => {
                    assert!(stage1_blocks > 0);
                    launch_backward_dual_reduce_blockwise(
                        d_source.as_ptr(),
                        acc_size,
                        d_partials.as_mut_ptr(),
                        &context,
                    )
                    .unwrap();
                    launch_backward_dual_finalize_from_partials(
                        d_partials.as_ptr(),
                        stage1_blocks,
                        d_prev_coord.as_ptr(),
                        d_seed.as_mut_ptr(),
                        d_claim.as_mut_ptr(),
                        d_eq_prefactor.as_mut_ptr(),
                        d_coeffs.as_mut_ptr(),
                        d_challenge.as_mut_ptr(),
                        slot_base,
                        size_before,
                        &context,
                    )
                    .unwrap();
                }
            }
            record_active_eq_slot_fold(&mut eq_sizes);
        }

        assert_eq!(
            eq_sizes,
            drained_eq_sizes(make_eq_sizes(challenge_count), round as u8),
            "{label} round {round}: the dynamic drain and the static descriptor mirror disagree",
        );

        let slabs = read_eq_slabs(&d_eq_low, &context);
        assert_eq_state_matches_cpu(
            label,
            round,
            slice,
            &eq_sizes,
            &slabs,
            &suffix_tables,
            &worker,
        );

        if round == 0 {
            // Non-vacuity: a half-sum substitution or a lost store is only
            // detectable while the slab entries are pairwise distinct.
            for (slot, width) in [
                (&slabs.low, eq_sizes.low),
                (&slabs.high[1], eq_sizes.high[1]),
                (&slabs.high[0], eq_sizes.high[0]),
            ] {
                let entries = &slot[..1usize << width];
                for (i, left) in entries.iter().enumerate() {
                    for right in &entries[i + 1..] {
                        assert_ne!(left, right, "{label}: fresh slab entries must be distinct");
                    }
                }
            }
        }

        let remaining = challenge_count - round;
        if probe_eq_inline && remaining >= 2 {
            assert_eq_inline_reads_match_cpu(
                label,
                round,
                remaining,
                eq_sizes,
                d_eq_low.as_ptr(),
                weights_ptr,
                &weights,
                &mut d_block_partials,
                &suffix_tables,
                &context,
            );
        }

        if let Some((previous_sizes, previous_slabs)) = previous.as_ref() {
            for slot in 0..GKR_EQ_HIGH_SLOTS {
                if eq_sizes.high[slot] == previous_sizes.high[slot] {
                    assert_eq!(
                        slabs.high[slot], previous_slabs.high[slot],
                        "{label} round {round}: un-drained constant-memory high slab {slot} \
                         must stay byte-identical across rounds",
                    );
                }
            }
        }
        previous = Some((eq_sizes, slabs));
    }

    assert_eq!(eq_sizes, GkrEqSizes::zeroed());
}

/// Main-layer finalize launcher: the factored eq must drain LOW slot first,
/// then `high[1]`, then `high[0]`, each round contracting the ACTIVE slot's
/// lowest bit (`dst[i] = src[2i] + src[2i+1]`). Oracle is the live CPU
/// `make_eq_poly_in_full_lsb` / `make_eq_table_lsb_first` pair.
#[test]
#[cfg(not(no_cuda))]
fn factored_eq_drains_low_first_through_from_partials() {
    for challenge_count in EQ_DRAIN_CHALLENGE_COUNTS {
        drive_low_first_eq_drain(challenge_count, FinalizeVariant::FromPartials, true);
    }
}

/// Dimension-reducing single-launch finalize path.
#[test]
#[cfg(not(no_cuda))]
fn factored_eq_drains_low_first_through_from_acc() {
    for challenge_count in EQ_DRAIN_CHALLENGE_COUNTS {
        drive_low_first_eq_drain(challenge_count, FinalizeVariant::FromAcc, false);
    }
}

/// Dimension-reducing two-stage finalize path.
#[test]
#[cfg(not(no_cuda))]
fn factored_eq_drains_low_first_through_blockwise_partials() {
    for challenge_count in EQ_DRAIN_CHALLENGE_COUNTS {
        drive_low_first_eq_drain(
            challenge_count,
            FinalizeVariant::BlockwiseThenPartials,
            false,
        );
    }
}

/// The segmented VM stamps its descriptors from `drained_eq_sizes`, a pure
/// function of the round index. Walk it against the dynamic drain the fused
/// tail applies, for every challenge count the 3-slot layout can hold.
#[test]
fn drained_eq_sizes_mirrors_the_dynamic_drain() {
    use crate::backward::vm::production_bind::drained_eq_sizes;

    for challenge_count in 1..=(GKR_EQ_GROUP_SIZE * (GKR_EQ_HIGH_SLOTS + 1)) {
        let mut dynamic = make_eq_sizes(challenge_count);
        for round in 0..=challenge_count {
            assert_eq!(
                dynamic,
                drained_eq_sizes(make_eq_sizes(challenge_count), round as u8),
                "challenge_count={challenge_count} round={round}",
            );
            if round < challenge_count {
                record_active_eq_slot_fold(&mut dynamic);
            }
        }
        assert_eq!(dynamic, GkrEqSizes::zeroed());
    }
}
