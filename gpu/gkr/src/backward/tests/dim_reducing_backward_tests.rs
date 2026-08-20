//! Arithmetic oracle for the dimension-reducing backward rounds.
//!
//! The reference below is a LOCAL transcription of the LSB index invariants of
//! `prover/src/gkr/prover/dimension_reduction/lsb_backward.rs` (the CPU scalar
//! chunks are `pub(crate)` there and not callable across crates):
//!
//! * an input poly is indexed `2*Y + b` with the gate bit `b` lowest, and a
//!   round pairs `Y = 2j` with `Y = 2j + 1`, so row `j` owns the four
//!   consecutive values `[4j, 4j+1, 4j+2, 4j+3]` and the round pairs an index
//!   with `index + 2`;
//! * round zero reads `h(0)` from the output poly at `2j`;
//! * a continuation folds the ancestor pair `(2*(c & !1) + (c & 1), that + 2)`
//!   into current index `c`, i.e.
//!   `dst[2*(2j+yy)+b] = fold(src[2*(4j+2yy)+b], src[2*(4j+2yy+1)+b])`.

use std::collections::BTreeSet;

use era_cudart::memory::memory_copy_async;
use era_cudart::slice::{CudaSlice, CudaSliceMut, DeviceSlice};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

use crate::backward::kernels::{
    dim_reducing_slot_index, get_dim_reducing_layer_claim_point_device_ptr,
    get_eq_high_constant_device_ptr, launch_build_eq_high_and_low_groups_from_point,
    launch_dim_reducing_continuation_batched_compact, launch_dim_reducing_round0_batched_compact,
    make_eq_sizes, pack_cache_u16, pack_source_u16,
    schedule_dim_reducing_batch_challenge_table_prelude, GkrEqSizes, GpuGKRDimensionReducingBatch,
    GpuGKRDimensionReducingSlot, GpuGKRSourceRecord, GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN,
    GKR_DIM_REDUCING_INPUTS_PER_SLOT, GKR_DIM_REDUCING_IO_PER_SLOT,
    GKR_DIM_REDUCING_OUTPUTS_PER_SLOT, GKR_DIM_REDUCING_SLOTS, GKR_EQ_GROUP_TABLE_LEN,
    GKR_EQ_HIGH_SLOTS, MAX_DIM_REDUCING_LAYER_CLAIM_POINT_LEN,
};
use crate::test_utils::make_test_context;
use crate::upstream::{Field, OutputType, PrimeField};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::{BF, E4};
use gpu_prover_context::ProverContext;

const SOURCE_BASE_SLOT: u8 = 0;
const AUX_BASE_SLOT: u8 = 1;
/// Distinct poly slots the fixture uses per base: two per enabled slot.
const POLY_COUNT: usize = GKR_DIM_REDUCING_SLOTS * GKR_DIM_REDUCING_INPUTS_PER_SLOT;
/// One extra never-referenced poly per base, used as an overrun tripwire.
const GUARD_POLY: usize = POLY_COUNT;

fn slot_is_pairwise(slot: usize) -> bool {
    slot == dim_reducing_slot_index(OutputType::PermutationProduct)
        || slot == dim_reducing_slot_index(OutputType::InitsAndTeardownsProduct)
}

fn poison() -> E4 {
    E4::from_array_of_base(std::array::from_fn(|i| {
        BF::from_u32_with_reduction(0x0bad_beef + i as u32)
    }))
}

fn random_e4(rng: &mut StdRng) -> E4 {
    E4::from_array_of_base(std::array::from_fn(|_| {
        BF::from_u32_with_reduction(rng.random())
    }))
}

fn sub(a: &E4, b: &E4) -> E4 {
    let mut v = *a;
    v.sub_assign(b);
    v
}

fn mul(a: &E4, b: &E4) -> E4 {
    let mut v = *a;
    v.mul_assign(b);
    v
}

fn upload(context: &ProverContext, host: &[E4]) -> DeviceAllocation<E4> {
    let mut device: DeviceAllocation<E4> = context
        .alloc(host.len(), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut device, host, context.get_exec_stream()).unwrap();
    device
}

fn download(context: &ProverContext, device: &DeviceAllocation<E4>) -> Vec<E4> {
    let mut host = vec![E4::ZERO; device.len()];
    memory_copy_async(&mut host, device, context.get_exec_stream()).unwrap();
    context.get_exec_stream().synchronize().unwrap();
    host
}

fn write_symbol(context: &ProverContext, ptr: *mut E4, host: &[E4]) {
    // SAFETY: both symbols used here are at least `host.len()` E4 long, as
    // pinned by MAX_DIM_REDUCING_LAYER_CLAIM_POINT_LEN and the eq-high shape.
    let view = unsafe { DeviceSlice::from_raw_parts_mut(ptr, host.len()) };
    memory_copy_async(view, host, context.get_exec_stream()).unwrap();
}

/// Poisons the whole layer-claim-point symbol except the slot the continuation
/// kernel must read, so an off-by-one on the challenge index shows up as a
/// mismatch rather than as a silent alias.
fn write_folding_challenge(context: &ProverContext, step: usize, challenge: E4) {
    let mut host = vec![poison(); MAX_DIM_REDUCING_LAYER_CLAIM_POINT_LEN];
    host[step - 1] = challenge;
    write_symbol(
        context,
        get_dim_reducing_layer_claim_point_device_ptr(),
        &host,
    );
}

/// `eq == 1` on every row: both high slabs and the low slab hold ONE and the
/// size descriptor is all-zero, so every row reads slot 0 of each.
fn install_identity_eq(context: &ProverContext) -> (DeviceAllocation<E4>, GkrEqSizes) {
    let ones = vec![E4::ONE; GKR_EQ_HIGH_SLOTS * GKR_EQ_GROUP_TABLE_LEN];
    write_symbol(context, get_eq_high_constant_device_ptr(), &ones);
    let low = upload(context, &vec![E4::ONE; GKR_EQ_GROUP_TABLE_LEN]);
    (
        low,
        GkrEqSizes {
            high: [0; GKR_EQ_HIGH_SLOTS],
            low: 0,
        },
    )
}

/// The production factored-eq build over `point[1..]`, mirroring
/// `schedule_execute_dimension_reducing_layer`.
fn install_point_eq(
    context: &ProverContext,
    point: &[E4],
    challenge_count: usize,
) -> (DeviceAllocation<E4>, GkrEqSizes) {
    let d_point = upload(context, point);
    let mut low: DeviceAllocation<E4> = context
        .alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::Top)
        .unwrap();
    launch_build_eq_high_and_low_groups_from_point(
        d_point.as_ptr(),
        1,
        challenge_count,
        get_eq_high_constant_device_ptr(),
        low.as_mut_ptr(),
        context,
    )
    .unwrap();
    context.get_exec_stream().synchronize().unwrap();
    (low, make_eq_sizes(challenge_count))
}

/// Powers of a random base, installed through the production prelude and
/// mirrored on the host (`table[i] == base^i`).
fn install_batch_challenges(context: &ProverContext, base: E4) -> (DeviceAllocation<E4>, Vec<E4>) {
    let d_base = upload(context, &[base]);
    schedule_dim_reducing_batch_challenge_table_prelude(d_base.as_ptr(), context).unwrap();
    let mut table = Vec::with_capacity(GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN);
    let mut acc = E4::ONE;
    for _ in 0..GKR_DIM_REDUCING_BATCH_CHALLENGE_TABLE_LEN {
        table.push(acc);
        acc.mul_assign(&base);
    }
    (d_base, table)
}

/// One enabled slot of the fixture: the poly index each input reads in the
/// source base, the poly index it folds into in the destination base, and the
/// output poly round zero reads.
#[derive(Clone, Copy, Debug)]
struct FixtureSlot {
    slot: usize,
    pairwise: bool,
    src: [u16; GKR_DIM_REDUCING_INPUTS_PER_SLOT],
    cache: [u16; GKR_DIM_REDUCING_INPUTS_PER_SLOT],
    outputs: [u16; GKR_DIM_REDUCING_OUTPUTS_PER_SLOT],
    batch_exp: [u16; GKR_DIM_REDUCING_OUTPUTS_PER_SLOT],
    first_access: [bool; GKR_DIM_REDUCING_INPUTS_PER_SLOT],
}

/// All five slots enabled with distinct polys, except that `share_last_input`
/// makes the top slot re-read the bottom slot's polys — the
/// `first_access == false` path where a slot reads a fold another slot already
/// wrote.
///
/// `distinct_cache` mirrors step 1, where the source poly index (consolidated
/// ext storage) differs from the destination poly index (dense folding arena);
/// later steps carry the same index in both.
fn fixture_slots(share_last_input: bool, distinct_cache: bool) -> Vec<FixtureSlot> {
    let mut slots = Vec::with_capacity(GKR_DIM_REDUCING_SLOTS);
    let mut seen_cache = BTreeSet::new();
    for slot in 0..GKR_DIM_REDUCING_SLOTS {
        let base = (slot * GKR_DIM_REDUCING_INPUTS_PER_SLOT) as u16;
        let src: [u16; GKR_DIM_REDUCING_INPUTS_PER_SLOT] =
            if share_last_input && slot + 1 == GKR_DIM_REDUCING_SLOTS {
                [0, 1]
            } else {
                [base, base + 1]
            };
        let last = POLY_COUNT as u16 - 1;
        let cache: [u16; GKR_DIM_REDUCING_INPUTS_PER_SLOT] = if distinct_cache {
            [last - src[0], last - src[1]]
        } else {
            src
        };
        let first_access = [seen_cache.insert(cache[0]), seen_cache.insert(cache[1])];
        slots.push(FixtureSlot {
            slot,
            pairwise: slot_is_pairwise(slot),
            src,
            cache,
            outputs: [base, base + 1],
            batch_exp: [2 * slot as u16, 2 * slot as u16 + 1],
            first_access,
        });
    }
    slots
}

#[allow(clippy::too_many_arguments)]
fn build_batch(
    slots: &[FixtureSlot],
    source_base: *const u8,
    source_log2_stride: u32,
    aux_base: *const u8,
    aux_log2_stride: u32,
    round_zero: bool,
    eq_low: *const E4,
    eq_sizes: GkrEqSizes,
    contributions: *mut E4,
) -> GpuGKRDimensionReducingBatch<E4> {
    let mut batch = GpuGKRDimensionReducingBatch::<E4> {
        enabled_mask: slots.iter().fold(0u32, |mask, s| mask | (1u32 << s.slot)),
        eq_low,
        eq_sizes,
        contributions,
        ..Default::default()
    };
    batch.tables.bases[SOURCE_BASE_SLOT as usize] = source_base;
    batch.tables.log2_stride[SOURCE_BASE_SLOT as usize] = source_log2_stride;
    batch.tables.bases[AUX_BASE_SLOT as usize] = aux_base;
    batch.tables.log2_stride[AUX_BASE_SLOT as usize] = aux_log2_stride;
    for fixture in slots {
        let mut io = [GpuGKRSourceRecord::default(); GKR_DIM_REDUCING_IO_PER_SLOT];
        let (inputs, outputs) = io.split_at_mut(GKR_DIM_REDUCING_INPUTS_PER_SLOT);
        for (k, record) in inputs.iter_mut().enumerate() {
            *record = if round_zero {
                GpuGKRSourceRecord::source_only(pack_source_u16(
                    false,
                    SOURCE_BASE_SLOT,
                    fixture.src[k],
                ))
            } else {
                GpuGKRSourceRecord::new(
                    pack_source_u16(fixture.first_access[k], SOURCE_BASE_SLOT, fixture.src[k]),
                    pack_cache_u16(AUX_BASE_SLOT, fixture.cache[k]),
                )
            };
        }
        if round_zero {
            for (k, record) in outputs.iter_mut().enumerate() {
                *record = GpuGKRSourceRecord::source_only(pack_source_u16(
                    false,
                    AUX_BASE_SLOT,
                    fixture.outputs[k],
                ));
            }
        }
        batch.slots[fixture.slot] = GpuGKRDimensionReducingSlot {
            io,
            batch_exp: fixture.batch_exp,
        };
    }
    batch
}

/// `dst[c] = src[lo] + r * (src[hi] - src[lo])` with `lo = 2*(c & !1) + (c & 1)`
/// and `hi = lo + 2`.
fn host_fold(src: &[E4], dst_len: usize, r: &E4) -> Vec<E4> {
    (0..dst_len)
        .map(|c| {
            let lo_idx = 2 * (c & !1) + (c & 1);
            let lo = src[lo_idx];
            let mut v = sub(&src[lo_idx + 2], &lo);
            v.mul_assign(r);
            v.add_assign(&lo);
            v
        })
        .collect()
}

/// The `[h(0), h(inf)]` contributions, row by row.
///
/// `values[value_index(slot, k)]` is input `k` of `slot` in the CURRENT round
/// layout (round zero: the layer's input poly; continuation: the folded poly).
/// `outputs` is `Some` only for round zero, where `h(0)` is read from the output
/// layer at index `2j`.
fn host_contributions(
    acc_size: usize,
    slots: &[FixtureSlot],
    value_index: impl Fn(&FixtureSlot, usize) -> usize,
    values: &[Vec<E4>],
    outputs: Option<&[Vec<E4>]>,
    batch_challenges: &[E4],
    eq: &[E4],
) -> Vec<E4> {
    let mut out = vec![E4::ZERO; 2 * acc_size];
    for j in 0..acc_size {
        let mut total0 = E4::ZERO;
        let mut total1 = E4::ZERO;
        let (even, odd) = (4 * j, 4 * j + 1);
        for fixture in slots {
            let bc = [
                batch_challenges[fixture.batch_exp[0] as usize],
                batch_challenges[fixture.batch_exp[1] as usize],
            ];
            let poly = |k: usize| &values[value_index(fixture, k)];
            let f0 = |k: usize, index: usize| poly(k)[index];
            let delta = |k: usize, index: usize| sub(&poly(k)[index + 2], &poly(k)[index]);
            if fixture.pairwise {
                for t in 0..GKR_DIM_REDUCING_OUTPUTS_PER_SLOT {
                    let v0 = match outputs {
                        Some(outs) => outs[fixture.outputs[t] as usize][2 * j],
                        None => mul(&f0(t, even), &f0(t, odd)),
                    };
                    total0.add_assign(&mul(&bc[t], &v0));
                    total1.add_assign(&mul(&bc[t], &mul(&delta(t, even), &delta(t, odd))));
                }
            } else {
                let (num0, den0) = match outputs {
                    Some(outs) => (
                        outs[fixture.outputs[0] as usize][2 * j],
                        outs[fixture.outputs[1] as usize][2 * j],
                    ),
                    None => {
                        let (a, b, c, d) = (f0(0, even), f0(1, even), f0(0, odd), f0(1, odd));
                        let mut num = mul(&a, &d);
                        num.add_assign(&mul(&c, &b));
                        (num, mul(&b, &d))
                    }
                };
                let (a, b, c, d) = (delta(0, even), delta(1, even), delta(0, odd), delta(1, odd));
                let mut numinf = mul(&a, &d);
                numinf.add_assign(&mul(&c, &b));
                let deninf = mul(&b, &d);
                total0.add_assign(&mul(&bc[0], &num0));
                total0.add_assign(&mul(&bc[1], &den0));
                total1.add_assign(&mul(&bc[0], &numinf));
                total1.add_assign(&mul(&bc[1], &deninf));
            }
        }
        out[j] = mul(&total0, &eq[j]);
        out[acc_size + j] = mul(&total1, &eq[j]);
    }
    out
}

fn assert_e4_slices_eq(gpu: &[E4], expected: &[E4], what: &str) {
    assert_eq!(gpu.len(), expected.len(), "{what}: length");
    let divergence = gpu.iter().zip(expected.iter()).position(|(g, e)| g != e);
    assert!(
        divergence.is_none(),
        "{what}: first divergent index {:?} (bits {:b}), gpu {:?} expected {:?}",
        divergence,
        divergence.unwrap_or(0),
        divergence.map(|i| gpu[i]),
        divergence.map(|i| expected[i]),
    );
}

fn split_polys(flat: &[E4], polys: usize, stride: usize) -> Vec<Vec<E4>> {
    (0..polys)
        .map(|p| flat[p * stride..(p + 1) * stride].to_vec())
        .collect()
}

/// Input pattern of a case.
#[derive(Clone, Copy, Debug)]
enum Fill {
    Random,
    /// Poly `0` of the source base becomes `e_offset` (a true basis vector,
    /// which the fold path is linear in); every other poly stays random so the
    /// quadratic gates keep both operands live.
    Basis(usize),
}

fn fill_source(polys: usize, stride: usize, fill: Fill, rng: &mut StdRng) -> Vec<E4> {
    let mut flat: Vec<E4> = (0..polys * stride).map(|_| random_e4(rng)).collect();
    if let Fill::Basis(offset) = fill {
        let offset = offset % stride;
        for (i, cell) in flat[..stride].iter_mut().enumerate() {
            *cell = if i == offset { E4::ONE } else { E4::ZERO };
        }
    }
    flat
}

struct Round0Case {
    acc_size: usize,
    fill: Fill,
    point_eq: bool,
}

fn run_round0_case(context: &ProverContext, case: &Round0Case, rng: &mut StdRng) {
    let acc_size = case.acc_size;
    let input_len = 4 * acc_size;
    let output_len = 2 * acc_size;
    let slots = fixture_slots(false, false);

    let (_d_base, batch_challenges) = install_batch_challenges(context, random_e4(rng));

    let inputs_flat = fill_source(POLY_COUNT + 1, input_len, case.fill, rng);
    let outputs_flat: Vec<E4> = (0..(POLY_COUNT + 1) * output_len)
        .map(|_| random_e4(rng))
        .collect();
    let d_inputs = upload(context, &inputs_flat);
    let d_outputs = upload(context, &outputs_flat);

    let challenge_count = acc_size.trailing_zeros() as usize;
    let (eq_low, eq_sizes, eq_host) = if case.point_eq {
        let point: Vec<E4> = (0..challenge_count + 1).map(|_| random_e4(rng)).collect();
        let (low, sizes) = install_point_eq(context, &point, challenge_count);
        let host = prover::gkr::sumcheck::eq_poly::make_eq_table_lsb_first::<E4>(
            &point[1..],
            &worker::Worker::new(),
        );
        (low, sizes, host)
    } else {
        let (low, sizes) = install_identity_eq(context);
        (low, sizes, vec![E4::ONE; acc_size])
    };
    assert_eq!(eq_host.len(), acc_size);

    let mut d_contributions = upload(context, &vec![poison(); 2 * acc_size]);
    let batch = build_batch(
        &slots,
        d_inputs.as_ptr() as *const u8,
        input_len.trailing_zeros(),
        d_outputs.as_ptr() as *const u8,
        output_len.trailing_zeros(),
        true,
        eq_low.as_ptr(),
        eq_sizes,
        d_contributions.as_mut_ptr(),
    );
    launch_dim_reducing_round0_batched_compact(&batch, acc_size, context).unwrap();
    let from_gpu = download(context, &d_contributions);

    let expected = host_contributions(
        acc_size,
        &slots,
        |fixture, k| fixture.src[k] as usize,
        &split_polys(&inputs_flat, POLY_COUNT + 1, input_len),
        Some(&split_polys(&outputs_flat, POLY_COUNT + 1, output_len)),
        &batch_challenges,
        &eq_host,
    );
    assert_e4_slices_eq(
        &from_gpu,
        &expected,
        &format!(
            "round0 acc_size={acc_size} fill={:?} point_eq={}",
            case.fill, case.point_eq
        ),
    );
}

struct ContinuationCase {
    acc_size: usize,
    step: usize,
    fill: Fill,
    distinct_cache: bool,
    share_last_input: bool,
}

fn run_continuation_case(context: &ProverContext, case: &ContinuationCase, rng: &mut StdRng) {
    let acc_size = case.acc_size;
    let source_len = 8 * acc_size;
    let dest_len = 4 * acc_size;
    let slots = fixture_slots(case.share_last_input, case.distinct_cache);

    let (_d_base, batch_challenges) = install_batch_challenges(context, random_e4(rng));
    let folding_challenge = random_e4(rng);
    write_folding_challenge(context, case.step, folding_challenge);

    let source_flat = fill_source(POLY_COUNT + 1, source_len, case.fill, rng);
    let d_source = upload(context, &source_flat);
    let d_dest = upload(context, &vec![poison(); (POLY_COUNT + 1) * dest_len]);
    let (eq_low, eq_sizes) = install_identity_eq(context);

    let mut d_contributions = upload(context, &vec![poison(); 2 * acc_size]);
    let batch = build_batch(
        &slots,
        d_source.as_ptr() as *const u8,
        source_len.trailing_zeros(),
        d_dest.as_ptr() as *const u8,
        dest_len.trailing_zeros(),
        false,
        eq_low.as_ptr(),
        eq_sizes,
        d_contributions.as_mut_ptr(),
    );
    launch_dim_reducing_continuation_batched_compact(&batch, acc_size, case.step, context).unwrap();
    let contributions_gpu = download(context, &d_contributions);
    let dest_gpu = download(context, &d_dest);

    let source = split_polys(&source_flat, POLY_COUNT + 1, source_len);
    let mut folded = vec![vec![poison(); dest_len]; POLY_COUNT + 1];
    let mut referenced = BTreeSet::new();
    for fixture in slots.iter() {
        for k in 0..GKR_DIM_REDUCING_INPUTS_PER_SLOT {
            let cache = fixture.cache[k] as usize;
            let expected = host_fold(
                &source[fixture.src[k] as usize],
                dest_len,
                &folding_challenge,
            );
            if referenced.insert(cache) {
                folded[cache] = expected;
            } else {
                assert_eq!(
                    folded[cache], expected,
                    "fixture aliases one cache slot to two different source polys"
                );
            }
        }
    }

    let label = format!(
        "continuation acc_size={acc_size} step={} fill={:?} distinct_cache={} shared={}",
        case.step, case.fill, case.distinct_cache, case.share_last_input
    );
    for cache in referenced.iter().copied() {
        assert_e4_slices_eq(
            &dest_gpu[cache * dest_len..(cache + 1) * dest_len],
            &folded[cache],
            &format!("{label} fold poly {cache}"),
        );
    }
    assert!(
        dest_gpu[GUARD_POLY * dest_len..]
            .iter()
            .all(|v| *v == poison()),
        "{label}: the destination arena's guard poly was written",
    );

    let expected = host_contributions(
        acc_size,
        &slots,
        |fixture, k| fixture.cache[k] as usize,
        &folded,
        None,
        &batch_challenges,
        &vec![E4::ONE; acc_size],
    );
    assert_e4_slices_eq(
        &contributions_gpu,
        &expected,
        &format!("{label} accumulator"),
    );
}

#[test]
fn dim_reducing_backward_matches_cpu_lsb() {
    let context = make_test_context(256, 64);
    let mut rng = StdRng::seed_from_u64(0x5e_ed_10_5b);

    for acc_size in [1usize, 2, 8, 256] {
        for fill in [Fill::Random, Fill::Basis(0), Fill::Basis(5)] {
            run_round0_case(
                &context,
                &Round0Case {
                    acc_size,
                    fill,
                    point_eq: false,
                },
                &mut rng,
            );
            if acc_size >= 2 {
                run_round0_case(
                    &context,
                    &Round0Case {
                        acc_size,
                        fill,
                        point_eq: true,
                    },
                    &mut rng,
                );
            }
            // Step 1: first access, source poly index != destination poly index.
            run_continuation_case(
                &context,
                &ContinuationCase {
                    acc_size,
                    step: 1,
                    fill,
                    distinct_cache: true,
                    share_last_input: false,
                },
                &mut rng,
            );
            // A later step: arena to arena, with one input poly shared so a slot
            // reads a fold another slot already wrote.
            run_continuation_case(
                &context,
                &ContinuationCase {
                    acc_size,
                    step: 3,
                    fill,
                    distinct_cache: false,
                    share_last_input: true,
                },
                &mut rng,
            );
        }
    }
}

/// Basis-vector sweep over the last continuation's source, pinning the
/// `[00, 01, 10, 11]` order of the four values this producer hands to the
/// final-evaluation gather: slot `2*Y + b`, surviving sumcheck coordinate `Y`
/// above gate bit `b`.
#[test]
fn dim_reducing_backward_final_evaluation_packing_is_lsb() {
    let context = make_test_context(64, 16);
    let mut rng = StdRng::seed_from_u64(0x1a_57_5f_ac);

    let acc_size = 1usize;
    let source_len = 8;
    let dest_len = 4;
    let step = 2usize;
    let slots = fixture_slots(false, false);
    let folding_challenge = random_e4(&mut rng);
    let mut one_minus_r = E4::ONE;
    one_minus_r.sub_assign(&folding_challenge);

    let (_d_base, _batch_challenges) = install_batch_challenges(&context, E4::ONE);
    let (eq_low, eq_sizes) = install_identity_eq(&context);
    write_folding_challenge(&context, step, folding_challenge);

    for ancestor in 0..source_len {
        let source_flat: Vec<E4> = (0..(POLY_COUNT + 1) * source_len)
            .map(|i| {
                if i % source_len == ancestor {
                    E4::ONE
                } else {
                    E4::ZERO
                }
            })
            .collect();
        let d_source = upload(&context, &source_flat);
        let d_dest = upload(&context, &vec![poison(); (POLY_COUNT + 1) * dest_len]);
        let mut d_contributions = upload(&context, &vec![poison(); 2 * acc_size]);
        let batch = build_batch(
            &slots,
            d_source.as_ptr() as *const u8,
            source_len.trailing_zeros(),
            d_dest.as_ptr() as *const u8,
            dest_len.trailing_zeros(),
            false,
            eq_low.as_ptr(),
            eq_sizes,
            d_contributions.as_mut_ptr(),
        );
        launch_dim_reducing_continuation_batched_compact(&batch, acc_size, step, &context).unwrap();
        let dest_gpu = download(&context, &d_dest);

        // Slot 2Y + b folds the ancestor pair (4Y + b, 4Y + b + 2).
        let expected: Vec<E4> = (0..dest_len)
            .map(|c| {
                let (y, b) = (c >> 1, c & 1);
                if ancestor == 4 * y + b {
                    one_minus_r
                } else if ancestor == 4 * y + b + 2 {
                    folding_challenge
                } else {
                    E4::ZERO
                }
            })
            .collect();
        assert_e4_slices_eq(
            &dest_gpu[..dest_len],
            &expected,
            &format!("final-evaluation packing, ancestor {ancestor}"),
        );
    }
}
