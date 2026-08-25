use core::fmt::Debug;
use core::mem::{align_of, offset_of, size_of};

use era_cudart::cuda_kernel;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::{CudaResult, CudaResultWrap};
use era_cudart::slice::DeviceSlice;
use era_cudart_sys::{cudaFuncSetAttribute, CudaFuncAttribute};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::{BF, E4};
use gpu_prover_context::ProverContext;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

use super::capacity::{portable_entry, DrTailCapacityDecision, DrTailCapacityRequest};
use super::census::corpus_census;
use super::reference::{
    run_reference, set_consistent_initial_claim, synthetic_two_group_eq, DrTailMutation,
    DrTailReferenceInput, DrTailReferenceOutput, DrTailReferenceSlot, DrTailSlotKind,
};
use super::{
    launch_dr_tail_megakernel_e4, DrTailMegakernelDesc, DrTailMegakernelE4Function, DrTailSlot,
    DR_TAIL_BLOCK_THREADS, DR_TAIL_MAX_FIRST_ROUND_ACC_SIZE, DR_TAIL_MAX_REMAINING_ROUNDS,
    DR_TAIL_MAX_SOURCES,
};
use crate::backward::kernels::{
    get_dim_reducing_layer_claim_point_device_ptr, get_eq_high_constant_device_ptr,
    launch_backward_dual_finalize_from_acc, launch_build_eq_high_and_low_groups_from_point,
    launch_dim_reducing_continuation_batched_compact, make_eq_sizes, pack_cache_u16,
    pack_source_u16, record_active_eq_slot_fold, resolve_active_eq_slot,
    schedule_dim_reducing_batch_challenge_table_prelude, GpuGKRDimensionReducingBatch,
    GpuGKRDimensionReducingSlot, GpuGKRDimensionReducingTables, GpuGKRSourceRecord,
    GKR_DIM_REDUCING_SLOTS, GKR_EQ_GROUP_TABLE_LEN, GKR_EQ_HIGH_SLOTS,
};
use crate::test_utils::make_test_context;
use crate::upstream::{
    commit_field_els, draw_random_field_els, Blake2sTranscript, Field, FieldExtension, PrimeField,
    Seed,
};

const CUDA_KERNEL_ARGUMENT_CEILING_BYTES: usize = 32_764;
const TRACE_EQ_GROUP_STRIDE: usize = 2 * GKR_EQ_GROUP_TABLE_LEN;
const TRACE_EQ_ROW_STRIDE: usize = DR_TAIL_MAX_FIRST_ROUND_ACC_SIZE;
const TRACE_ENTRY_SOURCE_STRIDE: usize =
    DR_TAIL_MAX_SOURCES * 16 * DR_TAIL_MAX_FIRST_ROUND_ACC_SIZE;
const TRACE_SOURCE_STRIDE: usize = DR_TAIL_MAX_SOURCES * 4 * DR_TAIL_MAX_FIRST_ROUND_ACC_SIZE;
const TRACE_TRANSCRIPT_STRIDE: usize = 3;
const TRACE_METADATA_STRIDE: usize = 8;
const GUARD_ELEMENTS: usize = 2;

const _: () = {
    assert!(TRACE_SOURCE_STRIDE == 5_120);
    assert!(TRACE_ENTRY_SOURCE_STRIDE == 20_480);
    assert!(size_of::<DrTailTraceDesc>() == 64);
    assert!(align_of::<DrTailTraceDesc>() == 8);
    assert!(offset_of!(DrTailTraceDesc, eq_groups) == 0);
    assert!(offset_of!(DrTailTraceDesc, eq_rows) == 8);
    assert!(offset_of!(DrTailTraceDesc, entry_levels) == 16);
    assert!(offset_of!(DrTailTraceDesc, source_levels) == 24);
    assert!(offset_of!(DrTailTraceDesc, transcript) == 32);
    assert!(offset_of!(DrTailTraceDesc, final_cells) == 40);
    assert!(offset_of!(DrTailTraceDesc, seeds) == 48);
    assert!(offset_of!(DrTailTraceDesc, metadata) == 56);
    assert!(
        size_of::<DrTailMegakernelDesc>() + size_of::<DrTailTraceDesc>()
            <= CUDA_KERNEL_ARGUMENT_CEILING_BYTES
    );
};

#[repr(C)]
#[derive(Clone, Copy)]
struct DrTailTraceDesc {
    eq_groups: *mut E4,
    eq_rows: *mut E4,
    entry_levels: *mut E4,
    source_levels: *mut E4,
    transcript: *mut E4,
    final_cells: *mut E4,
    seeds: *mut u32,
    metadata: *mut u32,
}

cuda_kernel!(
    DrTailMegakernelTraceE4,
    ab_gkr_dr_tail_megakernel_trace_e4_kernel(
        desc: DrTailMegakernelDesc,
        trace: DrTailTraceDesc,
    )
);

fn launch_trace(
    desc: DrTailMegakernelDesc,
    trace: DrTailTraceDesc,
    capacity: &DrTailCapacityDecision,
    context: &ProverContext,
) -> CudaResult<()> {
    let folding_steps = desc.folding_steps as usize;
    let entry_round = desc.entry_round as usize;
    let source_count = desc.source_count as usize;
    assert_eq!(entry_round, capacity.entry_round);
    assert_eq!(folding_steps, entry_round + capacity.remaining_rounds);
    assert!((1..=DR_TAIL_MAX_REMAINING_ROUNDS).contains(&capacity.remaining_rounds));
    assert!((1..=DR_TAIL_MAX_SOURCES).contains(&source_count));
    for source in desc.source_ptrs.iter().take(source_count) {
        assert_eq!(
            *source as usize % 32,
            0,
            "DR-tail packed entry load requires 32-byte aligned canonical source pointers",
        );
    }
    assert_eq!(capacity.eq_suffix_offset, entry_round + 1);
    assert_eq!(capacity.eq_suffix_bits, folding_steps - entry_round - 1);
    assert_eq!(capacity.eq_group_count, capacity.eq_suffix_bits.div_ceil(8));
    assert_eq!(
        capacity.entry_cells_per_source,
        1usize << (capacity.remaining_rounds + 1)
    );
    let first_round_acc_size = capacity.entry_cells_per_source / 4;
    assert!(first_round_acc_size <= DR_TAIL_MAX_FIRST_ROUND_ACC_SIZE);
    assert!(2 * first_round_acc_size <= DR_TAIL_BLOCK_THREADS as usize);
    assert_eq!(
        capacity.state_bytes,
        source_count * capacity.entry_cells_per_source * size_of::<E4>()
    );
    assert_eq!(
        capacity.factored_eq_bytes,
        capacity.eq_group_count * GKR_EQ_GROUP_TABLE_LEN * size_of::<E4>()
    );
    assert_eq!(
        capacity.dynamic_smem_bytes,
        capacity.state_bytes + capacity.factored_eq_bytes
    );
    let dynamic_smem_bytes = capacity.dynamic_smem_bytes;
    let function = DrTailMegakernelTraceE4Function::default();
    unsafe {
        cudaFuncSetAttribute(
            function.as_ptr(),
            CudaFuncAttribute::MaxDynamicSharedMemorySize,
            dynamic_smem_bytes as i32,
        )
    }
    .wrap()?;
    let config = CudaLaunchConfig::builder()
        .grid_dim(1)
        .block_dim(DR_TAIL_BLOCK_THREADS)
        .dynamic_smem_bytes(dynamic_smem_bytes)
        .stream(context.get_exec_stream())
        .build();
    let args = DrTailMegakernelTraceE4Arguments::new(desc, trace);
    function.launch(&config, &args)
}

fn lift(value: u32) -> E4 {
    <E4 as FieldExtension<BF>>::from_base(BF::from_u32_with_reduction(value))
}

fn random_e4(rng: &mut StdRng) -> E4 {
    E4::from_array_of_base(std::array::from_fn(|_| {
        BF::from_u32_with_reduction(rng.random())
    }))
}

fn mul(mut left: E4, right: E4) -> E4 {
    left.mul_assign(&right);
    left
}

fn power(base: E4, exponent: usize) -> E4 {
    (0..exponent).fold(E4::ONE, |value, _| mul(value, base))
}

fn poison(tag: u32) -> E4 {
    E4::from_array_of_base(std::array::from_fn(|limb| {
        BF::from_u32_with_reduction(0xa500_0000u32.wrapping_add(tag).wrapping_add(limb as u32))
    }))
}

struct Guarded<T: Copy + Default + PartialEq + Debug> {
    device: DeviceAllocation<T>,
    payload_len: usize,
    canary: T,
    label: String,
}

impl<T: Copy + Default + PartialEq + Debug> Guarded<T> {
    fn new(context: &ProverContext, payload: &[T], canary: T, label: impl Into<String>) -> Self {
        let mut host = vec![canary; GUARD_ELEMENTS + payload.len() + GUARD_ELEMENTS];
        host[GUARD_ELEMENTS..GUARD_ELEMENTS + payload.len()].copy_from_slice(payload);
        let mut device = context
            .alloc(host.len(), AllocationPlacement::BestFit)
            .unwrap();
        memory_copy_async(&mut device, &host, context.get_exec_stream()).unwrap();
        Self {
            device,
            payload_len: payload.len(),
            canary,
            label: label.into(),
        }
    }

    fn as_ptr(&self) -> *const T {
        unsafe { self.device.as_ptr().add(GUARD_ELEMENTS) }
    }

    fn as_mut_ptr(&mut self) -> *mut T {
        unsafe { self.device.as_mut_ptr().add(GUARD_ELEMENTS) }
    }

    fn read(&self, context: &ProverContext) -> Vec<T> {
        let mut host = vec![T::default(); self.device.len()];
        memory_copy_async(&mut host, &self.device, context.get_exec_stream()).unwrap();
        context.get_exec_stream().synchronize().unwrap();
        assert!(
            host[..GUARD_ELEMENTS]
                .iter()
                .all(|value| *value == self.canary),
            "{} leading canary changed",
            self.label,
        );
        assert!(
            host[GUARD_ELEMENTS + self.payload_len..]
                .iter()
                .all(|value| *value == self.canary),
            "{} trailing canary changed",
            self.label,
        );
        host[GUARD_ELEMENTS..GUARD_ELEMENTS + self.payload_len].to_vec()
    }
}

#[derive(Clone)]
struct Fixture {
    input: DrTailReferenceInput,
    slots: [DrTailSlot; GKR_DIM_REDUCING_SLOTS],
    enabled_mask: u32,
    batch_base: E4,
    alias_source_ptrs: bool,
    alias_tau_challenges: bool,
}

fn make_fixture(
    seed: u64,
    folding_steps: usize,
    enabled_mask: u32,
    source_count: usize,
    raw_lookup: Vec<usize>,
    basis_hot: Option<usize>,
    alias_source_ptrs: bool,
    alias_tau_challenges: bool,
) -> Fixture {
    let entry_round = portable_entry(folding_steps).unwrap();
    let remaining_rounds = folding_steps - entry_round;
    assert!((1..=DR_TAIL_MAX_REMAINING_ROUNDS).contains(&remaining_rounds));
    let enabled: Vec<_> = (0..GKR_DIM_REDUCING_SLOTS)
        .filter(|slot| enabled_mask & (1 << slot) != 0)
        .collect();
    assert_eq!(source_count, 2 * enabled.len());
    let mut rng = StdRng::seed_from_u64(seed);
    let batch_base = random_e4(&mut rng);
    let source_len = 1usize << (remaining_rounds + 4);
    let canonical_sources = (0..source_count)
        .map(|source| {
            (0..source_len)
                .map(|cell| {
                    if let Some(hot) = basis_hot {
                        if hot == source * source_len + cell {
                            E4::ONE
                        } else {
                            E4::ZERO
                        }
                    } else {
                        random_e4(&mut rng)
                    }
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let tau = (0..folding_steps)
        .map(|_| random_e4(&mut rng))
        .collect::<Vec<_>>();
    let entry_challenges = if alias_tau_challenges {
        tau[entry_round - 3..entry_round].try_into().unwrap()
    } else {
        std::array::from_fn(|_| random_e4(&mut rng))
    };

    let mut native_slots = [DrTailSlot::default(); GKR_DIM_REDUCING_SLOTS];
    let mut reference_slots = [None; GKR_DIM_REDUCING_SLOTS];
    for (enabled_index, slot) in enabled.into_iter().enumerate() {
        let sources = [2 * enabled_index, 2 * enabled_index + 1];
        let exponents = [2 * slot, 2 * slot + 1];
        native_slots[slot] = DrTailSlot {
            input_source: sources.map(|source| source as u16),
            batch_exp: exponents.map(|exponent| exponent as u16),
        };
        reference_slots[slot] = Some(DrTailReferenceSlot {
            kind: if slot == 0 || slot == 4 {
                DrTailSlotKind::Pairwise
            } else {
                DrTailSlotKind::Lookup
            },
            source_indices: sources,
            batch_weights: exponents.map(|exponent| power(batch_base, exponent)),
        });
    }

    let mut input = DrTailReferenceInput {
        folding_steps,
        entry_round,
        canonical_sources,
        slots: reference_slots,
        entry_challenges,
        tau,
        seed: Seed(std::array::from_fn(|_| rng.random())),
        initial_claim: E4::ZERO,
        initial_eq_prefactor: lift(17),
        raw_address_canonical_lookup: raw_lookup,
    };
    if alias_source_ptrs {
        assert!(source_count >= 2);
        input.canonical_sources[1] = input.canonical_sources[0].clone();
    }
    set_consistent_initial_claim(&mut input);
    Fixture {
        input,
        slots: native_slots,
        enabled_mask,
        batch_base,
        alias_source_ptrs,
        alias_tau_challenges,
    }
}

fn capacity(input: &DrTailReferenceInput) -> DrTailCapacityDecision {
    let request = DrTailCapacityRequest {
        folding_steps: input.folding_steps,
        entry_round: input.entry_round,
        canonical_sources: input.canonical_sources.len(),
        static_smem_bytes: 8_192,
        device_cap_bytes: usize::MAX,
    };
    let admitted = request.decide().unwrap();
    assert!(matches!(
        DrTailCapacityRequest {
            device_cap_bytes: admitted.total_smem_bytes - 1,
            ..request
        }
        .decide(),
        Err(super::capacity::DrTailCapacityRejection::DeviceCapacityExceeded { .. })
    ));
    assert_eq!(
        DrTailCapacityRequest {
            device_cap_bytes: admitted.total_smem_bytes,
            ..request
        }
        .decide()
        .unwrap(),
        admitted
    );
    admitted
}

fn challenge_image(input: &DrTailReferenceInput) -> Vec<E4> {
    let mut challenges = vec![poison(0x31); input.folding_steps];
    challenges[input.entry_round - 3..input.entry_round].copy_from_slice(&input.entry_challenges);
    challenges
}

fn make_desc(
    fixture: &Fixture,
    source_ptrs: [*const E4; DR_TAIL_MAX_SOURCES],
    final_sources: *mut E4,
    tau: *const E4,
    seed: *mut u32,
    claim: *mut E4,
    eq_prefactor: *mut E4,
    coeffs_out: *mut E4,
    challenges_out: *mut E4,
) -> DrTailMegakernelDesc {
    DrTailMegakernelDesc {
        enabled_mask: fixture.enabled_mask,
        folding_steps: fixture.input.folding_steps as u32,
        entry_round: fixture.input.entry_round as u32,
        source_count: fixture.input.canonical_sources.len() as u32,
        source_ptrs,
        final_sources,
        tau,
        seed,
        claim,
        eq_prefactor,
        coeffs_out,
        challenges_out,
        slots: fixture.slots,
    }
}

#[derive(Debug, PartialEq, Eq)]
struct TraceOutput {
    eq_groups: Vec<E4>,
    eq_rows: Vec<E4>,
    entry_levels: Vec<E4>,
    source_levels: Vec<E4>,
    transcript: Vec<E4>,
    final_cells: Vec<E4>,
    seeds: Vec<u32>,
    metadata: Vec<u32>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ArmKind {
    Production,
    Diagnostic,
    Legacy,
}

#[derive(Debug, PartialEq, Eq)]
struct ArmOutput {
    arm: ArmKind,
    seed: Seed,
    claim: E4,
    eq_prefactor: E4,
    coeffs: Vec<E4>,
    challenges: Vec<E4>,
    final_cells: Vec<E4>,
    epilogue: Vec<E4>,
    trace: Option<TraceOutput>,
}

fn poison_incoming_eq(context: &ProverContext, tag: u32) -> Guarded<E4> {
    let high = (0..GKR_EQ_HIGH_SLOTS)
        .flat_map(|slot| vec![poison(tag + slot as u32); GKR_EQ_GROUP_TABLE_LEN])
        .collect::<Vec<_>>();
    let high_view =
        unsafe { DeviceSlice::from_raw_parts_mut(get_eq_high_constant_device_ptr(), high.len()) };
    memory_copy_async(high_view, &high, context.get_exec_stream()).unwrap();
    Guarded::new(
        context,
        &vec![poison(tag + GKR_EQ_HIGH_SLOTS as u32); GKR_EQ_GROUP_TABLE_LEN],
        poison(tag ^ 0xaaaa),
        "incoming eq-low poison",
    )
}

fn run_epilogue(
    context: &ProverContext,
    canonical_cells: *const E4,
    canonical_count: usize,
    raw_lookup: &[usize],
    final_challenge: E4,
) -> Vec<E4> {
    assert!(raw_lookup.iter().all(|source| *source < canonical_count));
    let mut packed = Guarded::new(
        context,
        &vec![poison(0x61); 4 * raw_lookup.len()],
        poison(0x62),
        "raw epilogue input",
    );
    for (raw, canonical) in raw_lookup.iter().copied().enumerate() {
        let source = unsafe { DeviceSlice::from_raw_parts(canonical_cells.add(4 * canonical), 4) };
        let destination =
            unsafe { DeviceSlice::from_raw_parts_mut(packed.as_mut_ptr().add(4 * raw), 4) };
        memory_copy_async(destination, source, context.get_exec_stream()).unwrap();
    }
    let challenge = Guarded::new(
        context,
        &[final_challenge],
        poison(0x63),
        "epilogue challenge",
    );
    let mut lines = Guarded::new(
        context,
        &vec![poison(0x64); 2 * raw_lookup.len()],
        poison(0x65),
        "epilogue output",
    );
    let packed_view = unsafe { DeviceSlice::from_raw_parts(packed.as_ptr(), 4 * raw_lookup.len()) };
    let challenge_view = unsafe { DeviceSlice::from_raw_parts(challenge.as_ptr(), 1) };
    let lines_view =
        unsafe { DeviceSlice::from_raw_parts_mut(lines.as_mut_ptr(), 2 * raw_lookup.len()) };
    crate::gkr_ops::backward_dim_reducing_lsb_lines(
        packed_view,
        challenge_view,
        lines_view,
        context.get_exec_stream(),
    )
    .unwrap();
    let output = lines.read(context);
    packed.read(context);
    challenge.read(context);
    output
}

fn run_megakernel_arm(
    context: &ProverContext,
    fixture: &Fixture,
    trace_enabled: bool,
    eq_poison_tag: u32,
) -> ArmOutput {
    let input = &fixture.input;
    let remaining = input.folding_steps - input.entry_round;
    let admitted = capacity(input);
    let batch_base = Guarded::new(context, &[fixture.batch_base], poison(0x70), "batch base");
    schedule_dim_reducing_batch_challenge_table_prelude(batch_base.as_ptr(), context).unwrap();
    let incoming_low = poison_incoming_eq(context, eq_poison_tag);

    let source_allocations = input
        .canonical_sources
        .iter()
        .enumerate()
        .map(|(source, values)| {
            Guarded::new(
                context,
                values,
                poison(0x100 + source as u32),
                format!("canonical source {source}"),
            )
        })
        .collect::<Vec<_>>();
    let mut source_ptrs = [core::ptr::null(); DR_TAIL_MAX_SOURCES];
    for (source, allocation) in source_allocations.iter().enumerate() {
        source_ptrs[source] = allocation.as_ptr();
    }
    if fixture.alias_source_ptrs {
        source_ptrs[1] = source_ptrs[0];
    }

    let mut final_cells = Guarded::new(
        context,
        &vec![poison(0x201); 4 * input.canonical_sources.len()],
        poison(0x202),
        "canonical publication",
    );
    let mut seed = Guarded::new(context, &input.seed.0, 0x5a5a_a5a5, "seed");
    let mut claim = Guarded::new(context, &[input.initial_claim], poison(0x203), "claim");
    let mut prefactor = Guarded::new(
        context,
        &[input.initial_eq_prefactor],
        poison(0x204),
        "eq prefactor",
    );
    let mut coeffs = Guarded::new(
        context,
        &vec![poison(0x205); 4 * input.folding_steps],
        poison(0x206),
        "coefficients",
    );

    let mut tau = Guarded::new(context, &input.tau, poison(0x207), "tau");
    let mut challenges = if fixture.alias_tau_challenges {
        None
    } else {
        Some(Guarded::new(
            context,
            &challenge_image(input),
            poison(0x208),
            "challenges",
        ))
    };
    let challenge_ptr = challenges
        .as_mut()
        .map_or_else(|| tau.as_mut_ptr(), Guarded::as_mut_ptr);
    let desc = make_desc(
        fixture,
        source_ptrs,
        final_cells.as_mut_ptr(),
        tau.as_ptr(),
        seed.as_mut_ptr(),
        claim.as_mut_ptr(),
        prefactor.as_mut_ptr(),
        coeffs.as_mut_ptr(),
        challenge_ptr,
    );

    let mut trace_buffers = if trace_enabled {
        let mut eq_groups = Guarded::new(
            context,
            &vec![poison(0x301); remaining * TRACE_EQ_GROUP_STRIDE],
            poison(0x302),
            "trace eq groups",
        );
        let mut eq_rows = Guarded::new(
            context,
            &vec![poison(0x303); remaining * TRACE_EQ_ROW_STRIDE],
            poison(0x304),
            "trace eq rows",
        );
        let mut source_levels = Guarded::new(
            context,
            &vec![poison(0x305); remaining * TRACE_SOURCE_STRIDE],
            poison(0x306),
            "trace source levels",
        );
        let mut entry_levels = Guarded::new(
            context,
            &vec![poison(0x30b); 3 * TRACE_ENTRY_SOURCE_STRIDE],
            poison(0x30c),
            "trace entry source levels",
        );
        let mut transcript = Guarded::new(
            context,
            &vec![poison(0x307); remaining * TRACE_TRANSCRIPT_STRIDE],
            poison(0x308),
            "trace transcript",
        );
        let mut trace_final = Guarded::new(
            context,
            &vec![poison(0x309); 4 * input.canonical_sources.len()],
            poison(0x30a),
            "trace final cells",
        );
        let mut trace_seeds = Guarded::new(
            context,
            &vec![0x1bad_b002; remaining * 8],
            0x1bad_b003,
            "trace seeds",
        );
        let mut metadata = Guarded::new(
            context,
            &vec![0xfeed_0000; remaining * TRACE_METADATA_STRIDE],
            0xfeed_beef,
            "trace metadata",
        );
        let trace_desc = DrTailTraceDesc {
            eq_groups: eq_groups.as_mut_ptr(),
            eq_rows: eq_rows.as_mut_ptr(),
            entry_levels: entry_levels.as_mut_ptr(),
            source_levels: source_levels.as_mut_ptr(),
            transcript: transcript.as_mut_ptr(),
            final_cells: trace_final.as_mut_ptr(),
            seeds: trace_seeds.as_mut_ptr(),
            metadata: metadata.as_mut_ptr(),
        };
        launch_trace(desc, trace_desc, &admitted, context).unwrap();
        Some((
            eq_groups,
            eq_rows,
            entry_levels,
            source_levels,
            transcript,
            trace_final,
            trace_seeds,
            metadata,
        ))
    } else {
        // Production raises the ceiling once, at admission, to the proof
        // maximum; this harness drives the kernel directly, so it raises to
        // the fixture's admitted size here.
        let function = DrTailMegakernelE4Function::default();
        unsafe {
            cudaFuncSetAttribute(
                function.as_ptr(),
                CudaFuncAttribute::MaxDynamicSharedMemorySize,
                admitted.dynamic_smem_bytes as i32,
            )
        }
        .wrap()
        .unwrap();
        launch_dr_tail_megakernel_e4(desc, &admitted, context).unwrap();
        None
    };

    let seed_host = seed.read(context);
    let claim_host = claim.read(context)[0];
    let prefactor_host = prefactor.read(context)[0];
    let coeffs_host = coeffs.read(context);
    let challenges_host = challenges
        .as_ref()
        .map_or_else(|| tau.read(context), |buffer| buffer.read(context));
    let final_host = final_cells.read(context);
    let final_challenge = challenges_host[input.folding_steps - 1];
    let epilogue = run_epilogue(
        context,
        final_cells.as_ptr(),
        input.canonical_sources.len(),
        &input.raw_address_canonical_lookup,
        final_challenge,
    );
    for source in &source_allocations {
        source.read(context);
    }
    batch_base.read(context);
    incoming_low.read(context);
    tau.read(context);

    let trace = trace_buffers.take().map(
        |(
            eq_groups,
            eq_rows,
            entry_levels,
            source_levels,
            transcript,
            trace_final,
            seeds,
            metadata,
        )| {
            TraceOutput {
                eq_groups: eq_groups.read(context),
                eq_rows: eq_rows.read(context),
                entry_levels: entry_levels.read(context),
                source_levels: source_levels.read(context),
                transcript: transcript.read(context),
                final_cells: trace_final.read(context),
                seeds: seeds.read(context),
                metadata: metadata.read(context),
            }
        },
    );
    ArmOutput {
        arm: if trace_enabled {
            ArmKind::Diagnostic
        } else {
            ArmKind::Production
        },
        seed: Seed(seed_host.try_into().unwrap()),
        claim: claim_host,
        eq_prefactor: prefactor_host,
        coeffs: coeffs_host,
        challenges: challenges_host,
        final_cells: final_host,
        epilogue,
        trace,
    }
}

fn device_copy<T: Copy>(
    context: &ProverContext,
    destination: *mut T,
    source: *const T,
    len: usize,
) {
    let destination = unsafe { DeviceSlice::from_raw_parts_mut(destination, len) };
    let source = unsafe { DeviceSlice::from_raw_parts(source, len) };
    memory_copy_async(destination, source, context.get_exec_stream()).unwrap();
}

fn install_claim_point(context: &ProverContext, challenges: *const E4, len: usize) {
    device_copy(
        context,
        get_dim_reducing_layer_claim_point_device_ptr(),
        challenges,
        len,
    );
}

fn legacy_batch(
    fixture: &Fixture,
    source: *const E4,
    source_stride: usize,
    destination: *mut E4,
    destination_stride: usize,
    eq_low: *const E4,
    eq_sizes: crate::backward::GkrEqSizes,
    contributions: *mut E4,
) -> GpuGKRDimensionReducingBatch<E4> {
    assert!(source_stride.is_power_of_two());
    assert!(destination_stride.is_power_of_two());
    let mut batch = GpuGKRDimensionReducingBatch::<E4> {
        enabled_mask: fixture.enabled_mask,
        eq_low,
        eq_sizes,
        contributions,
        tables: GpuGKRDimensionReducingTables::default(),
        ..Default::default()
    };
    batch.tables.bases[0] = source.cast();
    batch.tables.bases[1] = destination.cast();
    batch.tables.log2_stride[0] = source_stride.trailing_zeros();
    batch.tables.log2_stride[1] = destination_stride.trailing_zeros();
    let mut seen = [false; DR_TAIL_MAX_SOURCES];
    for slot_index in 0..GKR_DIM_REDUCING_SLOTS {
        if fixture.enabled_mask & (1 << slot_index) == 0 {
            continue;
        }
        let slot = fixture.slots[slot_index];
        let mut encoded = GpuGKRDimensionReducingSlot::default();
        for input_index in 0..2 {
            let source_index = slot.input_source[input_index] as usize;
            encoded.io[input_index] = GpuGKRSourceRecord::new(
                pack_source_u16(!seen[source_index], 0, source_index as u16),
                pack_cache_u16(1, source_index as u16),
            );
            seen[source_index] = true;
        }
        encoded.batch_exp = slot.batch_exp;
        batch.slots[slot_index] = encoded;
    }
    assert!(
        seen[..fixture.input.canonical_sources.len()]
            .iter()
            .all(|seen| *seen),
        "every canonical source must be folded by the legacy arm"
    );
    batch
}

#[derive(Debug, PartialEq, Eq)]
struct LegacyOutput {
    public: ArmOutput,
    entry_source_levels: Vec<Vec<E4>>,
    source_levels: Vec<Vec<E4>>,
    round_states: Vec<(Seed, E4, E4)>,
}

fn run_legacy_arm(context: &ProverContext, fixture: &Fixture) -> LegacyOutput {
    let input = &fixture.input;
    let source_count = input.canonical_sources.len();
    let batch_base = Guarded::new(
        context,
        &[fixture.batch_base],
        poison(0x401),
        "legacy batch base",
    );
    schedule_dim_reducing_batch_challenge_table_prelude(batch_base.as_ptr(), context).unwrap();

    let tau = Guarded::new(context, &input.tau, poison(0x402), "legacy tau");
    let mut challenges = Guarded::new(
        context,
        &challenge_image(input),
        poison(0x403),
        "legacy challenges",
    );
    install_claim_point(context, challenges.as_ptr(), input.folding_steps);
    let mut seed = Guarded::new(context, &input.seed.0, 0x0ddc_0ffe, "legacy seed");
    let mut claim = Guarded::new(
        context,
        &[input.initial_claim],
        poison(0x404),
        "legacy claim",
    );
    let mut prefactor = Guarded::new(
        context,
        &[input.initial_eq_prefactor],
        poison(0x405),
        "legacy eq prefactor",
    );
    let mut coeffs = Guarded::new(
        context,
        &vec![poison(0x406); 4 * input.folding_steps],
        poison(0x407),
        "legacy coefficients",
    );
    let mut eq_low = Guarded::new(
        context,
        &vec![poison(0x408); GKR_EQ_GROUP_TABLE_LEN],
        poison(0x409),
        "legacy eq low",
    );

    let initial_flat = input
        .canonical_sources
        .iter()
        .flatten()
        .copied()
        .collect::<Vec<_>>();
    let mut levels = vec![Guarded::new(
        context,
        &initial_flat,
        poison(0x410),
        "legacy pre-entry source level",
    )];
    let mut level_cells = input.canonical_sources[0].len();
    let mut tail_level_indices = Vec::new();
    let mut contributions = Vec::new();
    let mut seed_snapshots = Vec::new();
    let mut state_snapshots = Vec::new();
    let mut eq_sizes = make_eq_sizes(0);

    for step in input.entry_round - 2..input.folding_steps {
        let destination_cells = level_cells / 2;
        let mut destination = Guarded::new(
            context,
            &vec![poison(0x420 + step as u32); source_count * destination_cells],
            poison(0x430 + step as u32),
            format!("legacy source level {step}"),
        );
        let acc_size = destination_cells / 4;
        let mut round_contributions = Guarded::new(
            context,
            &vec![poison(0x440 + step as u32); 2 * acc_size],
            poison(0x450 + step as u32),
            format!("legacy contributions {step}"),
        );

        if step <= input.entry_round {
            let challenge_count = input.folding_steps - step - 1;
            if challenge_count == 0 {
                let low_identity =
                    unsafe { DeviceSlice::from_raw_parts_mut(eq_low.as_mut_ptr(), 1) };
                memory_copy_async(low_identity, &[E4::ONE], context.get_exec_stream()).unwrap();
            }
            launch_build_eq_high_and_low_groups_from_point(
                tau.as_ptr(),
                step + 1,
                challenge_count,
                get_eq_high_constant_device_ptr(),
                eq_low.as_mut_ptr(),
                context,
            )
            .unwrap();
            eq_sizes = make_eq_sizes(challenge_count);
        }
        let batch = legacy_batch(
            fixture,
            levels.last().unwrap().as_ptr(),
            level_cells,
            destination.as_mut_ptr(),
            destination_cells,
            eq_low.as_ptr(),
            eq_sizes,
            round_contributions.as_mut_ptr(),
        );
        launch_dim_reducing_continuation_batched_compact(&batch, acc_size, step, context).unwrap();
        levels.push(destination);
        level_cells = destination_cells;

        if step >= input.entry_round {
            tail_level_indices.push(levels.len() - 1);
            let final_round = step + 1 == input.folding_steps;
            let (active_eq, active_size) = if final_round {
                (eq_low.as_mut_ptr(), 0)
            } else {
                resolve_active_eq_slot(&eq_sizes, eq_low.as_mut_ptr())
            };
            launch_backward_dual_finalize_from_acc(
                round_contributions.as_ptr(),
                acc_size,
                unsafe { tau.as_ptr().add(step) },
                seed.as_mut_ptr(),
                claim.as_mut_ptr(),
                prefactor.as_mut_ptr(),
                unsafe { coeffs.as_mut_ptr().add(4 * step) },
                unsafe { challenges.as_mut_ptr().add(step) },
                active_eq,
                active_size,
                context,
            )
            .unwrap();
            if !final_round {
                record_active_eq_slot_fold(&mut eq_sizes);
                device_copy(
                    context,
                    unsafe { get_dim_reducing_layer_claim_point_device_ptr().add(step) },
                    unsafe { challenges.as_ptr().add(step) },
                    1,
                );
            }

            let mut seed_snapshot = Guarded::new(
                context,
                &[0xdead_beef; 8],
                0xdead_babe,
                format!("legacy seed snapshot {step}"),
            );
            device_copy(context, seed_snapshot.as_mut_ptr(), seed.as_ptr(), 8);
            seed_snapshots.push(seed_snapshot);
            let mut state_snapshot = Guarded::new(
                context,
                &[poison(0x460), poison(0x461)],
                poison(0x462),
                format!("legacy scalar snapshot {step}"),
            );
            device_copy(context, state_snapshot.as_mut_ptr(), claim.as_ptr(), 1);
            device_copy(
                context,
                unsafe { state_snapshot.as_mut_ptr().add(1) },
                prefactor.as_ptr(),
                1,
            );
            state_snapshots.push(state_snapshot);
        }
        contributions.push(round_contributions);
    }

    assert_eq!(level_cells, 4);
    let final_level = levels.last().unwrap();
    let final_challenge_host = {
        let all = challenges.read(context);
        all[input.folding_steps - 1]
    };
    let epilogue = run_epilogue(
        context,
        final_level.as_ptr(),
        source_count,
        &input.raw_address_canonical_lookup,
        final_challenge_host,
    );
    let source_levels = tail_level_indices
        .into_iter()
        .map(|index| levels[index].read(context))
        .collect::<Vec<_>>();
    let entry_source_levels = levels[1..=3]
        .iter()
        .map(|level| level.read(context))
        .collect::<Vec<_>>();
    let round_states = seed_snapshots
        .iter()
        .zip(&state_snapshots)
        .map(|(seed_snapshot, state_snapshot)| {
            let seed = Seed(seed_snapshot.read(context).try_into().unwrap());
            let state = state_snapshot.read(context);
            (seed, state[0], state[1])
        })
        .collect();
    let public = ArmOutput {
        arm: ArmKind::Legacy,
        seed: Seed(seed.read(context).try_into().unwrap()),
        claim: claim.read(context)[0],
        eq_prefactor: prefactor.read(context)[0],
        coeffs: coeffs.read(context),
        challenges: challenges.read(context),
        final_cells: final_level.read(context),
        epilogue,
        trace: None,
    };
    for level in &levels {
        level.read(context);
    }
    for contribution in &contributions {
        contribution.read(context);
    }
    batch_base.read(context);
    tau.read(context);
    eq_low.read(context);

    LegacyOutput {
        public,
        entry_source_levels,
        source_levels,
        round_states,
    }
}

fn expected_round_seeds(
    input: &DrTailReferenceInput,
    expected: &DrTailReferenceOutput,
) -> Vec<Seed> {
    let mut seed = input.seed;
    expected
        .rounds
        .iter()
        .map(|round| {
            commit_field_els::<BF, E4, Blake2sTranscript>(&mut seed, &round.coefficients);
            let challenge = draw_random_field_els::<BF, E4, Blake2sTranscript>(&mut seed, 1)[0];
            assert_eq!(challenge, round.challenge);
            seed
        })
        .collect()
}

fn assert_public_matches(
    label: &str,
    input: &DrTailReferenceInput,
    actual: &ArmOutput,
    expected: &DrTailReferenceOutput,
) {
    assert_eq!(actual.seed, expected.seed, "{label}: final seed");
    assert_eq!(
        actual.claim,
        expected.rounds.last().unwrap().claim,
        "{label}: final claim"
    );
    assert_eq!(
        actual.eq_prefactor,
        expected.rounds.last().unwrap().eq_prefactor,
        "{label}: final eq prefactor"
    );
    for (round_index, round) in expected.rounds.iter().enumerate() {
        let absolute = input.entry_round + round_index;
        assert_eq!(
            &actual.coeffs[4 * absolute..4 * absolute + 4],
            &round.coefficients,
            "{label}: coefficients at round {absolute}"
        );
        assert_eq!(
            actual.challenges[absolute], round.challenge,
            "{label}: challenge at round {absolute}"
        );
    }
    let expected_final = expected
        .final_canonical_cells
        .iter()
        .flatten()
        .copied()
        .collect::<Vec<_>>();
    assert_eq!(
        actual.final_cells, expected_final,
        "{label}: four-cell publication"
    );
    let expected_epilogue = expected
        .epilogue_raw_cells
        .iter()
        .flatten()
        .copied()
        .collect::<Vec<_>>();
    assert_eq!(
        actual.epilogue, expected_epilogue,
        "{label}: two-cell epilogue"
    );
}

fn assert_trace_matches(fixture: &Fixture, trace: &TraceOutput, expected: &DrTailReferenceOutput) {
    let input = &fixture.input;
    let remaining = input.folding_steps - input.entry_round;
    let source_count = input.canonical_sources.len();
    let source_stride = 1usize << (remaining + 1);
    let admitted = capacity(input);
    let expected_seeds = expected_round_seeds(input, expected);
    assert_eq!(
        trace.final_cells,
        expected
            .final_canonical_cells
            .iter()
            .flatten()
            .copied()
            .collect::<Vec<_>>()
    );

    let first_level_cells = 4 * source_stride;
    for (level, expected_sources) in expected.entry_source_levels.iter().enumerate() {
        let level_cells = first_level_cells >> level;
        for (source, expected_source) in expected_sources.iter().enumerate() {
            assert_eq!(expected_source.len(), level_cells);
            let start = level * TRACE_ENTRY_SOURCE_STRIDE + source * first_level_cells;
            assert_eq!(
                &trace.entry_levels[start..start + level_cells],
                expected_source,
                "entry fold {level}: source {source}"
            );
        }
    }

    for snapshot in 0..remaining {
        let eq = &expected.rounds[snapshot].eq_before;
        let metadata = &trace.metadata
            [snapshot * TRACE_METADATA_STRIDE..(snapshot + 1) * TRACE_METADATA_STRIDE];
        assert_eq!(&metadata[..3], &eq.sizes);
        assert_eq!(metadata[3] as usize, eq.per_row_values.len());
        assert_eq!(metadata[4] as usize, source_stride >> snapshot);
        assert_eq!(metadata[5] as usize, eq.group_tables.len());
        assert_eq!(metadata[6] as usize, source_stride);
        assert_eq!(metadata[7] as usize, source_count * source_stride);
        assert!(
            metadata[7] as usize + metadata[5] as usize * GKR_EQ_GROUP_TABLE_LEN
                <= admitted.dynamic_smem_bytes / size_of::<E4>(),
            "snapshot {snapshot}: recorder shared indices exceed admitted dynamic memory"
        );
        let rows = &trace.eq_rows[snapshot * TRACE_EQ_ROW_STRIDE
            ..snapshot * TRACE_EQ_ROW_STRIDE + eq.per_row_values.len()];
        assert_eq!(
            rows, eq.per_row_values,
            "snapshot {snapshot}: represented Eq rows"
        );
        for (group, expected_group) in eq.group_tables.iter().enumerate() {
            let start = snapshot * TRACE_EQ_GROUP_STRIDE + group * GKR_EQ_GROUP_TABLE_LEN;
            assert_eq!(
                &trace.eq_groups[start..start + expected_group.len()],
                expected_group,
                "snapshot {snapshot}: Eq group {group}"
            );
        }

        let expected_sources = if snapshot == 0 {
            expected.entry_source_levels.last().unwrap()
        } else {
            &expected.rounds[snapshot - 1].source_level_after
        };
        let current_cells = source_stride >> snapshot;
        for (source, expected_source) in expected_sources.iter().enumerate() {
            assert_eq!(expected_source.len(), current_cells);
            let start = snapshot * TRACE_SOURCE_STRIDE + source * source_stride;
            assert_eq!(
                &trace.source_levels[start..start + current_cells],
                expected_source,
                "snapshot {snapshot}: source {source}"
            );
        }

        let round = &expected.rounds[snapshot];
        let transcript = &trace.transcript
            [snapshot * TRACE_TRANSCRIPT_STRIDE..(snapshot + 1) * TRACE_TRANSCRIPT_STRIDE];
        assert_eq!(
            transcript,
            &[round.challenge, round.claim, round.eq_prefactor]
        );
        assert_eq!(
            &trace.seeds[snapshot * 8..(snapshot + 1) * 8],
            &expected_seeds[snapshot].0
        );
    }
}

fn assert_case(context: &ProverContext, fixture: &Fixture, label: &str) -> ArmOutput {
    let expected = run_reference(&fixture.input, DrTailMutation::None).unwrap();
    let production = run_megakernel_arm(context, fixture, false, 0x501);
    let diagnostic = run_megakernel_arm(context, fixture, true, 0x502);
    let legacy = run_legacy_arm(context, fixture);
    assert!(
        production.trace.is_none(),
        "{label}: production arm produced trace output"
    );
    assert!(
        diagnostic.trace.is_some(),
        "{label}: diagnostic arm produced no trace output"
    );
    assert_public_matches(
        &format!("{label} production"),
        &fixture.input,
        &production,
        &expected,
    );
    assert_public_matches(
        &format!("{label} diagnostic"),
        &fixture.input,
        &diagnostic,
        &expected,
    );
    assert_public_matches(
        &format!("{label} legacy"),
        &fixture.input,
        &legacy.public,
        &expected,
    );
    assert_eq!(
        production.seed, diagnostic.seed,
        "{label}: incoming Eq poison changed seed"
    );
    assert_eq!(
        production.final_cells, diagnostic.final_cells,
        "{label}: incoming Eq poison changed publication"
    );
    assert_trace_matches(fixture, diagnostic.trace.as_ref().unwrap(), &expected);
    let expected_seeds = expected_round_seeds(&fixture.input, &expected);
    assert_eq!(legacy.round_states.len(), expected.rounds.len());
    for (level, expected_sources) in expected.entry_source_levels.iter().enumerate() {
        assert_eq!(
            legacy.entry_source_levels[level],
            expected_sources
                .iter()
                .flatten()
                .copied()
                .collect::<Vec<_>>(),
            "{label}: legacy entry source level {level}"
        );
    }
    for (round, ((seed, claim, prefactor), expected_seed)) in
        legacy.round_states.iter().zip(&expected_seeds).enumerate()
    {
        assert_eq!(seed, expected_seed, "{label}: legacy seed round {round}");
        assert_eq!(
            claim, &expected.rounds[round].claim,
            "{label}: legacy claim round {round}"
        );
        assert_eq!(
            prefactor, &expected.rounds[round].eq_prefactor,
            "{label}: legacy prefactor round {round}"
        );
        let expected_level = if round == 0 {
            expected.entry_source_levels.last().unwrap()
        } else {
            &expected.rounds[round - 1].source_level_after
        };
        assert_eq!(
            legacy.source_levels[round],
            expected_level.iter().flatten().copied().collect::<Vec<_>>(),
            "{label}: legacy source level round {round}"
        );
    }
    production
}

fn mask_shape(index: usize) -> (u32, usize) {
    [(0x01, 2), (0x0d, 6), (0x0f, 8), (0x1f, 10)][index % 4]
}

#[test]
fn dr_tail_gpu_random_differential() {
    let context = make_test_context(256, 64);
    let remaining_rounds = [1, 2, 3, 4, 6, 8];
    for case in 0..32 {
        let remaining = remaining_rounds[case % remaining_rounds.len()];
        let (mask, sources) = mask_shape(case);
        let fixture = make_fixture(
            0xd7a1_0000 + case as u64,
            15 + remaining,
            mask,
            sources,
            (0..sources).collect(),
            None,
            false,
            false,
        );
        assert_case(&context, &fixture, &format!("random case {case}"));
    }
}

#[test]
fn dr_tail_gpu_boundaries_and_masks() {
    let context = make_test_context(256, 64);
    for (case, entry) in [3, 6, 9, 12, 15].into_iter().enumerate() {
        let (mask, sources) = mask_shape(case);
        let fixture = make_fixture(
            0xb0a0_0000 + entry as u64,
            entry + 1,
            mask,
            sources,
            (0..sources).collect(),
            None,
            false,
            false,
        );
        assert_eq!(fixture.input.entry_round, entry);
        assert_case(&context, &fixture, &format!("portable entry {entry}"));
    }
    for (round_index, remaining) in [1, 2, 3, 4, 6, 8].into_iter().enumerate() {
        for shape in 0..4 {
            let (mask, sources) = mask_shape(shape);
            let fixture = make_fixture(
                0xb0b0_0000 + (round_index * 4 + shape) as u64,
                15 + remaining,
                mask,
                sources,
                (0..sources).collect(),
                None,
                false,
                false,
            );
            let admitted = capacity(&fixture.input);
            assert_eq!(
                (admitted.entry_cells_per_source >> (remaining - 1)) / 4,
                1,
                "final-round accumulator must contain one row"
            );
            assert_case(
                &context,
                &fixture,
                &format!("remaining {remaining} mask {mask:#x}"),
            );
        }
    }
    for hot in 0..8 {
        let fixture = make_fixture(
            0xb0c0_0000 + hot as u64,
            16,
            0x01,
            2,
            vec![0, 1],
            Some(hot),
            false,
            false,
        );
        assert_case(&context, &fixture, &format!("basis vector {hot}"));
    }
}

#[test]
fn dr_tail_gpu_eq_rebuild_and_alias() {
    let context = make_test_context(256, 64);
    let fixture = make_fixture(
        0xe911_a115,
        23,
        0x1f,
        10,
        (0..10).collect(),
        None,
        true,
        true,
    );
    let baseline = assert_case(&context, &fixture, "max-mask alias");

    let mut changed_tau = fixture.clone();
    changed_tau.input.tau[changed_tau.input.entry_round + 1].add_assign(&E4::ONE);
    let changed_tau_output = run_megakernel_arm(&context, &changed_tau, false, 0x511);
    let changed_tau_expected = run_reference(&changed_tau.input, DrTailMutation::None).unwrap();
    assert_public_matches(
        "tau mutation",
        &changed_tau.input,
        &changed_tau_output,
        &changed_tau_expected,
    );
    assert_ne!(baseline, changed_tau_output, "tau mutation was vacuous");

    let mut changed_prefactor = fixture.clone();
    changed_prefactor
        .input
        .initial_eq_prefactor
        .add_assign(&E4::ONE);
    let changed_prefactor_output = run_megakernel_arm(&context, &changed_prefactor, false, 0x512);
    let changed_prefactor_expected =
        run_reference(&changed_prefactor.input, DrTailMutation::None).unwrap();
    assert_public_matches(
        "eq-prefactor mutation",
        &changed_prefactor.input,
        &changed_prefactor_output,
        &changed_prefactor_expected,
    );
    assert_ne!(
        baseline, changed_prefactor_output,
        "eq-prefactor mutation was vacuous"
    );

    // The admitted megakernel has at most seven rebuilt Eq bits (one group).
    // Exercise both incoming high slabs plus low via poison above, and pin the
    // Task-1 two-group drain oracle without launching an inadmissible shape.
    let two_group = synthetic_two_group_eq(&(0..9).map(|i| lift(71 + i)).collect::<Vec<_>>());
    assert_eq!(two_group[0].sizes, [8, 0, 1]);
    assert_eq!(two_group[1].sizes, [8, 0, 0]);
    assert_eq!(two_group[2].sizes, [7, 0, 0]);
}

#[test]
fn dr_tail_gpu_raw_canonical_order_mismatch() {
    let context = make_test_context(256, 64);
    let (layout_name, layer_idx, canonical, raw_lookup) = super::dr_tail_first_order_mismatch();
    assert_ne!(canonical, raw_lookup);
    let row = corpus_census()
        .rows
        .iter()
        .find(|row| row.layout_name == layout_name && row.layer_idx == layer_idx)
        .unwrap();
    let fixture = make_fixture(
        0x0dde_4a11,
        row.folding_steps,
        row.enabled_mask,
        row.order.sorted_canonical.len(),
        raw_lookup,
        None,
        false,
        false,
    );
    let production = assert_case(&context, &fixture, "census ordering mismatch");
    let direct = run_reference(&fixture.input, DrTailMutation::DirectCanonicalEpilogue).unwrap();
    let direct_lines = direct
        .epilogue_raw_cells
        .iter()
        .flatten()
        .copied()
        .collect::<Vec<_>>();
    assert_ne!(production.epilogue, direct_lines);
}
