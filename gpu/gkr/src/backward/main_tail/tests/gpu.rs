#![cfg(not(no_cuda))]

use core::mem::{size_of, size_of_val};
use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::memory::memory_copy_async;
use era_cudart::slice::{CudaSliceMut, DeviceSlice};
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::context::{DeviceAllocation, HostAllocation};
use gpu_core::primitives::field::{BF, E4};
use gpu_core::primitives::static_host::{alloc_static_pinned_box_from_slice, StaticPinnedBox};
use gpu_gkr_compiler::{CoefficientRecipeId, SourceId, WindowFamily};
use gpu_prover_context::ProverContext;

use super::binding::{
    bind_main_tail, launch_main_tail, launch_main_tail_counted,
    schedule_per_round_remainder_counted, MainTailBindError, MainTailDispatchCounters,
    MainTailRuntimeState,
};
use super::reference::{
    main_tail_reference, main_tail_reference_with_mutation, MainTailClaimOutput,
    MainTailReferenceEntry, MainTailReferenceError, MainTailReferenceInput,
    MainTailReferenceMutation, MainTailReferenceOutput,
};
use super::{lower_main_tail_program, MainTailProgram};
use crate::backward::kernels::{
    launch_backward_dual_finalize_from_partials, max_partials_len, record_active_eq_slot_fold,
    warp_partial_count,
};
use crate::backward::main_continuation::{ContinuationPublishedLevel, ContinuationPublishedShape};
use crate::backward::main_layer::execution_plan::MainEqBoundaryWitness;
use crate::backward::vm::production_bind::{
    build_bwd_vm_ext_rounds_after_continuations, schedule_bwd_vm_ext_bank_fill,
};
use crate::backward::vm::seg::bwd_seg_coeff_bank_device_ptr;
use crate::backward::vm::seg_coeff_eval::BWD_SEG_CHALLENGE_SLOTS;
use crate::backward::{
    compile_corpus_layout, get_eq_high_constant_device_ptr, get_main_layer_claim_point_device_ptr,
    make_eq_sizes, GKR_EQ_GROUP_TABLE_LEN,
};
use crate::storage_types::GpuGKRStorage;
use crate::test_utils::make_test_context;
use crate::upstream::{Field, FieldExtension, GKRAddress, PrimeField, VirtualSetupPoly};

fn lift(value: u32) -> E4 {
    <E4 as FieldExtension<BF>>::from_base(BF::from_u32_with_reduction(value))
}

fn neg(mut value: E4) -> E4 {
    value.negate();
    value
}

fn eq_weight(bit: usize, coordinate: E4) -> E4 {
    if bit == 0 {
        let mut weight = E4::ONE;
        weight.sub_assign(&coordinate);
        weight
    } else {
        coordinate
    }
}

fn direct_eq(point: &[E4]) -> Vec<E4> {
    (0..1usize << point.len())
        .map(|row| {
            point
                .iter()
                .enumerate()
                .fold(E4::ONE, |mut weight, (bit, coordinate)| {
                    weight.mul_assign(&eq_weight((row >> bit) & 1, *coordinate));
                    weight
                })
        })
        .collect()
}

fn as_bytes<T: Copy>(values: &[T]) -> &[u8] {
    // SAFETY: the byte view covers exactly the initialized slice extent.
    unsafe { core::slice::from_raw_parts(values.as_ptr().cast::<u8>(), size_of_val(values)) }
}

struct Fixture {
    program: gpu_gkr_compiler::ContinuationLayerProgram,
    tail_program: MainTailProgram,
    source_ids: Vec<SourceId>,
    columns: Vec<E4>,
    coefficient_bank: Vec<E4>,
    generated_challenges: Vec<E4>,
    claim_coordinates: Vec<E4>,
    entry_eq_low: Vec<E4>,
    seed: [u32; 8],
    claim: E4,
    eq_prefactor: E4,
    entry_round: u8,
    entry_depth: u8,
    eq_boundary: MainEqBoundaryWitness,
    tail_rounds: usize,
}

struct FixtureEqState {
    high_sentinels: [E4; 2],
    low: Vec<E4>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ClaimMode {
    Aliased,
    Detached,
}

impl ClaimMode {
    fn reference(self) -> MainTailClaimOutput {
        match self {
            Self::Aliased => MainTailClaimOutput::Aliased,
            Self::Detached => MainTailClaimOutput::Detached,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct DifferentialCase {
    folding_steps: usize,
    entry_round: u8,
    claim_mode: ClaimMode,
    salt: u32,
    ruled: bool,
}

fn differential_cases() -> Vec<DifferentialCase> {
    let geometries = [
        (7, 6, false),
        (8, 6, false),
        (10, 6, false),
        (11, 6, false),
        (12, 6, false),
        (20, 15, true),
        (22, 18, true),
        (23, 18, true),
        (24, 18, true),
    ];
    geometries
        .into_iter()
        .flat_map(|(folding_steps, entry_round, ruled)| {
            [ClaimMode::Aliased, ClaimMode::Detached]
                .into_iter()
                .flat_map(move |claim_mode| {
                    (0..2).map(move |salt| DifferentialCase {
                        folding_steps,
                        entry_round,
                        claim_mode,
                        salt,
                        ruled,
                    })
                })
        })
        .collect()
}

impl Fixture {
    fn deterministic() -> Self {
        let (programs, layers) =
            compile_corpus_layout("blake2_with_extended_control_layout_gkr.json");
        let program = (0..layers)
            .map(|layer| programs.continuation_layer(layer))
            .find(|program| {
                program.coefficients.sources.len() > 1
                    && !program.coefficient_recipes.is_empty()
                    && !program.program.words.is_empty()
            })
            .unwrap()
            .clone();
        let tail_program = lower_main_tail_program(&program).unwrap();
        let source_count = usize::from(tail_program.source_count);
        let tail_rounds = 4usize;
        let entry_round = 6u8;
        let entry_depth = entry_round - 3;
        let folding_steps = usize::from(entry_round) + tail_rounds;
        let stride = 1usize << (tail_rounds + 3);
        let columns = (0..source_count * stride)
            .map(|index| {
                let source = index / stride;
                let element = index % stride;
                lift(17 + source as u32 * 65_537 + element as u32 * 257)
            })
            .collect();
        let mut coefficient_bank = (0..usize::from(tail_program.coefficient_count))
            .map(|index| lift(101 + 19 * index as u32))
            .collect::<Vec<_>>();
        coefficient_bank[CoefficientRecipeId::ONE.0 as usize] = E4::ONE;
        coefficient_bank[CoefficientRecipeId::NEG_ONE.0 as usize] = neg(E4::ONE);
        let claim_coordinates = (0..folding_steps)
            .map(|index| lift(307 + 23 * index as u32))
            .collect::<Vec<_>>();
        let generated_challenges = (0..folding_steps)
            .map(|index| lift(1_307 + 29 * index as u32))
            .collect::<Vec<_>>();
        let semantic_suffix_offset = entry_round + 1;
        let entry_eq_low =
            direct_eq(&claim_coordinates[usize::from(semantic_suffix_offset)..folding_steps]);
        Self {
            program,
            tail_program,
            source_ids: (0..source_count)
                .map(|source| SourceId(source as u32))
                .collect(),
            columns,
            coefficient_bank,
            generated_challenges,
            claim_coordinates,
            entry_eq_low,
            seed: [
                0x1020_3040,
                0x5060_7080,
                0x90a0_b0c0,
                0xd0e0_f001,
                0x1234_5678,
                0x9abc_def0,
                0x0bad_cafe,
                0xfeed_beef,
            ],
            claim: lift(19),
            eq_prefactor: lift(29),
            entry_round,
            entry_depth,
            eq_boundary: MainEqBoundaryWitness {
                consumer_round: entry_round,
                semantic_suffix_offset,
                eq_sizes: make_eq_sizes(tail_rounds - 1),
            },
            tail_rounds,
        }
    }

    fn for_case(
        program: gpu_gkr_compiler::ContinuationLayerProgram,
        case: DifferentialCase,
    ) -> Self {
        let tail_program = lower_main_tail_program(&program).unwrap();
        let source_count = usize::from(tail_program.source_count);
        let tail_rounds = case.folding_steps - usize::from(case.entry_round);
        let entry_depth = case.entry_round - 3;
        let stride = 1usize << (tail_rounds + 3);
        let columns = (0..source_count * stride)
            .map(|index| {
                let source = index / stride;
                let element = index % stride;
                lift(17 + case.salt * 1_000_003 + source as u32 * 65_537 + element as u32 * 257)
            })
            .collect();
        let mut coefficient_bank = (0..usize::from(tail_program.coefficient_count))
            .map(|index| lift(101 + case.salt * 65_539 + 19 * index as u32))
            .collect::<Vec<_>>();
        coefficient_bank[CoefficientRecipeId::ONE.0 as usize] = E4::ONE;
        coefficient_bank[CoefficientRecipeId::NEG_ONE.0 as usize] = neg(E4::ONE);
        let claim_coordinates = (0..case.folding_steps)
            .map(|index| lift(307 + case.salt * 4_099 + 23 * index as u32))
            .collect::<Vec<_>>();
        let generated_challenges = (0..case.folding_steps)
            .map(|index| lift(1_307 + case.salt * 8_191 + 29 * index as u32))
            .collect::<Vec<_>>();
        let semantic_suffix_offset = case.entry_round + 1;
        let entry_eq_low =
            direct_eq(&claim_coordinates[usize::from(semantic_suffix_offset)..case.folding_steps]);
        Self {
            program,
            tail_program,
            source_ids: (0..source_count)
                .map(|source| SourceId(source as u32))
                .collect(),
            columns,
            coefficient_bank,
            generated_challenges,
            claim_coordinates,
            entry_eq_low,
            seed: [
                0x1020_3040 ^ case.salt,
                0x5060_7080,
                0x90a0_b0c0,
                0xd0e0_f001,
                0x1234_5678,
                0x9abc_def0,
                0x0bad_cafe,
                0xfeed_beef,
            ],
            claim: lift(19 + case.salt),
            eq_prefactor: lift(29 + case.salt),
            entry_round: case.entry_round,
            entry_depth,
            eq_boundary: MainEqBoundaryWitness {
                consumer_round: case.entry_round,
                semantic_suffix_offset,
                eq_sizes: make_eq_sizes(tail_rounds - 1),
            },
            tail_rounds,
        }
    }

    fn reference_input(&self) -> MainTailReferenceInput<'_> {
        self.reference_input_for(MainTailClaimOutput::Detached)
    }

    fn reference_input_for(&self, claim_output: MainTailClaimOutput) -> MainTailReferenceInput<'_> {
        MainTailReferenceInput {
            program: &self.program,
            tail_program: &self.tail_program,
            coefficient_bank: &self.coefficient_bank,
            entry: MainTailReferenceEntry {
                source_ids: &self.source_ids,
                columns: &self.columns,
                stride: 1usize << (self.tail_rounds + 3),
                depth: self.entry_depth,
            },
            generated_challenges: &self.generated_challenges,
            claim_coordinates: &self.claim_coordinates,
            entry_eq_low: &self.entry_eq_low,
            seed: self.seed,
            claim: self.claim,
            eq_prefactor: self.eq_prefactor,
            entry_round: self.entry_round,
            eq_boundary: self.eq_boundary,
            claim_output,
        }
    }

    fn aliased_claim_and_challenge_coordinates(&self) -> Vec<E4> {
        let mut coordinates = self.claim_coordinates.clone();
        let end = usize::from(self.entry_round);
        let start = end - 3;
        coordinates[start..end].copy_from_slice(&self.generated_challenges[start..end]);
        coordinates
    }

    fn eq_state(&self) -> FixtureEqState {
        FixtureEqState {
            high_sentinels: [E4::ONE; 2],
            low: self.entry_eq_low.clone(),
        }
    }
}

fn max_source_program() -> gpu_gkr_compiler::ContinuationLayerProgram {
    let (programs, layers) = compile_corpus_layout("blake2_with_extended_control_layout_gkr.json");
    let program = (0..layers)
        .map(|layer| programs.continuation_layer(layer))
        .max_by_key(|program| program.coefficients.sources.len())
        .unwrap()
        .clone();
    assert_eq!(program.coefficients.sources.len(), 1_012);
    program
}

#[test]
fn cpu_main_tail_gpu_differential_case_matrix_is_complete() {
    let cases = differential_cases();
    assert_eq!(cases.len(), 36);
    assert!(cases.len() >= 32);
    let mut tail_lengths = cases
        .iter()
        .map(|case| case.folding_steps - usize::from(case.entry_round))
        .collect::<Vec<_>>();
    tail_lengths.sort_unstable();
    tail_lengths.dedup();
    assert_eq!(tail_lengths, [1, 2, 4, 5, 6]);
    let mut first_round_rows = cases
        .iter()
        .map(|case| 1usize << (case.folding_steps - usize::from(case.entry_round) - 1))
        .collect::<Vec<_>>();
    first_round_rows.sort_unstable();
    first_round_rows.dedup();
    assert!(first_round_rows.iter().any(|&rows| rows < 32));
    assert!(first_round_rows.iter().any(|&rows| rows >= 32));
    assert!(cases
        .iter()
        .any(|case| case.claim_mode == ClaimMode::Aliased));
    assert!(cases
        .iter()
        .any(|case| case.claim_mode == ClaimMode::Detached));
    let mut ruled = cases
        .iter()
        .filter(|case| case.ruled)
        .map(|case| (case.folding_steps, case.entry_round))
        .collect::<Vec<_>>();
    ruled.sort_unstable();
    ruled.dedup();
    assert_eq!(ruled, [(20, 15), (22, 18), (23, 18), (24, 18)]);
    assert_eq!(max_source_program().coefficients.sources.len(), 1_012);
}

#[test]
fn cpu_main_tail_smoke_eq_state_covers_strict_three_slot_contract() {
    let fixture = Fixture::deterministic();
    let staged = fixture.eq_state();
    let expected = direct_eq(
        &fixture.claim_coordinates[usize::from(fixture.eq_boundary.semantic_suffix_offset)..],
    );
    assert_eq!(staged.low, expected);
    for (row, &low) in staged.low.iter().enumerate() {
        let mut actual = staged.high_sentinels[0];
        actual.mul_assign(&staged.high_sentinels[1]);
        actual.mul_assign(&low);
        assert_eq!(actual, expected[row], "row {row}");
    }
    for slot in 0..staged.high_sentinels.len() {
        let mut mutated = staged.high_sentinels;
        mutated[slot] = E4::ZERO;
        assert!(
            staged.low.iter().zip(&expected).any(|(&low, &expected)| {
                let mut actual = mutated[0];
                actual.mul_assign(&mutated[1]);
                actual.mul_assign(&low);
                actual != expected
            }),
            "zeroing high sentinel {slot} must be observable",
        );
    }
}

fn upload<T: Copy>(
    context: &ProverContext,
    host: &[T],
) -> (DeviceAllocation<T>, StaticPinnedBox<T>) {
    let staging = alloc_static_pinned_box_from_slice(host).unwrap();
    let mut device = context
        .alloc(host.len().max(1), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(
        &mut device[..host.len()],
        &staging[..],
        context.get_exec_stream(),
    )
    .unwrap();
    (device, staging)
}

fn write_coefficient_bank(context: &ProverContext, coefficients: &[E4]) -> StaticPinnedBox<E4> {
    let staging = alloc_static_pinned_box_from_slice(coefficients).unwrap();
    // SAFETY: the fixture copies only its validated live coefficient prefix.
    let destination = unsafe {
        DeviceSlice::from_raw_parts_mut(bwd_seg_coeff_bank_device_ptr(), coefficients.len())
    };
    memory_copy_async(destination, &staging[..], context.get_exec_stream()).unwrap();
    staging
}

fn write_eq_high_sentinels(
    context: &ProverContext,
    sentinels: &[E4; 2],
) -> [StaticPinnedBox<E4>; 2] {
    let high = get_eq_high_constant_device_ptr();
    std::array::from_fn(|slot| {
        let staging = alloc_static_pinned_box_from_slice(&sentinels[slot..=slot]).unwrap();
        // SAFETY: each strict high slot owns `GKR_EQ_GROUP_TABLE_LEN` E4 values;
        // this fixture writes only its mandatory identity at offset zero.
        let destination =
            unsafe { DeviceSlice::from_raw_parts_mut(high.add(slot * GKR_EQ_GROUP_TABLE_LEN), 1) };
        memory_copy_async(destination, &staging[..], context.get_exec_stream()).unwrap();
        staging
    })
}

#[derive(Debug, PartialEq, Eq)]
struct Observation {
    final_columns: Vec<E4>,
    coefficients: Vec<E4>,
    challenges: Vec<E4>,
    seed: Vec<u32>,
    claim: Vec<E4>,
    eq_prefactor: Vec<E4>,
    eq_low: Vec<E4>,
    eq_high: Vec<E4>,
}

enum FinalColumnsReadback<'a> {
    Contiguous(&'a DeviceSlice<E4>),
    Scattered(&'a [*const E4]),
}

struct ReadbackJob<'a> {
    finished: CudaEvent,
    callbacks: Callbacks<'a>,
    _final_columns: HostAllocation<[E4]>,
    _coefficients: HostAllocation<[E4]>,
    _challenges: HostAllocation<[E4]>,
    _seed: HostAllocation<[u32]>,
    _claim: HostAllocation<[E4]>,
    _eq_prefactor: HostAllocation<[E4]>,
    _eq_low: HostAllocation<[E4]>,
    _eq_high: HostAllocation<[E4]>,
    output: Arc<Mutex<Option<Observation>>>,
}

impl ReadbackJob<'_> {
    fn finish(self) -> Observation {
        self.finished.synchronize().unwrap();
        drop(self.callbacks);
        Arc::try_unwrap(self.output)
            .ok()
            .expect("the readback callback releases its result handle")
            .into_inner()
            .unwrap()
            .expect("the completion event follows the readback callback")
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct PathCoverage {
    main_tail_launches: usize,
    per_round_remainder_launches: usize,
    high_eq_folds: usize,
    fold_weight_symbol_writes: usize,
}

#[derive(Debug, PartialEq, Eq)]
struct ArmObservation {
    output: Observation,
    round_boundaries: Vec<(u8, crate::backward::GkrEqSizes)>,
    final_eq_sizes: crate::backward::GkrEqSizes,
    final_semantic_suffix_offset: u8,
    final_stride: usize,
    coverage: PathCoverage,
}

fn write_symbol<T: Copy>(
    context: &ProverContext,
    destination: *mut T,
    values: &[T],
) -> StaticPinnedBox<T> {
    let staging = alloc_static_pinned_box_from_slice(values).unwrap();
    // SAFETY: each caller names a device symbol with at least `values.len()`
    // elements, and keeps the staging allocation alive until stream completion.
    let destination = unsafe { DeviceSlice::from_raw_parts_mut(destination, values.len()) };
    memory_copy_async(destination, &staging[..], context.get_exec_stream()).unwrap();
    staging
}

fn coefficient_top_bits(program: &gpu_gkr_compiler::ContinuationLayerProgram) -> Vec<u32> {
    let count = program
        .coefficient_recipes
        .iter()
        .flat_map(|recipe| &recipe.terms)
        .flat_map(|product| &product.inits_and_teardowns_top_bits)
        .map(|reference| reference.set_index + 1)
        .max()
        .unwrap_or(0);
    (0..count).map(|index| 3 + index as u32).collect()
}

fn family_address(family: WindowFamily, column: usize) -> GKRAddress {
    match family {
        WindowFamily::BaseLayerMemory => GKRAddress::BaseLayerMemory(column),
        WindowFamily::BaseLayerWitness => GKRAddress::BaseLayerWitness(column),
        WindowFamily::Setup => GKRAddress::Setup(column),
        WindowFamily::Scratch => GKRAddress::ScratchSpace(column),
        WindowFamily::LayerOutput { layer, .. } => GKRAddress::InnerLayer {
            layer,
            offset: column,
        },
        WindowFamily::CacheOutput { layer, .. } => GKRAddress::Cached {
            layer,
            offset: column,
        },
        WindowFamily::VirtualSetup { kind } => GKRAddress::VirtualSetup(match kind {
            0 => VirtualSetupPoly::RangeCheck16Bits,
            1 => VirtualSetupPoly::RangeCheckTimestamp,
            2 => VirtualSetupPoly::InitsAndTeardownsLow,
            3 => VirtualSetupPoly::InitsAndTeardownsHigh,
            _ => panic!("unknown virtual setup kind {kind}"),
        }),
    }
}

fn semantic_source_addresses(
    program: &gpu_gkr_compiler::ContinuationLayerProgram,
) -> Vec<GKRAddress> {
    let mut addresses = vec![None; program.coefficients.sources.len()];
    for window in &program.binding.windows {
        for column in &window.columns {
            let source = column.source as usize;
            assert!(
                addresses[source]
                    .replace(family_address(window.family, column.column))
                    .is_none(),
                "semantic source {source} was visited twice",
            );
        }
    }
    addresses
        .into_iter()
        .enumerate()
        .map(|(source, address)| {
            address.unwrap_or_else(|| panic!("semantic source {source} was not visited"))
        })
        .collect()
}

#[allow(clippy::too_many_arguments)]
fn schedule_readback<'a>(
    final_columns: FinalColumnsReadback<'_>,
    coefficients: &DeviceSlice<E4>,
    challenges: &DeviceSlice<E4>,
    seed: &DeviceSlice<u32>,
    claim: &DeviceSlice<E4>,
    eq_prefactor: &DeviceSlice<E4>,
    eq_low: &DeviceSlice<E4>,
    context: &'a ProverContext,
) -> ReadbackJob<'a> {
    let stream = context.get_exec_stream();
    let final_len = match final_columns {
        FinalColumnsReadback::Contiguous(columns) => columns.len(),
        FinalColumnsReadback::Scattered(columns) => 2 * columns.len(),
    };
    let mut final_host = unsafe { context.alloc_host_uninit_slice(final_len) };
    let mut coefficients_host = unsafe { context.alloc_host_uninit_slice(coefficients.len()) };
    let mut challenges_host = unsafe { context.alloc_host_uninit_slice(challenges.len()) };
    let mut seed_host = unsafe { context.alloc_host_uninit_slice(seed.len()) };
    let mut claim_host = unsafe { context.alloc_host_uninit_slice(claim.len()) };
    let mut prefactor_host = unsafe { context.alloc_host_uninit_slice(eq_prefactor.len()) };
    let mut eq_low_host = unsafe { context.alloc_host_uninit_slice(eq_low.len()) };
    let mut eq_high_host = unsafe { context.alloc_host_uninit_slice(2) };
    match final_columns {
        FinalColumnsReadback::Contiguous(columns) => {
            memory_copy_async(&mut final_host, columns, stream).unwrap();
        }
        FinalColumnsReadback::Scattered(columns) => {
            for (source, &pointer) in columns.iter().enumerate() {
                assert!(!pointer.is_null());
                // SAFETY: the per-round repoint contract returns the two live final
                // E4 cells for this semantic address, and its owning launch remains
                // alive through the completion callback.
                let device = unsafe { DeviceSlice::from_raw_parts(pointer, 2) };
                let final_slice = unsafe { final_host.as_mut_slice() };
                memory_copy_async(&mut final_slice[2 * source..2 * source + 2], device, stream)
                    .unwrap();
            }
        }
    }
    memory_copy_async(&mut coefficients_host, coefficients, stream).unwrap();
    memory_copy_async(&mut challenges_host, challenges, stream).unwrap();
    memory_copy_async(&mut seed_host, seed, stream).unwrap();
    memory_copy_async(&mut claim_host, claim, stream).unwrap();
    memory_copy_async(&mut prefactor_host, eq_prefactor, stream).unwrap();
    memory_copy_async(&mut eq_low_host, eq_low, stream).unwrap();
    for slot in 0..2 {
        let source = unsafe {
            DeviceSlice::from_raw_parts(
                get_eq_high_constant_device_ptr().add(slot * GKR_EQ_GROUP_TABLE_LEN),
                1,
            )
        };
        let eq_high_slice = unsafe { eq_high_host.as_mut_slice() };
        memory_copy_async(&mut eq_high_slice[slot..slot + 1], source, stream).unwrap();
    }

    let final_accessor = final_host.get_accessor();
    let coefficients_accessor = coefficients_host.get_accessor();
    let challenges_accessor = challenges_host.get_accessor();
    let seed_accessor = seed_host.get_accessor();
    let claim_accessor = claim_host.get_accessor();
    let prefactor_accessor = prefactor_host.get_accessor();
    let eq_low_accessor = eq_low_host.get_accessor();
    let eq_high_accessor = eq_high_host.get_accessor();
    let output = Arc::new(Mutex::new(None));
    let callback_output = Arc::clone(&output);
    let mut callbacks = Callbacks::new();
    callbacks
        .schedule(
            move || unsafe {
                callback_output.lock().unwrap().replace(Observation {
                    final_columns: final_accessor.get().to_vec(),
                    coefficients: coefficients_accessor.get().to_vec(),
                    challenges: challenges_accessor.get().to_vec(),
                    seed: seed_accessor.get().to_vec(),
                    claim: claim_accessor.get().to_vec(),
                    eq_prefactor: prefactor_accessor.get().to_vec(),
                    eq_low: eq_low_accessor.get().to_vec(),
                    eq_high: eq_high_accessor.get().to_vec(),
                });
            },
            stream,
        )
        .unwrap();
    let finished = CudaEvent::create_with_flags(CudaEventCreateFlags::DISABLE_TIMING).unwrap();
    finished.record(stream).unwrap();
    ReadbackJob {
        finished,
        callbacks,
        _final_columns: final_host,
        _coefficients: coefficients_host,
        _challenges: challenges_host,
        _seed: seed_host,
        _claim: claim_host,
        _eq_prefactor: prefactor_host,
        _eq_low: eq_low_host,
        _eq_high: eq_high_host,
        output,
    }
}

fn make_entry_level(
    context: &ProverContext,
    fixture: &Fixture,
) -> (ContinuationPublishedLevel, StaticPinnedBox<E4>) {
    let (allocation, staging) = upload(context, &fixture.columns);
    let level = ContinuationPublishedLevel::try_new(
        ContinuationPublishedShape {
            depth: fixture.entry_depth,
            columns: fixture.source_ids.len(),
            column_elems: 1usize << (fixture.tail_rounds + 3),
        },
        allocation,
        fixture
            .source_ids
            .iter()
            .copied()
            .map(|source| (source, source.0 as usize)),
    )
    .unwrap();
    (level, staging)
}

fn run_main_tail_arm(
    context: &ProverContext,
    fixture: &Fixture,
    claim_mode: ClaimMode,
) -> ArmObservation {
    let mut round_boundaries = Vec::with_capacity(fixture.tail_rounds);
    let mut boundary_sizes = fixture.eq_boundary.eq_sizes;
    let mut boundary_suffix = fixture.eq_boundary.semantic_suffix_offset;
    for iteration in 0..fixture.tail_rounds {
        round_boundaries.push((boundary_suffix, boundary_sizes));
        if iteration + 1 < fixture.tail_rounds {
            record_active_eq_slot_fold(&mut boundary_sizes);
            boundary_suffix += 1;
        }
    }
    let (entry, _entry_staging) = make_entry_level(context, fixture);
    let _coefficient_staging = write_coefficient_bank(context, &fixture.coefficient_bank);
    let eq_state = fixture.eq_state();
    let _eq_high_staging = write_eq_high_sentinels(context, &eq_state.high_sentinels);
    let claim_coordinate_input = match claim_mode {
        ClaimMode::Aliased => fixture.aliased_claim_and_challenge_coordinates(),
        ClaimMode::Detached => fixture.claim_coordinates.clone(),
    };
    let (mut claim_coordinates, _claim_coordinates_staging) =
        upload(context, &claim_coordinate_input);
    let (mut detached_challenges, _detached_challenges_staging) =
        upload(context, &fixture.generated_challenges);
    let (mut eq_low, _eq_staging) = upload(context, &eq_state.low);
    let (mut seed, _seed_staging) = upload(context, &fixture.seed);
    let (mut claim, _claim_staging) = upload(context, &[fixture.claim]);
    let (mut eq_prefactor, _prefactor_staging) = upload(context, &[fixture.eq_prefactor]);
    let (mut coefficients, _coefficients_staging) = upload(
        context,
        &vec![E4::ZERO; 4 * fixture.claim_coordinates.len()],
    );
    let challenges_out = match claim_mode {
        ClaimMode::Aliased => claim_coordinates.as_mut_ptr(),
        ClaimMode::Detached => detached_challenges.as_mut_ptr(),
    };
    let launch = bind_main_tail(
        fixture.program.layer,
        &fixture.tail_program,
        entry,
        usize::from(fixture.entry_round),
        fixture.claim_coordinates.len(),
        fixture.eq_boundary,
        MainTailRuntimeState {
            eq_low: eq_low.as_mut_ptr(),
            prev_claim_coordinates: claim_coordinates.as_ptr(),
            seed: seed.as_mut_ptr(),
            claim: claim.as_mut_ptr(),
            eq_prefactor: eq_prefactor.as_mut_ptr(),
            coefficients_out: coefficients.as_mut_ptr(),
            challenges_out,
        },
        context,
    )
    .unwrap();
    let mut dispatch = MainTailDispatchCounters::default();
    let launched = launch_main_tail_counted(launch, context, &mut dispatch).unwrap();
    let challenge_slice: &DeviceSlice<E4> = match claim_mode {
        ClaimMode::Aliased => &claim_coordinates,
        ClaimMode::Detached => &detached_challenges,
    };
    let output = schedule_readback(
        FinalColumnsReadback::Contiguous(launched.final_level().allocation()),
        &coefficients,
        challenge_slice,
        &seed,
        &claim,
        &eq_prefactor,
        &eq_low,
        context,
    )
    .finish();
    assert_eq!(launched.final_level().shape().column_elems, 2);
    let high_eq_folds = output
        .eq_high
        .iter()
        .filter(|slot| **slot != E4::ONE)
        .count();
    ArmObservation {
        output,
        round_boundaries,
        final_eq_sizes: boundary_sizes,
        final_semantic_suffix_offset: boundary_suffix,
        final_stride: launched.final_level().shape().column_elems,
        coverage: PathCoverage {
            main_tail_launches: dispatch.main_tail_launches,
            per_round_remainder_launches: dispatch.per_round_remainder_launches,
            high_eq_folds,
            fold_weight_symbol_writes: dispatch.fold_weight_symbol_writes,
        },
    }
}

fn run_per_round_arm(
    context: &ProverContext,
    fixture: &Fixture,
    claim_mode: ClaimMode,
) -> ArmObservation {
    let (entry, _entry_staging) = make_entry_level(context, fixture);
    let eq_state = fixture.eq_state();
    let _eq_high_staging = write_eq_high_sentinels(context, &eq_state.high_sentinels);
    let (mut eq_low, _eq_staging) = upload(context, &eq_state.low);
    let max_acc_size = 1usize << (fixture.tail_rounds - 1);
    let mut partials = context
        .alloc(max_partials_len(max_acc_size), AllocationPlacement::Top)
        .unwrap();
    let storage = GpuGKRStorage::<BF, E4>::default();
    let top_bits = coefficient_top_bits(&fixture.program);
    let mut launch = build_bwd_vm_ext_rounds_after_continuations(
        &storage,
        &fixture.program,
        fixture.entry_round,
        fixture.claim_coordinates.len(),
        eq_low.as_ptr(),
        partials.as_mut_ptr(),
        &top_bits,
        context,
    )
    .unwrap();
    launch
        .adopt_published_level(entry)
        .unwrap_or_else(|(_, error)| panic!("per-round publication adoption: {error:?}"));

    let challenge_slab_values = (0..BWD_SEG_CHALLENGE_SLOTS)
        .map(|slot| lift(701 + 37 * slot as u32))
        .collect::<Vec<_>>();
    let (challenge_slab, _challenge_slab_staging) = upload(context, &challenge_slab_values);
    schedule_bwd_vm_ext_bank_fill(
        &mut launch,
        challenge_slab.as_ptr(),
        unsafe { challenge_slab.as_ptr().add(7) },
        unsafe { challenge_slab.as_ptr().add(8) },
        unsafe { challenge_slab.as_ptr().add(9) },
        context,
    )
    .unwrap();
    let _coefficient_staging = write_coefficient_bank(context, &fixture.coefficient_bank);

    let claim_point = get_main_layer_claim_point_device_ptr();
    let aliased_coordinates = fixture.aliased_claim_and_challenge_coordinates();
    let _claim_point_staging = write_symbol(context, claim_point, &aliased_coordinates);
    let (claim_coordinates, _claim_coordinates_staging) =
        upload(context, &fixture.claim_coordinates);
    let (mut detached_challenges, _detached_challenges_staging) =
        upload(context, &fixture.generated_challenges);
    let (mut seed, _seed_staging) = upload(context, &fixture.seed);
    let (mut claim, _claim_staging) = upload(context, &[fixture.claim]);
    let (mut eq_prefactor, _prefactor_staging) = upload(context, &[fixture.eq_prefactor]);
    let (mut coefficients, _coefficients_staging) = upload(
        context,
        &vec![E4::ZERO; 4 * fixture.claim_coordinates.len()],
    );

    let mut eq_sizes = fixture.eq_boundary.eq_sizes;
    let mut semantic_suffix_offset = fixture.eq_boundary.semantic_suffix_offset;
    let mut round_boundaries = Vec::with_capacity(fixture.tail_rounds);
    let mut dispatch = MainTailDispatchCounters::default();
    for absolute_round in usize::from(fixture.entry_round)..fixture.claim_coordinates.len() {
        round_boundaries.push((semantic_suffix_offset, eq_sizes));
        let acc_size = 1usize << (fixture.claim_coordinates.len() - absolute_round - 1);
        schedule_per_round_remainder_counted(
            &mut launch,
            absolute_round as u32,
            acc_size as u32,
            context,
            &mut dispatch,
        )
        .unwrap();
        assert_eq!(eq_sizes.high, [0, 0]);
        let is_final = absolute_round + 1 == fixture.claim_coordinates.len();
        let active_eq_size = if is_final { 0 } else { eq_sizes.low };
        let previous_coordinate = match claim_mode {
            ClaimMode::Aliased => unsafe { claim_point.add(absolute_round) },
            ClaimMode::Detached => unsafe { claim_coordinates.as_ptr().add(absolute_round) },
        };
        let challenge_out = match claim_mode {
            ClaimMode::Aliased => unsafe { claim_point.add(absolute_round) },
            ClaimMode::Detached => unsafe { detached_challenges.as_mut_ptr().add(absolute_round) },
        };
        launch_backward_dual_finalize_from_partials(
            partials.as_ptr(),
            warp_partial_count(acc_size),
            previous_coordinate,
            seed.as_mut_ptr(),
            claim.as_mut_ptr(),
            eq_prefactor.as_mut_ptr(),
            unsafe { coefficients.as_mut_ptr().add(4 * absolute_round) },
            challenge_out,
            eq_low.as_mut_ptr(),
            active_eq_size,
            context,
        )
        .unwrap();
        if claim_mode == ClaimMode::Detached {
            // The legacy fold-weight kernel consumes the output claim-point
            // symbol. Keep the independently owned challenge output as the
            // observed result, then stream-copy only this completed challenge
            // into the symbol needed by the next round's fold.
            let source = unsafe {
                DeviceSlice::from_raw_parts(detached_challenges.as_ptr().add(absolute_round), 1)
            };
            let destination =
                unsafe { DeviceSlice::from_raw_parts_mut(claim_point.add(absolute_round), 1) };
            memory_copy_async(destination, source, context.get_exec_stream()).unwrap();
        }
        if !is_final {
            record_active_eq_slot_fold(&mut eq_sizes);
            semantic_suffix_offset += 1;
        }
    }

    let source_addresses = semantic_source_addresses(&fixture.program);
    let mut source_pointers = source_addresses
        .iter()
        .copied()
        .map(|address| (address, std::ptr::null()))
        .collect::<BTreeMap<_, _>>();
    assert_eq!(source_pointers.len(), fixture.source_ids.len());
    launch.repoint_final_evaluations(&mut source_pointers);
    let final_pointers = source_addresses
        .iter()
        .map(|address| source_pointers[address])
        .collect::<Vec<_>>();
    // SAFETY: the aliased output is the whole main-layer claim-point symbol.
    let aliased_challenges =
        unsafe { DeviceSlice::from_raw_parts(claim_point, fixture.claim_coordinates.len()) };
    let challenges: &DeviceSlice<E4> = match claim_mode {
        ClaimMode::Aliased => aliased_challenges,
        ClaimMode::Detached => &detached_challenges,
    };
    let output = schedule_readback(
        FinalColumnsReadback::Scattered(&final_pointers),
        &coefficients,
        challenges,
        &seed,
        &claim,
        &eq_prefactor,
        &eq_low,
        context,
    )
    .finish();
    let high_eq_folds = output
        .eq_high
        .iter()
        .filter(|slot| **slot != E4::ONE)
        .count();
    ArmObservation {
        output,
        round_boundaries,
        final_eq_sizes: eq_sizes,
        final_semantic_suffix_offset: semantic_suffix_offset,
        final_stride: 2,
        coverage: PathCoverage {
            main_tail_launches: dispatch.main_tail_launches,
            per_round_remainder_launches: dispatch.per_round_remainder_launches,
            high_eq_folds,
            fold_weight_symbol_writes: dispatch.fold_weight_symbol_writes,
        },
    }
}

fn arm_matches_reference(
    arm: &ArmObservation,
    expected: &MainTailReferenceOutput,
    fixture: &Fixture,
) -> bool {
    let tail_start = usize::from(fixture.entry_round);
    let tail_end = tail_start + fixture.tail_rounds;
    let expected_coefficients = expected
        .rounds
        .iter()
        .flat_map(|round| round.coefficients)
        .collect::<Vec<_>>();
    let expected_challenges = expected
        .rounds
        .iter()
        .map(|round| round.challenge)
        .collect::<Vec<_>>();
    arm.output.final_columns == expected.final_columns
        && arm.output.coefficients[4 * tail_start..4 * tail_end] == expected_coefficients
        && arm.output.challenges[tail_start..tail_end] == expected_challenges
        && arm.output.seed == expected.seed
        && arm.output.claim == [expected.claim]
        && arm.output.eq_prefactor == [expected.eq_prefactor]
        && arm.output.eq_low[..expected.final_eq_low.len()] == expected.final_eq_low
        && expected.final_eq_low.len()
            == 1usize
                << (expected.final_eq_sizes.high[0]
                    + expected.final_eq_sizes.high[1]
                    + expected.final_eq_sizes.low)
        && arm.round_boundaries
            == expected
                .rounds
                .iter()
                .map(|round| (round.semantic_suffix_offset, round.eq_sizes))
                .collect::<Vec<_>>()
        && arm.final_eq_sizes == expected.final_eq_sizes
        && arm.final_semantic_suffix_offset == expected.final_semantic_suffix_offset
        && arm.final_stride == expected.final_stride
}

fn assert_arm_matches_reference(
    label: &str,
    arm: &ArmObservation,
    expected: &MainTailReferenceOutput,
    fixture: &Fixture,
) {
    let tail_start = usize::from(fixture.entry_round);
    assert_eq!(arm.round_boundaries.len(), expected.rounds.len(), "{label}");
    for (iteration, round) in expected.rounds.iter().enumerate() {
        let absolute_round = tail_start + iteration;
        assert_eq!(
            &arm.output.coefficients[4 * absolute_round..4 * absolute_round + 4],
            &round.coefficients,
            "{label}: coefficients at round {absolute_round}",
        );
        assert_eq!(
            arm.output.challenges[absolute_round], round.challenge,
            "{label}: challenge at round {absolute_round}",
        );
        assert_eq!(
            arm.round_boundaries[iteration],
            (round.semantic_suffix_offset, round.eq_sizes),
            "{label}: pass-local Eq boundary at round {absolute_round}",
        );
    }
    assert_eq!(arm.output.seed, expected.seed, "{label}: seed");
    assert_eq!(arm.output.claim, [expected.claim], "{label}: claim");
    assert_eq!(
        arm.output.eq_prefactor,
        [expected.eq_prefactor],
        "{label}: Eq prefactor",
    );
    assert_eq!(
        arm.final_eq_sizes, expected.final_eq_sizes,
        "{label}: final Eq sizes",
    );
    assert_eq!(
        arm.final_semantic_suffix_offset, expected.final_semantic_suffix_offset,
        "{label}: final semantic suffix offset",
    );
    assert_eq!(
        arm.final_stride, expected.final_stride,
        "{label}: final source stride",
    );
    let observed_eq = &arm.output.eq_low[..expected.final_eq_low.len()];
    assert_eq!(observed_eq, expected.final_eq_low, "{label}: final Eq");
    assert_eq!(
        as_bytes(observed_eq),
        as_bytes(&expected.final_eq_low),
        "{label}: final Eq raw bytes",
    );
    assert_eq!(
        arm.output.eq_high,
        [E4::ONE, E4::ONE],
        "{label}: strict Eq-high identity slots",
    );
    assert_eq!(
        arm.output.final_columns.len(),
        fixture.source_ids.len() * 2,
        "{label}: final source extent",
    );
    for source in 0..fixture.source_ids.len() {
        let range = 2 * source..2 * source + 2;
        assert_eq!(
            as_bytes(&arm.output.final_columns[range.clone()]),
            as_bytes(&expected.final_columns[range]),
            "{label}: final source {source} raw bytes",
        );
    }
    assert!(arm_matches_reference(arm, expected, fixture));
}

fn assert_arms_match(
    case: DifferentialCase,
    megakernel: &ArmObservation,
    per_round: &ArmObservation,
    fixture: &Fixture,
) {
    let start = usize::from(fixture.entry_round);
    let end = start + fixture.tail_rounds;
    assert_eq!(
        &megakernel.output.coefficients[4 * start..4 * end],
        &per_round.output.coefficients[4 * start..4 * end],
        "{case:?}: arm coefficient mismatch",
    );
    assert_eq!(
        &megakernel.output.challenges[start..end],
        &per_round.output.challenges[start..end],
        "{case:?}: arm challenge mismatch",
    );
    assert_eq!(megakernel.output.seed, per_round.output.seed, "{case:?}");
    assert_eq!(megakernel.output.claim, per_round.output.claim, "{case:?}");
    assert_eq!(
        megakernel.output.eq_prefactor, per_round.output.eq_prefactor,
        "{case:?}",
    );
    assert_eq!(
        as_bytes(&megakernel.output.eq_low[..1]),
        as_bytes(&per_round.output.eq_low[..1]),
        "{case:?}: arm Eq raw-byte mismatch",
    );
    assert_eq!(
        megakernel.output.eq_high, per_round.output.eq_high,
        "{case:?}: arm Eq-high mismatch",
    );
    assert_eq!(
        megakernel.final_eq_sizes, per_round.final_eq_sizes,
        "{case:?}",
    );
    assert_eq!(
        megakernel.round_boundaries, per_round.round_boundaries,
        "{case:?}: arm per-round Eq boundary mismatch",
    );
    assert_eq!(
        megakernel.final_semantic_suffix_offset, per_round.final_semantic_suffix_offset,
        "{case:?}",
    );
    assert_eq!(megakernel.final_stride, 2, "{case:?}");
    assert_eq!(per_round.final_stride, 2, "{case:?}");
    for source in 0..fixture.source_ids.len() {
        let range = 2 * source..2 * source + 2;
        assert_eq!(
            as_bytes(&megakernel.output.final_columns[range.clone()]),
            as_bytes(&per_round.output.final_columns[range]),
            "{case:?}: arm final source {source} raw-byte mismatch",
        );
    }
}

#[test]
fn gpu_main_tail_matches_cpu_and_per_round() {
    let context = make_test_context(256, 64);
    let program = max_source_program();
    let cases = differential_cases();
    assert!(cases.len() >= 32);
    for case in cases.iter().copied() {
        let fixture = Fixture::for_case(program.clone(), case);
        assert_eq!(fixture.source_ids.len(), 1_012, "{case:?}");
        let expected =
            main_tail_reference(fixture.reference_input_for(case.claim_mode.reference())).unwrap();
        let megakernel = run_main_tail_arm(&context, &fixture, case.claim_mode);
        let per_round = run_per_round_arm(&context, &fixture, case.claim_mode);
        assert_arm_matches_reference("megakernel", &megakernel, &expected, &fixture);
        assert_arm_matches_reference("per-round", &per_round, &expected, &fixture);
        assert_arms_match(case, &megakernel, &per_round, &fixture);
        assert_eq!(
            megakernel.coverage,
            PathCoverage {
                main_tail_launches: 1,
                ..PathCoverage::default()
            },
            "{case:?}: megakernel path coverage",
        );
        assert_eq!(
            per_round.coverage,
            PathCoverage {
                per_round_remainder_launches: fixture.tail_rounds,
                fold_weight_symbol_writes: fixture.tail_rounds,
                ..PathCoverage::default()
            },
            "{case:?}: per-round path coverage",
        );
    }
    assert_eq!(cases.len(), 36);
}

#[test]
fn gpu_main_tail_gpu_mutation() {
    let context = make_test_context(256, 64);
    let case = DifferentialCase {
        folding_steps: 11,
        entry_round: 6,
        claim_mode: ClaimMode::Aliased,
        salt: 17,
        ruled: false,
    };
    let fixture = Fixture::for_case(max_source_program(), case);
    let correct =
        main_tail_reference(fixture.reference_input_for(case.claim_mode.reference())).unwrap();
    let megakernel = run_main_tail_arm(&context, &fixture, case.claim_mode);
    let per_round = run_per_round_arm(&context, &fixture, case.claim_mode);
    assert_arm_matches_reference("megakernel", &megakernel, &correct, &fixture);
    assert_arm_matches_reference("per-round", &per_round, &correct, &fixture);

    for (label, mutation) in [
        ("q-order", MainTailReferenceMutation::PermuteD3QOrder),
        (
            "reversed-challenge",
            MainTailReferenceMutation::ReverseD3Challenges,
        ),
        ("final-fold", MainTailReferenceMutation::ExtraFinalEqFold),
    ] {
        let mutated = main_tail_reference_with_mutation(
            fixture.reference_input_for(case.claim_mode.reference()),
            mutation,
        )
        .unwrap();
        assert!(
            !arm_matches_reference(&megakernel, &mutated, &fixture),
            "{label} mutation survived the megakernel differential",
        );
        assert!(
            !arm_matches_reference(&per_round, &mutated, &fixture),
            "{label} mutation survived the per-round differential",
        );
    }

    let mut cumulative_eq = Fixture::for_case(fixture.program.clone(), case);
    cumulative_eq.eq_boundary.semantic_suffix_offset = 1;
    cumulative_eq.eq_boundary.eq_sizes = make_eq_sizes(case.folding_steps - 1);
    cumulative_eq.entry_eq_low = direct_eq(&cumulative_eq.claim_coordinates[1..]);
    assert!(
        matches!(
            main_tail_reference(cumulative_eq.reference_input_for(case.claim_mode.reference())),
            Err(MainTailReferenceError::BoundarySuffixOffset { .. })
        ),
        "cumulative Eq must be rejected before it can enter the differential",
    );
    let (cumulative_entry, _cumulative_entry_staging) = make_entry_level(&context, &cumulative_eq);
    let e4_pointer = core::ptr::NonNull::<E4>::dangling().as_ptr();
    let seed_pointer = core::ptr::NonNull::<u32>::dangling().as_ptr();
    assert!(matches!(
        bind_main_tail(
            cumulative_eq.program.layer,
            &cumulative_eq.tail_program,
            cumulative_entry,
            usize::from(cumulative_eq.entry_round),
            cumulative_eq.claim_coordinates.len(),
            cumulative_eq.eq_boundary,
            MainTailRuntimeState {
                eq_low: e4_pointer,
                prev_claim_coordinates: e4_pointer,
                seed: seed_pointer,
                claim: e4_pointer,
                eq_prefactor: e4_pointer,
                coefficients_out: e4_pointer,
                challenges_out: e4_pointer,
            },
            &context,
        ),
        Err(MainTailBindError::EqBoundarySuffix { .. })
            | Err(MainTailBindError::EqBoundarySizes { .. })
    ));
    assert!(
        matches!(
            main_tail_reference_with_mutation(
                fixture.reference_input_for(case.claim_mode.reference()),
                MainTailReferenceMutation::SkipFirstNonFinalEqFold,
            ),
            Err(MainTailReferenceError::EqEvolutionLength { .. })
        ),
        "skipping the first pass-local Eq fold must be observable",
    );
}

#[test]
fn gpu_main_tail_smoke_matches_reference() {
    let context = make_test_context(256, 64);
    let fixture = Fixture::deterministic();
    assert!(fixture.tail_rounds >= 2);
    let expected = main_tail_reference(fixture.reference_input()).unwrap();
    let entry_bytes = fixture.columns.len() * size_of::<E4>();

    let (entry_allocation, _entry_staging) = upload(&context, &fixture.columns);
    let entry = ContinuationPublishedLevel::try_new(
        ContinuationPublishedShape {
            depth: fixture.entry_depth,
            columns: fixture.source_ids.len(),
            column_elems: 1usize << (fixture.tail_rounds + 3),
        },
        entry_allocation,
        fixture
            .source_ids
            .iter()
            .copied()
            .map(|source| (source, source.0 as usize)),
    )
    .unwrap();
    let _coefficient_staging = write_coefficient_bank(&context, &fixture.coefficient_bank);
    let eq_state = fixture.eq_state();
    let _eq_high_staging = write_eq_high_sentinels(&context, &eq_state.high_sentinels);
    let (claim_coordinates, _claim_coordinates_staging) =
        upload(&context, &fixture.claim_coordinates);
    let (mut eq_low, _eq_staging) = upload(&context, &eq_state.low);
    let (mut seed, _seed_staging) = upload(&context, &fixture.seed);
    let (mut claim, _claim_staging) = upload(&context, &[fixture.claim]);
    let (mut eq_prefactor, _prefactor_staging) = upload(&context, &[fixture.eq_prefactor]);
    let folding_steps = fixture.claim_coordinates.len();
    let (mut coefficients, _coefficients_staging) =
        upload(&context, &vec![E4::ZERO; 4 * folding_steps]);
    let (mut challenges, _challenges_staging) = upload(&context, &fixture.generated_challenges);

    let launch = bind_main_tail(
        fixture.program.layer,
        &fixture.tail_program,
        entry,
        usize::from(fixture.entry_round),
        folding_steps,
        fixture.eq_boundary,
        MainTailRuntimeState {
            eq_low: eq_low.as_mut_ptr(),
            prev_claim_coordinates: claim_coordinates.as_ptr(),
            seed: seed.as_mut_ptr(),
            claim: claim.as_mut_ptr(),
            eq_prefactor: eq_prefactor.as_mut_ptr(),
            coefficients_out: coefficients.as_mut_ptr(),
            challenges_out: challenges.as_mut_ptr(),
        },
        &context,
    )
    .unwrap();
    let mut launch_observer = context.observe_device_memory_high_water();
    let launched = launch_main_tail(launch, &context).unwrap();
    let launch_snapshot = launch_observer.seal();
    let launch_report = launch_observer.finish();
    assert_eq!(
        launch_snapshot.physical_backing_peak_bytes,
        launch_snapshot.start.physical_backing_bytes
    );
    assert_eq!(
        launch_snapshot.logical_live_peak_bytes,
        launch_snapshot.start.logical_live_bytes
    );
    assert_eq!(launch_snapshot.summed_requested_bytes, 0);
    let reclaimed_physical_bytes = launch_snapshot
        .start
        .physical_backing_bytes
        .checked_sub(launch_snapshot.peak_window_end.physical_backing_bytes)
        .expect("main-tail launch must not increase physical backing");
    let reclaimed_logical_bytes = launch_snapshot
        .start
        .logical_live_bytes
        .checked_sub(launch_snapshot.peak_window_end.logical_live_bytes)
        .expect("main-tail launch must not increase logical live memory");
    assert_eq!(reclaimed_physical_bytes, reclaimed_logical_bytes);
    assert!(
        reclaimed_logical_bytes >= entry_bytes,
        "launch must reclaim at least the requested entry allocation"
    );
    assert_eq!(launch_report.start, launch_snapshot.start);
    assert_eq!(
        launch_report.physical_backing_peak_bytes,
        launch_snapshot.start.physical_backing_bytes
    );
    assert_eq!(
        launch_report.logical_live_peak_bytes,
        launch_snapshot.start.logical_live_bytes
    );
    assert_eq!(launch_report.summed_requested_bytes, 0);
    assert_eq!(
        launch_report.peak_window_end,
        launch_snapshot.peak_window_end
    );
    assert_eq!(
        launch_report.return_to_entry,
        launch_snapshot.peak_window_end
    );

    let final_elems = fixture.source_ids.len() * 2;
    let final_bytes = final_elems * size_of::<E4>();
    let scratch_bytes = launched.scratch().len() * size_of::<E4>();
    assert_eq!(
        launched.final_level().shape(),
        ContinuationPublishedShape {
            depth: (folding_steps - 1) as u8,
            columns: fixture.source_ids.len(),
            column_elems: 2,
        }
    );
    assert_eq!(launched.final_level().allocation().len(), final_elems);
    assert_eq!(
        launched.final_level().allocation().len() * size_of::<E4>(),
        final_bytes
    );
    assert_eq!(launched.scratch().len(), fixture.source_ids.len() * 16);
    assert!(final_bytes < scratch_bytes);
    assert!(fixture.source_ids.len() > 2);
    for source in [0, 1, fixture.source_ids.len() - 1] {
        assert_eq!(
            launched.final_level().source_ptr(SourceId(source as u32)),
            launched.final_level().as_ptr().wrapping_add(source * 2)
        );
    }

    let observation = schedule_readback(
        FinalColumnsReadback::Contiguous(launched.final_level().allocation()),
        &coefficients,
        &challenges,
        &seed,
        &claim,
        &eq_prefactor,
        &eq_low,
        &context,
    )
    .finish();
    let tail_start = usize::from(fixture.entry_round);
    let tail_end = tail_start + fixture.tail_rounds;
    let expected_coefficients = expected
        .rounds
        .iter()
        .flat_map(|round| round.coefficients)
        .collect::<Vec<_>>();
    let expected_challenges = expected
        .rounds
        .iter()
        .map(|round| round.challenge)
        .collect::<Vec<_>>();
    assert_eq!(observation.final_columns, expected.final_columns);
    assert_eq!(as_bytes(&observation.final_columns).len(), final_bytes);
    assert_eq!(
        as_bytes(&observation.final_columns),
        as_bytes(&expected.final_columns)
    );
    assert_eq!(
        &observation.coefficients[4 * tail_start..4 * tail_end],
        expected_coefficients.as_slice()
    );
    assert_eq!(
        &observation.challenges[tail_start..tail_end],
        expected_challenges.as_slice()
    );
    assert_eq!(observation.seed, expected.seed);
    assert_eq!(observation.claim, [expected.claim]);
    assert_eq!(observation.eq_prefactor, [expected.eq_prefactor]);
    assert_eq!(observation.eq_low[0], expected.final_eq_low[0]);
    assert_eq!(expected.final_eq_sizes, make_eq_sizes(0));
    assert_eq!(expected.final_semantic_suffix_offset as usize, tail_end);
    assert_eq!(fixture.source_ids[0], SourceId(0));
}
