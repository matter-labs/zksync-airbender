#![cfg(not(no_cuda))]

use core::mem::{size_of, size_of_val};
use std::sync::{Arc, Mutex};

use era_cudart::event::{CudaEvent, CudaEventCreateFlags};
use era_cudart::memory::memory_copy_async;
use era_cudart::slice::DeviceSlice;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::callbacks::Callbacks;
use gpu_core::primitives::context::{DeviceAllocation, HostAllocation};
use gpu_core::primitives::field::{BF, E4};
use gpu_core::primitives::static_host::{alloc_static_pinned_box_from_slice, StaticPinnedBox};
use gpu_gkr_compiler::{CoefficientRecipeId, SourceId};
use gpu_prover_context::ProverContext;

use super::binding::{bind_main_tail, launch_main_tail, MainTailRuntimeState};
use super::reference::{
    main_tail_reference, MainTailClaimOutput, MainTailReferenceEntry, MainTailReferenceInput,
};
use super::{lower_main_tail_program, MainTailProgram, MAIN_TAIL_BLOB_BYTES};
use crate::backward::main_continuation::{ContinuationPublishedLevel, ContinuationPublishedShape};
use crate::backward::main_layer::execution_plan::MainEqBoundaryWitness;
use crate::backward::vm::seg::bwd_seg_coeff_bank_device_ptr;
use crate::backward::{compile_corpus_layout, make_eq_sizes};
use crate::test_utils::make_test_context;
use crate::upstream::{Field, FieldExtension, PrimeField};

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

    fn reference_input(&self) -> MainTailReferenceInput<'_> {
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
            claim_coordinates: &self.claim_coordinates,
            entry_eq_low: &self.entry_eq_low,
            seed: self.seed,
            claim: self.claim,
            eq_prefactor: self.eq_prefactor,
            entry_round: self.entry_round,
            eq_boundary: self.eq_boundary,
            claim_output: MainTailClaimOutput::Detached,
        }
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

#[derive(Debug)]
struct Observation {
    final_columns: Vec<E4>,
    coefficients: Vec<E4>,
    challenges: Vec<E4>,
    seed: Vec<u32>,
    claim: Vec<E4>,
    eq_prefactor: Vec<E4>,
    eq_low: Vec<E4>,
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

#[allow(clippy::too_many_arguments)]
fn schedule_readback<'a>(
    final_columns: &DeviceAllocation<E4>,
    coefficients: &DeviceAllocation<E4>,
    challenges: &DeviceAllocation<E4>,
    seed: &DeviceAllocation<u32>,
    claim: &DeviceAllocation<E4>,
    eq_prefactor: &DeviceAllocation<E4>,
    eq_low: &DeviceAllocation<E4>,
    context: &'a ProverContext,
) -> ReadbackJob<'a> {
    let stream = context.get_exec_stream();
    let mut final_host = unsafe { context.alloc_host_uninit_slice(final_columns.len()) };
    let mut coefficients_host = unsafe { context.alloc_host_uninit_slice(coefficients.len()) };
    let mut challenges_host = unsafe { context.alloc_host_uninit_slice(challenges.len()) };
    let mut seed_host = unsafe { context.alloc_host_uninit_slice(seed.len()) };
    let mut claim_host = unsafe { context.alloc_host_uninit_slice(claim.len()) };
    let mut prefactor_host = unsafe { context.alloc_host_uninit_slice(eq_prefactor.len()) };
    let mut eq_low_host = unsafe { context.alloc_host_uninit_slice(eq_low.len()) };
    memory_copy_async(&mut final_host, final_columns, stream).unwrap();
    memory_copy_async(&mut coefficients_host, coefficients, stream).unwrap();
    memory_copy_async(&mut challenges_host, challenges, stream).unwrap();
    memory_copy_async(&mut seed_host, seed, stream).unwrap();
    memory_copy_async(&mut claim_host, claim, stream).unwrap();
    memory_copy_async(&mut prefactor_host, eq_prefactor, stream).unwrap();
    memory_copy_async(&mut eq_low_host, eq_low, stream).unwrap();

    let final_accessor = final_host.get_accessor();
    let coefficients_accessor = coefficients_host.get_accessor();
    let challenges_accessor = challenges_host.get_accessor();
    let seed_accessor = seed_host.get_accessor();
    let claim_accessor = claim_host.get_accessor();
    let prefactor_accessor = prefactor_host.get_accessor();
    let eq_low_accessor = eq_low_host.get_accessor();
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
        output,
    }
}

#[test]
fn gpu_main_tail_smoke_matches_reference() {
    let context = make_test_context(256, 64);
    let fixture = Fixture::deterministic();
    assert!(fixture.tail_rounds >= 2);
    let expected = main_tail_reference(fixture.reference_input()).unwrap();

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
    let (claim_coordinates, _claim_coordinates_staging) =
        upload(&context, &fixture.claim_coordinates);
    let (mut eq_low, _eq_staging) = upload(&context, &fixture.entry_eq_low);
    let (mut seed, _seed_staging) = upload(&context, &fixture.seed);
    let (mut claim, _claim_staging) = upload(&context, &[fixture.claim]);
    let (mut eq_prefactor, _prefactor_staging) = upload(&context, &[fixture.eq_prefactor]);
    let folding_steps = fixture.claim_coordinates.len();
    let (mut coefficients, _coefficients_staging) =
        upload(&context, &vec![E4::ZERO; 4 * folding_steps]);
    let (mut challenges, _challenges_staging) = upload(&context, &vec![E4::ZERO; folding_steps]);

    let launch = bind_main_tail(
        fixture.program.layer,
        &fixture.tail_program,
        &entry,
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
    assert_eq!(launch_snapshot.peak_window_end, launch_snapshot.start);
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
    assert_eq!(launch_report.peak_window_end, launch_snapshot.start);
    assert_eq!(launch_report.return_to_entry, launch_snapshot.start);

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
    assert_eq!(launched.program_blob_device().len(), MAIN_TAIL_BLOB_BYTES);
    assert!(fixture.source_ids.len() > 2);
    for source in [0, 1, fixture.source_ids.len() - 1] {
        assert_eq!(
            launched.final_level().source_ptr(SourceId(source as u32)),
            launched.final_level().as_ptr().wrapping_add(source * 2)
        );
    }

    let observation = schedule_readback(
        launched.final_level().allocation(),
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
