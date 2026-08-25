//! GPU differential for the universal dimension-reducing width-3 R0 producer.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use era_cudart::memory::memory_copy_async;
use era_cudart::slice::DeviceSlice;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::{BF, E4};
use gpu_gkr_compiler::{
    lower_dr_window_program, project_dr_window_inputs, DrWindowInputOutput,
    DrWindowInputProjection, DrWindowProgram, DR_WINDOWED_CONT_KERNEL_SYMBOL,
    DR_WINDOWED_R0_KERNEL_SYMBOL,
};
use gpu_prover_context::ProverContext;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

use super::binding::{
    bind_dr_window_continuation_launch, bind_dr_window_continuations, bind_dr_window_r0,
    build_dr_window_continuation_batch, dr_window_partials_len, launch_dr_window_continuation,
    launch_dr_window_r0, DrContinuationFactoredEqScratch, DrWindowContinuationArena,
    DrWindowContinuationSource, DrWindowRuntimeScratch,
};
use super::composition::{
    continuation_window_count, megakernel_entry_round, plan_dr_window_continuations,
    DrWindowLayerCompositionHook, DrWindowPassEqState,
};
use super::reference::{
    compare_dr_tensors, dr_continuation_tensor_reference, dr_final_lookup_four_cells,
    dr_r0_tensor_reference, fold_dr_continuation_depth3, DrTensorMismatch, DrTensorOracleProgram,
};
use crate::backward::dim_reducing_encoder::{
    build_continuation_batch_compact_for_arenas, build_round0_batch_compact,
    build_round1_batch_compact_for_arena,
};
use crate::backward::dim_reducing_sumcheck_plan::launch_dr_window_continuation_chain_for_test;
use crate::backward::kernels::{
    eq_group_count, get_dim_reducing_layer_claim_point_device_ptr, get_eq_high_constant_device_ptr,
    launch_backward_dual_finalize_from_acc, launch_build_eq_high_and_low_groups_from_point,
    launch_build_eq_independent_groups_from_point,
    launch_dim_reducing_continuation_batched_compact, launch_dim_reducing_round0_batched_compact,
    make_eq_sizes, record_active_eq_slot_fold, resolve_active_eq_slot,
    schedule_dim_reducing_batch_challenge_table_prelude, FoldingArenaBinding, GkrEqSizes,
    GpuGKRDimensionReducingBatch, GpuGKRDimensionReducingLayerSlots, GKR_EQ_GROUP_TABLE_LEN,
    MAX_DIM_REDUCING_LAYER_CLAIM_POINT_LEN,
};
use crate::backward::window::reference::tensor_round_tail_reference;
use crate::backward::window::tail::{
    launch_window_tensor_round_tail, WindowTailArm, WindowTailState,
};
use crate::backward::{
    derive_dimension_reducing_inputs, legacy_dimension_reducing_slots_for_test,
    CONTINUATION_GOLDEN_CORPUS,
};
use crate::gkr_address_audit::AddressClass;
use crate::storage_layout::{FieldType, GpuGKRLayerLayout, GpuGKRStorageLayout};
use crate::test_utils::make_test_context;
use crate::upstream::{DimensionReducingInputOutput, Field, GKRAddress, OutputType, PrimeField};
use crate::GpuGKRStorage;

const INPUT_LAYER: usize = 7;
const OUTPUT_LAYER: usize = 8;
const DR_SLOT_COUNT: usize = 5;
const TENSOR_CELLS: usize = 27;
const PEELED_COORDINATES: usize = 3;
const OBSERVED_MASKS: [u32; 4] = [0x01, 0x0d, 0x0f, 0x1f];
const UNOBSERVED_WELL_FORMED_MASK: u32 = 0x02;

fn continuation_eq_scratch(
    context: &ProverContext,
    folding_steps: usize,
) -> DrContinuationFactoredEqScratch {
    let geometries = plan_dr_window_continuations(
        folding_steps,
        continuation_window_count(folding_steps),
        megakernel_entry_round(folding_steps),
    )
    .unwrap();
    DrContinuationFactoredEqScratch::allocate(context, &geometries).unwrap()
}
const TENSOR_INSTANCES_PER_MASK: usize = 32;
const CORPUS_FINAL_TRACE_LOG: u32 = 4;

#[derive(Clone, Debug, PartialEq, Eq)]
struct ProductionDrFinalOrderMismatch {
    layout_name: &'static str,
    absolute_layer: usize,
    enabled_mask: u32,
    publication_indices: Vec<usize>,
}

fn production_dr_final_order_mismatches() -> Vec<ProductionDrFinalOrderMismatch> {
    let mut checked_layers = 0usize;
    let mut merge_layers = 0usize;
    let mut mismatches = Vec::new();
    for (layout_name, _) in CONTINUATION_GOLDEN_CORPUS {
        let (programs, main_layers) = crate::backward::compile_corpus_layout(layout_name);
        let runtime = programs.runtime_circuit();
        let initial_trace_log = runtime.trace_len.trailing_zeros();
        let legacy_layers = derive_dimension_reducing_inputs(
            main_layers,
            &runtime.global_output_map,
            initial_trace_log,
            CORPUS_FINAL_TRACE_LOG,
        );
        let layout =
            GpuGKRStorageLayout::from_artifact_with_tower(runtime, CORPUS_FINAL_TRACE_LOG as usize);
        let bundle = programs
            .resolve_dr_window_programs(CORPUS_FINAL_TRACE_LOG)
            .unwrap();
        for (absolute_layer, legacy_description) in legacy_layers {
            let legacy_slots = legacy_dimension_reducing_slots_for_test(&legacy_description);
            let canonical = bundle
                .layer(absolute_layer)
                .unwrap()
                .input_projection()
                .canonical_sources();
            let raw = legacy_slots.input_addresses().collect::<Vec<_>>();
            let raw_sorted = raw.iter().copied().collect::<BTreeSet<_>>();
            merge_layers += usize::from(raw_sorted.len() != canonical.len());
            let publication_indices = raw_sorted
                .iter()
                .map(|raw| {
                    let canonical_address = layout.aliases.get(raw).copied().unwrap_or(*raw);
                    canonical.binary_search(&canonical_address).unwrap()
                })
                .collect::<Vec<_>>();
            if publication_indices != (0..canonical.len()).collect::<Vec<_>>() {
                mismatches.push(ProductionDrFinalOrderMismatch {
                    layout_name,
                    absolute_layer,
                    enabled_mask: legacy_slots.enabled_mask(),
                    publication_indices,
                });
            }
            checked_layers += 1;
        }
    }
    assert_eq!(checked_layers, 229);
    assert_eq!(merge_layers, 0);
    assert_eq!(mismatches.len(), 9);
    mismatches
}

fn output_type(slot: usize) -> OutputType {
    match slot {
        0 => OutputType::PermutationProduct,
        1 => OutputType::Lookup16Bits,
        2 => OutputType::LookupTimestamps,
        3 => OutputType::GenericLookup,
        4 => OutputType::InitsAndTeardownsProduct,
        _ => unreachable!("DR slot is a five-bit mask position"),
    }
}

fn input_address(slot: usize, operand: usize) -> GKRAddress {
    GKRAddress::InnerLayer {
        layer: INPUT_LAYER,
        offset: 2 * slot + operand,
    }
}

fn aliased_input_address(publication_index: usize) -> GKRAddress {
    GKRAddress::InnerLayer {
        layer: INPUT_LAYER,
        offset: 2 * DR_SLOT_COUNT + publication_index,
    }
}

fn output_address(slot: usize, operand: usize) -> GKRAddress {
    GKRAddress::InnerLayer {
        layer: OUTPUT_LAYER,
        offset: 2 * slot + operand,
    }
}

fn add(mut left: E4, right: E4) -> E4 {
    left.add_assign(&right);
    left
}

fn mul(mut left: E4, right: E4) -> E4 {
    left.mul_assign(&right);
    left
}

fn eq_weight(bit: usize, coordinate: E4) -> E4 {
    if bit == 0 {
        let mut result = E4::ONE;
        result.sub_assign(&coordinate);
        result
    } else {
        coordinate
    }
}

fn random_e4(rng: &mut StdRng) -> E4 {
    E4::from_array_of_base(core::array::from_fn(|_| {
        BF::from_u32_with_reduction(rng.random())
    }))
}

fn upload<T: Copy>(context: &ProverContext, host: &[T]) -> DeviceAllocation<T> {
    let mut device: DeviceAllocation<T> = context
        .alloc(host.len().max(1), AllocationPlacement::BestFit)
        .unwrap();
    memory_copy_async(&mut device[..host.len()], host, context.get_exec_stream()).unwrap();
    device
}

fn download<T: Copy + Default>(context: &ProverContext, device: &DeviceSlice<T>) -> Vec<T> {
    let mut host = vec![T::default(); device.len()];
    memory_copy_async(&mut host[..], device, context.get_exec_stream()).unwrap();
    host
}

fn raw_device_slice<'a, T>(pointer: *const T, len: usize) -> &'a DeviceSlice<T> {
    // SAFETY: every caller passes a live allocation/symbol range of `len`
    // elements and keeps its owner alive through the following synchronization.
    unsafe { DeviceSlice::from_raw_parts(pointer, len) }
}

struct PreparedRun {
    scratch: DeviceAllocation<E4>,
    hook: DrWindowLayerCompositionHook,
    claim_point: DeviceAllocation<E4>,
    _batch_base: DeviceAllocation<E4>,
}

struct ContinuationPassObservation {
    tensor: [E4; TENSOR_CELLS],
    published: Vec<E4>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct DrContinuationChainObservation {
    published: Vec<Vec<E4>>,
    tensors: Vec<[E4; TENSOR_CELLS]>,
    coefficients: Vec<E4>,
    claim_point: Vec<E4>,
    seed: [u32; 8],
    claim: E4,
    eq_prefactor: E4,
    eq_entries: Vec<GkrEqSizes>,
    eq_boundaries: Vec<GkrEqSizes>,
    eq_entry_active_sizes: Vec<u32>,
    eq_entry_active_values: Vec<Vec<E4>>,
    eq_boundary_active_sizes: Vec<u32>,
    eq_boundary_active_values: Vec<Vec<E4>>,
    constant_slab: Vec<E4>,
    r0_low: Vec<E4>,
}

#[derive(Clone, Copy, Debug)]
enum DrContinuationChainMutation {
    Publication,
    Axis,
    BatchExponent,
    ProductExcess,
    EqSuffix,
    ConstantPointer,
    PriorViewReuse,
    CumulativeDrain,
}

fn mutate_dr_continuation_chain(
    observation: &DrContinuationChainObservation,
    mutation: DrContinuationChainMutation,
) -> DrContinuationChainObservation {
    let mut mutated = observation.clone();
    match mutation {
        DrContinuationChainMutation::Publication => {
            mutated.published[0][0].add_assign(&E4::ONE);
        }
        DrContinuationChainMutation::Axis => {
            mutated.tensors[0].swap(1, 3);
            if mutated.tensors == observation.tensors {
                mutated.tensors[0][1].add_assign(&E4::ONE);
            }
        }
        DrContinuationChainMutation::BatchExponent => {
            mutated.tensors[0][9].add_assign(&E4::ONE);
        }
        DrContinuationChainMutation::ProductExcess => {
            for a0 in 0..2 {
                for a1 in 0..2 {
                    for a2 in 0..2 {
                        mutated.tensors[0][9 * a0 + 3 * a1 + a2] = E4::ZERO;
                    }
                }
            }
        }
        DrContinuationChainMutation::EqSuffix => {
            mutated.eq_entries[0] = mutated.eq_boundaries[0];
            mutated.eq_entry_active_sizes[0] = mutated.eq_boundary_active_sizes[0];
            mutated.eq_entry_active_values[0] = mutated.eq_boundary_active_values[0].clone();
        }
        DrContinuationChainMutation::ConstantPointer => {
            let entry_len = mutated.eq_entry_active_values[0].len();
            mutated.eq_entry_active_values[0] = mutated.constant_slab[..entry_len].to_vec();
        }
        DrContinuationChainMutation::PriorViewReuse => {
            mutated.eq_entries[1] = mutated.eq_entries[0];
            mutated.eq_entry_active_sizes[1] = mutated.eq_entry_active_sizes[0];
            mutated.eq_entry_active_values[1] = mutated.eq_entry_active_values[0].clone();
        }
        DrContinuationChainMutation::CumulativeDrain => {
            mutated.eq_entries[1] = mutated.eq_boundaries[0];
            mutated.eq_entry_active_sizes[1] = mutated.eq_boundary_active_sizes[0];
            mutated.eq_entry_active_values[1] = mutated.eq_boundary_active_values[0].clone();
        }
    }
    mutated
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ThreeRoundStateObservation {
    r0_output: [E4; TENSOR_CELLS],
    coefficients: [E4; 12],
    challenges: [E4; PEELED_COORDINATES],
    seed: [u32; 8],
    claim: E4,
    eq_prefactor: E4,
    claim_point_slots: [E4; PEELED_COORDINATES],
    source_before: Vec<u8>,
    source_after: Vec<u8>,
    remaining_eq_values: Vec<E4>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ThreeRoundStateMismatch {
    R0Output { index: usize },
    Coefficient { index: usize },
    Challenge { index: usize },
    Seed { index: usize },
    Claim,
    EqPrefactor,
    ClaimPointSlot { index: usize },
    ExpectedSourceMutation { index: usize },
    ObservedSourceMutation { index: usize },
    SourceBefore { index: usize },
    SourceAfter { index: usize },
    RemainingEqValue { index: usize },
}

fn first_mismatch<T: PartialEq>(left: &[T], right: &[T]) -> Option<usize> {
    left.iter()
        .zip(right)
        .position(|(left, right)| left != right)
        .or_else(|| (left.len() != right.len()).then_some(left.len().min(right.len())))
}

fn compare_three_round_states(
    expected: &ThreeRoundStateObservation,
    observed: &ThreeRoundStateObservation,
) -> Result<(), ThreeRoundStateMismatch> {
    if let Some(index) = first_mismatch(&expected.r0_output, &observed.r0_output) {
        return Err(ThreeRoundStateMismatch::R0Output { index });
    }
    if let Some(index) = first_mismatch(&expected.coefficients, &observed.coefficients) {
        return Err(ThreeRoundStateMismatch::Coefficient { index });
    }
    if let Some(index) = first_mismatch(&expected.challenges, &observed.challenges) {
        return Err(ThreeRoundStateMismatch::Challenge { index });
    }
    if let Some(index) = first_mismatch(&expected.seed, &observed.seed) {
        return Err(ThreeRoundStateMismatch::Seed { index });
    }
    if expected.claim != observed.claim {
        return Err(ThreeRoundStateMismatch::Claim);
    }
    if expected.eq_prefactor != observed.eq_prefactor {
        return Err(ThreeRoundStateMismatch::EqPrefactor);
    }
    if let Some(index) = first_mismatch(&expected.claim_point_slots, &observed.claim_point_slots) {
        return Err(ThreeRoundStateMismatch::ClaimPointSlot { index });
    }
    if let Some(index) = first_mismatch(&expected.source_before, &expected.source_after) {
        return Err(ThreeRoundStateMismatch::ExpectedSourceMutation { index });
    }
    if let Some(index) = first_mismatch(&observed.source_before, &observed.source_after) {
        return Err(ThreeRoundStateMismatch::ObservedSourceMutation { index });
    }
    if let Some(index) = first_mismatch(&expected.source_before, &observed.source_before) {
        return Err(ThreeRoundStateMismatch::SourceBefore { index });
    }
    if let Some(index) = first_mismatch(&expected.source_after, &observed.source_after) {
        return Err(ThreeRoundStateMismatch::SourceAfter { index });
    }
    if let Some(index) =
        first_mismatch(&expected.remaining_eq_values, &observed.remaining_eq_values)
    {
        return Err(ThreeRoundStateMismatch::RemainingEqValue { index });
    }
    Ok(())
}

#[test]
fn cpu_dr_window_production_final_order_mismatch_descriptor_is_exact() {
    let mismatches = production_dr_final_order_mismatches();
    assert_eq!(mismatches.len(), 9);
    for mismatch in mismatches {
        assert!((1..=0x1f).contains(&mismatch.enabled_mask));
        assert_eq!(
            mismatch
                .publication_indices
                .iter()
                .copied()
                .collect::<BTreeSet<_>>(),
            (0..mismatch.publication_indices.len()).collect(),
            "{} layer {} must remain a no-merge permutation",
            mismatch.layout_name,
            mismatch.absolute_layer,
        );
        assert_ne!(
            mismatch.publication_indices,
            (0..mismatch.publication_indices.len()).collect::<Vec<_>>(),
            "{} layer {} must remain a canonical/raw mismatch",
            mismatch.layout_name,
            mismatch.absolute_layer,
        );
    }
}

struct DrGpuFixture<'a> {
    context: &'a ProverContext,
    folding_steps: usize,
    program: DrWindowProgram,
    projection: DrWindowInputProjection,
    oracle_program: DrTensorOracleProgram,
    legacy_slots: GpuGKRDimensionReducingLayerSlots,
    aliases: BTreeMap<GKRAddress, GKRAddress>,
    columns: BTreeMap<GKRAddress, Vec<E4>>,
    storage: GpuGKRStorage<(), E4>,
    input_backing: Arc<DeviceAllocation<E4>>,
    input_stride: usize,
    output_backing: Arc<DeviceAllocation<E4>>,
    output_stride: usize,
    claim_point: Vec<E4>,
    batch_base: E4,
    tail_seed: [u32; 8],
}

impl<'a> DrGpuFixture<'a> {
    fn new(context: &'a ProverContext, mask: u32, folding_steps: usize, seed: u64) -> Self {
        Self::new_with_publication_permutation(context, mask, folding_steps, seed, None)
    }

    fn new_with_publication_permutation(
        context: &'a ProverContext,
        mask: u32,
        folding_steps: usize,
        seed: u64,
        publication_permutation: Option<&[usize]>,
    ) -> Self {
        assert!((1..=0x1f).contains(&mask));
        assert!((4..=12).contains(&folding_steps));
        let raw_inputs = (0..DR_SLOT_COUNT)
            .filter(|slot| mask & (1 << slot) != 0)
            .flat_map(|slot| (0..2).map(move |operand| input_address(slot, operand)))
            .collect::<Vec<_>>();
        let aliases = publication_permutation.map_or_else(BTreeMap::new, |permutation| {
            assert_eq!(permutation.len(), raw_inputs.len());
            assert_eq!(
                permutation.iter().copied().collect::<BTreeSet<_>>(),
                (0..raw_inputs.len()).collect(),
            );
            raw_inputs
                .iter()
                .copied()
                .zip(permutation.iter().copied())
                .map(|(raw, publication_index)| (raw, aliased_input_address(publication_index)))
                .collect()
        });
        let input_stride = 1usize << (folding_steps + 1);
        let output_stride = 1usize << folding_steps;
        let mut rng = StdRng::seed_from_u64(seed);
        let mut rows = BTreeMap::new();
        let mut columns = BTreeMap::<GKRAddress, Vec<E4>>::new();
        let mut input_backing_host = vec![E4::ZERO; 2 * DR_SLOT_COUNT * input_stride];
        let mut output_backing_host = vec![E4::ZERO; 2 * DR_SLOT_COUNT * output_stride];

        for slot in 0..DR_SLOT_COUNT {
            if mask & (1 << slot) == 0 {
                continue;
            }
            let inputs = [input_address(slot, 0), input_address(slot, 1)];
            let outputs = [output_address(slot, 0), output_address(slot, 1)];
            rows.insert(output_type(slot), DrWindowInputOutput::new(inputs, outputs));

            for operand in 0..2 {
                let values = (0..input_stride)
                    .map(|_| random_e4(&mut rng))
                    .collect::<Vec<_>>();
                let poly = 2 * slot + operand;
                input_backing_host[poly * input_stride..(poly + 1) * input_stride]
                    .copy_from_slice(&values);
                columns.insert(inputs[operand], values.clone());
                if let Some(&canonical) = aliases.get(&inputs[operand]) {
                    columns.insert(canonical, values);
                }
            }

            if slot == 0 || slot == 4 {
                for tower in 0..2 {
                    let input = &columns[&inputs[tower]];
                    let output = (0..output_stride)
                        .map(|y| mul(input[2 * y], input[2 * y + 1]))
                        .collect::<Vec<_>>();
                    let poly = 2 * slot + tower;
                    output_backing_host[poly * output_stride..(poly + 1) * output_stride]
                        .copy_from_slice(&output);
                    columns.insert(outputs[tower], output);
                }
            } else {
                let numerator = &columns[&inputs[0]];
                let denominator = &columns[&inputs[1]];
                let output_num = (0..output_stride)
                    .map(|y| {
                        add(
                            mul(numerator[2 * y], denominator[2 * y + 1]),
                            mul(numerator[2 * y + 1], denominator[2 * y]),
                        )
                    })
                    .collect::<Vec<_>>();
                let output_den = (0..output_stride)
                    .map(|y| mul(denominator[2 * y], denominator[2 * y + 1]))
                    .collect::<Vec<_>>();
                for (operand, output) in [output_num, output_den].into_iter().enumerate() {
                    let poly = 2 * slot + operand;
                    output_backing_host[poly * output_stride..(poly + 1) * output_stride]
                        .copy_from_slice(&output);
                    columns.insert(outputs[operand], output);
                }
            }
        }

        let program = lower_dr_window_program(&rows).expect("nonzero five-bit DR mask lowers");
        assert_eq!(program.enabled_mask(), mask);
        let projection = project_dr_window_inputs(&program, &aliases);
        let oracle_program = DrTensorOracleProgram::from_production(&program);
        let legacy_rows = rows
            .iter()
            .map(|(&output_type, row)| {
                (
                    output_type,
                    DimensionReducingInputOutput {
                        inputs: row.inputs().to_vec(),
                        output: row.outputs().to_vec(),
                    },
                )
            })
            .collect::<BTreeMap<_, _>>();
        let legacy_slots = legacy_dimension_reducing_slots_for_test(&legacy_rows);
        assert_eq!(legacy_slots.enabled_mask(), mask);

        let input_backing = Arc::new(upload(context, &input_backing_host));
        let output_backing = Arc::new(upload(context, &output_backing_host));
        let input_class = AddressClass::ThisLayerInnerLayerWrite;
        let output_class = AddressClass::ThisLayerCachedWrite;
        let mut layout_layers = vec![GpuGKRLayerLayout::default(); OUTPUT_LAYER + 1];
        layout_layers[INPUT_LAYER].log2_stride = (folding_steps + 1) as u32;
        layout_layers[OUTPUT_LAYER].log2_stride = folding_steps as u32;
        for slot in 0..DR_SLOT_COUNT {
            if mask & (1 << slot) == 0 {
                continue;
            }
            for operand in 0..2 {
                let raw_input = input_address(slot, operand);
                let canonical_input = aliases.get(&raw_input).copied().unwrap_or(raw_input);
                layout_layers[INPUT_LAYER].index.insert(
                    canonical_input,
                    (input_class, FieldType::Ext, (2 * slot + operand) as u32),
                );
                layout_layers[OUTPUT_LAYER].index.insert(
                    output_address(slot, operand),
                    (output_class, FieldType::Ext, (2 * slot + operand) as u32),
                );
            }
        }
        let layout = GpuGKRStorageLayout {
            trace_len: input_stride,
            artifact_log2_stride: (folding_steps + 1) as u32,
            layers: layout_layers,
            aliases: aliases.clone(),
            scratch_space_mapping_rev: BTreeMap::new(),
        };
        let mut storage = GpuGKRStorage::<(), E4>::default();
        storage.set_layout(Arc::new(layout));
        storage
            .layers
            .resize_with(OUTPUT_LAYER + 1, Default::default);
        storage.layers[INPUT_LAYER]
            .ext_class_backings
            .insert(input_class, Arc::clone(&input_backing));
        storage.layers[OUTPUT_LAYER]
            .ext_class_backings
            .insert(output_class, Arc::clone(&output_backing));

        let claim_point = (0..folding_steps)
            .map(|_| random_e4(&mut rng))
            .collect::<Vec<_>>();
        let mut batch_base = random_e4(&mut rng);
        if batch_base == E4::ZERO || batch_base == E4::ONE {
            batch_base.add_assign(&random_e4(&mut rng));
        }
        assert_ne!(batch_base, E4::ZERO);
        assert_ne!(batch_base, E4::ONE);
        let tail_seed = core::array::from_fn(|_| rng.random());

        Self {
            context,
            folding_steps,
            program,
            projection,
            oracle_program,
            legacy_slots,
            aliases,
            columns,
            storage,
            input_backing,
            input_stride,
            output_backing,
            output_stride,
            claim_point,
            batch_base,
            tail_seed,
        }
    }

    fn expected_tensor(&self) -> [E4; TENSOR_CELLS] {
        dr_r0_tensor_reference(
            &self.oracle_program,
            &self.columns,
            self.batch_base,
            &self.claim_point[PEELED_COORDINATES..],
        )
        .expect("fixture matches the compiler-owned DR program")
    }

    fn prepare(&self) -> PreparedRun {
        let mut scratch: DeviceAllocation<E4> = self
            .context
            .alloc(
                dr_window_partials_len(self.folding_steps),
                AllocationPlacement::BestFit,
            )
            .unwrap();
        let eq = DrWindowPassEqState::allocate(
            self.context,
            PEELED_COORDINATES,
            self.folding_steps - PEELED_COORDINATES,
        )
        .unwrap();
        assert_eq!(eq.build_offset, PEELED_COORDINATES);
        assert_eq!(
            eq.eq_sizes,
            make_eq_sizes(self.folding_steps - PEELED_COORDINATES)
        );
        let claim_point = upload(self.context, &self.claim_point);
        let batch_base = upload(self.context, &[self.batch_base]);
        schedule_dim_reducing_batch_challenge_table_prelude(batch_base.as_ptr(), self.context)
            .unwrap();
        let hook = bind_dr_window_r0(
            &self.program,
            &self.projection,
            &self.storage,
            self.folding_steps,
            eq,
            DrWindowRuntimeScratch {
                partials: scratch.as_mut_ptr(),
                partials_capacity: scratch.len(),
            },
        )
        .expect("production DR R0 binding accepts the fixture");
        assert_eq!(
            hook.r0_launch.selected_symbol(),
            DR_WINDOWED_R0_KERNEL_SYMBOL
        );
        assert!(hook.r0_launch.binding.batch.contributions.is_null());
        launch_dr_window_r0(&hook, claim_point.as_ptr(), self.context).unwrap();
        PreparedRun {
            scratch,
            hook,
            claim_point,
            _batch_base: batch_base,
        }
    }

    fn collect_partial_tensor(&self, prepared: &PreparedRun) -> [E4; TENSOR_CELLS] {
        let partials_len = TENSOR_CELLS * prepared.hook.r0_launch.row_tiles;
        let partials = download(self.context, &prepared.scratch[..partials_len]);
        self.context.get_exec_stream().synchronize().unwrap();
        let mut tensor = [E4::ZERO; TENSOR_CELLS];
        for (index, value) in partials.into_iter().enumerate() {
            tensor[index % TENSOR_CELLS].add_assign(&value);
        }
        tensor
    }

    fn run_producer(&self) -> ([E4; TENSOR_CELLS], &'static str, usize) {
        let prepared = self.prepare();
        let tensor = self.collect_partial_tensor(&prepared);
        (
            tensor,
            prepared.hook.r0_launch.selected_symbol(),
            prepared.hook.r0_launch.row_tiles,
        )
    }

    fn folded_continuation_columns(
        &self,
        source: &BTreeMap<GKRAddress, Vec<E4>>,
        start_round: usize,
    ) -> BTreeMap<GKRAddress, Vec<E4>> {
        let challenges: [E4; 3] = self.claim_point[start_round - 3..start_round]
            .try_into()
            .expect("one continuation consumes three prior challenges");
        self.projection
            .canonical_sources()
            .iter()
            .copied()
            .map(|address| {
                let folded = fold_dr_continuation_depth3(&source[&address], challenges)
                    .expect("fixture source has packed depth-3 geometry");
                (address, folded)
            })
            .collect()
    }

    fn continuation_arena(
        &self,
        start_round: usize,
    ) -> (Arc<DeviceAllocation<E4>>, DrWindowContinuationArena) {
        let poly_count = self.projection.canonical_sources().len();
        let log2_stride = (self.folding_steps + 1 - start_round) as u32;
        let allocation = Arc::new(
            self.context
                .alloc(
                    poly_count * (1usize << log2_stride),
                    AllocationPlacement::BestFit,
                )
                .unwrap(),
        );
        let arena =
            DrWindowContinuationArena::new(Arc::clone(&allocation), log2_stride, poly_count)
                .expect("fixture arena has exact canonical geometry");
        (allocation, arena)
    }

    fn run_continuation_pass(
        &self,
        start_round: usize,
        source: DrWindowContinuationSource<'_, ()>,
        destination: &DrWindowContinuationArena,
        destination_allocation: &DeviceAllocation<E4>,
        eq_scratch: &DrContinuationFactoredEqScratch,
        partials: &mut DeviceAllocation<E4>,
        claim_point: &DeviceAllocation<E4>,
    ) -> ContinuationPassObservation {
        let suffix_log = self.folding_steps - start_round;
        let eq = eq_scratch
            .view_for_pass(self.folding_steps, start_round)
            .expect("fixture continuation boundary is legal");
        let batch = build_dr_window_continuation_batch(
            &self.program,
            &self.projection,
            source,
            destination,
            eq,
        )
        .expect("fixture input-only continuation batch binds");
        let batch_base = upload(self.context, &[self.batch_base]);
        schedule_dim_reducing_batch_challenge_table_prelude(batch_base.as_ptr(), self.context)
            .unwrap();
        let launch = bind_dr_window_continuation_launch(
            batch,
            self.folding_steps,
            start_round,
            eq,
            DrWindowRuntimeScratch {
                partials: partials.as_mut_ptr(),
                partials_capacity: partials.len(),
            },
            claim_point.as_ptr(),
        )
        .expect("fixture continuation launch binds");
        assert_eq!(launch.selected_symbol(), DR_WINDOWED_CONT_KERNEL_SYMBOL);
        launch_dr_window_continuation(&launch, self.context).unwrap();

        let partials_len = TENSOR_CELLS * launch.row_tiles;
        let partial_values = download(self.context, &partials[..partials_len]);
        let published = download(self.context, &destination_allocation[..]);
        self.context.get_exec_stream().synchronize().unwrap();
        let mut tensor = [E4::ZERO; TENSOR_CELLS];
        for (index, value) in partial_values.into_iter().enumerate() {
            tensor[index % TENSOR_CELLS].add_assign(&value);
        }
        assert_eq!(launch.binding.log_rows as usize, suffix_log - 3);
        ContinuationPassObservation { tensor, published }
    }

    fn assert_published_columns(&self, expected: &BTreeMap<GKRAddress, Vec<E4>>, observed: &[E4]) {
        let stride = expected
            .values()
            .next()
            .expect("nonzero mask has a canonical source")
            .len();
        assert_eq!(
            observed.len(),
            self.projection.canonical_sources().len() * stride
        );
        for (publication_index, address) in self
            .projection
            .canonical_sources()
            .iter()
            .copied()
            .enumerate()
        {
            assert_eq!(
                &observed[publication_index * stride..(publication_index + 1) * stride],
                expected[&address].as_slice(),
                "canonical publication {publication_index} for {address:?}",
            );
        }
    }

    fn initial_claim(&self, tensor: &[E4; TENSOR_CELLS]) -> E4 {
        (0..8).fold(E4::ZERO, |mut claim, y| {
            let weight = (0..PEELED_COORDINATES).fold(E4::ONE, |mut weight, bit| {
                weight.mul_assign(&eq_weight((y >> bit) & 1, self.claim_point[bit]));
                weight
            });
            let index = 9 * (y & 1) + 3 * ((y >> 1) & 1) + ((y >> 2) & 1);
            let mut value = tensor[index];
            value.mul_assign(&weight);
            claim.add_assign(&value);
            claim
        })
    }

    fn suffix_eq_table(&self) -> Vec<E4> {
        self.eq_table_from(PEELED_COORDINATES)
    }

    fn eq_table_from(&self, coordinate_offset: usize) -> Vec<E4> {
        let suffix = &self.claim_point[coordinate_offset..];
        (0..1usize << suffix.len())
            .map(|row| {
                suffix
                    .iter()
                    .enumerate()
                    .fold(E4::ONE, |mut weight, (bit, coordinate)| {
                        weight.mul_assign(&eq_weight((row >> bit) & 1, *coordinate));
                        weight
                    })
            })
            .collect()
    }

    fn source_snapshot(&self) -> Vec<u8> {
        let input = download(
            self.context,
            raw_device_slice(
                self.input_backing.as_ptr().cast(),
                self.input_backing.len() * core::mem::size_of::<E4>(),
            ),
        );
        let output = download(
            self.context,
            raw_device_slice(
                self.output_backing.as_ptr().cast(),
                self.output_backing.len() * core::mem::size_of::<E4>(),
            ),
        );
        self.context.get_exec_stream().synchronize().unwrap();
        assert_eq!(
            input.len(),
            2 * DR_SLOT_COUNT * self.input_stride * core::mem::size_of::<E4>()
        );
        assert_eq!(
            output.len(),
            2 * DR_SLOT_COUNT * self.output_stride * core::mem::size_of::<E4>()
        );
        input.into_iter().chain(output).collect()
    }

    fn run_window_three_rounds(&self, arm: WindowTailArm) -> ThreeRoundStateObservation {
        let source_before = self.source_snapshot();
        let mut prepared = self.prepare();
        let r0_output = self.collect_partial_tensor(&prepared);
        let expected_r0_output = self.expected_tensor();

        let (active_eq_slot, active_eq_size) = resolve_active_eq_slot(
            &prepared.hook.r0_eq.eq_sizes,
            prepared.hook.r0_eq.eq_low.as_mut_ptr(),
        );
        assert_eq!(
            active_eq_size,
            (self.folding_steps - PEELED_COORDINATES) as u32
        );
        let eq_before = download(
            self.context,
            raw_device_slice(
                active_eq_slot.cast_const(),
                1usize << active_eq_size as usize,
            ),
        );
        self.context.get_exec_stream().synchronize().unwrap();
        assert_eq!(
            eq_before,
            self.eq_table_from(PEELED_COORDINATES),
            "window Eq is the fresh offset-3 reference",
        );

        let mut seed = upload(self.context, &self.tail_seed);
        let mut claim = upload(self.context, &[self.initial_claim(&expected_r0_output)]);
        let mut eq_prefactor = upload(self.context, &[E4::ONE]);
        let mut coefficients: DeviceAllocation<E4> = self
            .context
            .alloc(12, AllocationPlacement::BestFit)
            .unwrap();
        let state = WindowTailState {
            partials: prepared.scratch.as_ptr(),
            row_tiles: prepared.hook.r0_launch.row_tiles,
            reduced_tensor: prepared.hook.r0_launch.reduced_tensor,
            prev_claim_coords: prepared.claim_point.as_ptr(),
            seed: seed.as_mut_ptr(),
            claim: claim.as_mut_ptr(),
            eq_prefactor: eq_prefactor.as_mut_ptr(),
            coeffs_out: coefficients.as_mut_ptr(),
            challenges_out: prepared.claim_point.as_mut_ptr(),
            active_eq_slot_base: active_eq_slot,
            active_eq_size_before_fold: active_eq_size,
        };
        launch_window_tensor_round_tail(arm, &state, self.context).unwrap();

        let coefficients: [E4; 12] = download(self.context, &coefficients[..])
            .try_into()
            .expect("window tail writes twelve coefficients");
        let claim_point_after = download(self.context, &prepared.claim_point[..]);
        let seed: [u32; 8] = download(self.context, &seed[..])
            .try_into()
            .expect("transcript seed has eight words");
        let claim = download(self.context, &claim[..]);
        let eq_prefactor = download(self.context, &eq_prefactor[..]);
        let remaining_eq_values = download(
            self.context,
            raw_device_slice(
                active_eq_slot.cast_const(),
                1usize << (active_eq_size as usize - 1),
            ),
        );
        let source_after = self.source_snapshot();
        self.context.get_exec_stream().synchronize().unwrap();

        let challenges: [E4; PEELED_COORDINATES] = claim_point_after[..PEELED_COORDINATES]
            .try_into()
            .expect("window tail overwrites three claim-point slots");
        let mut sizes_after = prepared.hook.r0_eq.eq_sizes;
        record_active_eq_slot_fold(&mut sizes_after);
        assert_eq!(
            sizes_after,
            make_eq_sizes(self.folding_steps - PEELED_COORDINATES - 1),
            "window Eq drains exactly once",
        );
        assert_eq!(
            remaining_eq_values,
            self.eq_table_from(PEELED_COORDINATES + 1),
            "window remaining Eq function",
        );

        ThreeRoundStateObservation {
            r0_output,
            coefficients,
            challenges,
            seed,
            claim: claim[0],
            eq_prefactor: eq_prefactor[0],
            claim_point_slots: challenges,
            source_before,
            source_after,
            remaining_eq_values,
        }
    }

    /// Explicitly forced whole-layer legacy diagnostic comparator. This is a
    /// test control only; it is not a production fallback or selection path.
    fn run_legacy_three_round_diagnostic(&self) -> ThreeRoundStateObservation {
        assert_eq!(self.folding_steps, 9, "fixture pins one low Eq group");
        let source_before = self.source_snapshot();
        let folding_addresses = self.projection.canonical_sources();
        assert!(folding_addresses.windows(2).all(|pair| pair[0] < pair[1]));

        let claim_point = upload(self.context, &self.claim_point);
        let mut eq_low: DeviceAllocation<E4> = self
            .context
            .alloc(GKR_EQ_GROUP_TABLE_LEN, AllocationPlacement::BestFit)
            .unwrap();
        launch_build_eq_high_and_low_groups_from_point(
            claim_point.as_ptr(),
            1,
            self.folding_steps - 1,
            get_eq_high_constant_device_ptr(),
            eq_low.as_mut_ptr(),
            self.context,
        )
        .unwrap();
        let mut eq_sizes = make_eq_sizes(self.folding_steps - 1);
        assert_eq!(
            eq_sizes,
            GkrEqSizes {
                high: [0, 0],
                low: 8
            }
        );

        let batch_base = upload(self.context, &[self.batch_base]);
        schedule_dim_reducing_batch_challenge_table_prelude(batch_base.as_ptr(), self.context)
            .unwrap();
        let claim_point_symbol = get_dim_reducing_layer_claim_point_device_ptr();
        let symbol_initial = vec![E4::ZERO; MAX_DIM_REDUCING_LAYER_CLAIM_POINT_LEN];
        // SAFETY: the CUDA symbol has exactly the pinned maximum claim-point
        // length, and remains live for the full diagnostic sequence.
        let symbol_view =
            unsafe { DeviceSlice::from_raw_parts_mut(claim_point_symbol, symbol_initial.len()) };
        memory_copy_async(symbol_view, &symbol_initial, self.context.get_exec_stream()).unwrap();

        let mut seed = upload(self.context, &self.tail_seed);
        let r0_output = self.expected_tensor();
        let mut claim = upload(self.context, &[self.initial_claim(&r0_output)]);
        let mut eq_prefactor = upload(self.context, &[E4::ONE]);
        let mut coefficients: DeviceAllocation<E4> = self
            .context
            .alloc(12, AllocationPlacement::BestFit)
            .unwrap();
        let max_acc_size = 1usize << (self.folding_steps - 1);
        let mut contributions: DeviceAllocation<E4> = self
            .context
            .alloc(2 * max_acc_size, AllocationPlacement::BestFit)
            .unwrap();
        let arena_poly_count = folding_addresses.len();
        let first_arena: DeviceAllocation<E4> = self
            .context
            .alloc(
                arena_poly_count * (1usize << self.folding_steps),
                AllocationPlacement::BestFit,
            )
            .unwrap();
        let second_arena: DeviceAllocation<E4> = self
            .context
            .alloc(
                arena_poly_count * (1usize << (self.folding_steps - 1)),
                AllocationPlacement::BestFit,
            )
            .unwrap();

        for step in 0..PEELED_COORDINATES {
            let acc_size = 1usize << (self.folding_steps - 1 - step);
            let mut batch: GpuGKRDimensionReducingBatch<E4> = match step {
                0 => build_round0_batch_compact(&self.legacy_slots, &self.storage),
                1 => build_round1_batch_compact_for_arena(
                    &self.legacy_slots,
                    &self.storage,
                    folding_addresses,
                    FoldingArenaBinding::new(
                        first_arena.as_ptr().cast(),
                        self.folding_steps as u32,
                    ),
                ),
                2 => build_continuation_batch_compact_for_arenas(
                    &self.legacy_slots,
                    &self.storage,
                    folding_addresses,
                    FoldingArenaBinding::new(
                        first_arena.as_ptr().cast(),
                        self.folding_steps as u32,
                    ),
                    FoldingArenaBinding::new(
                        second_arena.as_ptr().cast(),
                        (self.folding_steps - 1) as u32,
                    ),
                ),
                _ => unreachable!("the diagnostic compares exactly three rounds"),
            };
            batch.eq_low = eq_low.as_ptr();
            batch.eq_sizes = eq_sizes;
            batch.contributions = contributions.as_mut_ptr();
            if step == 0 {
                launch_dim_reducing_round0_batched_compact(&batch, acc_size, self.context).unwrap();
            } else {
                launch_dim_reducing_continuation_batched_compact(
                    &batch,
                    acc_size,
                    step,
                    self.context,
                )
                .unwrap();
            }

            let (active_eq_slot, active_eq_size) =
                resolve_active_eq_slot(&eq_sizes, eq_low.as_mut_ptr());
            // SAFETY: coefficient and claim-point outputs each address their
            // pinned round-major allocation/symbol slots.
            let coeffs_out = unsafe { coefficients.as_mut_ptr().add(4 * step) };
            let challenge_out = unsafe { claim_point_symbol.add(step) };
            let prev_claim_coord = unsafe { claim_point.as_ptr().add(step) };
            launch_backward_dual_finalize_from_acc(
                contributions.as_ptr(),
                acc_size,
                prev_claim_coord,
                seed.as_mut_ptr(),
                claim.as_mut_ptr(),
                eq_prefactor.as_mut_ptr(),
                coeffs_out,
                challenge_out,
                active_eq_slot,
                active_eq_size,
                self.context,
            )
            .unwrap();
            record_active_eq_slot_fold(&mut eq_sizes);
        }

        assert_eq!(
            eq_sizes,
            make_eq_sizes(self.folding_steps - 4),
            "legacy diagnostic Eq drains exactly three times",
        );
        let (remaining_eq_slot, remaining_eq_size) =
            resolve_active_eq_slot(&eq_sizes, eq_low.as_mut_ptr());
        let coefficients: [E4; 12] = download(self.context, &coefficients[..])
            .try_into()
            .expect("legacy diagnostic writes twelve coefficients");
        let challenges: [E4; PEELED_COORDINATES] = download(
            self.context,
            raw_device_slice(claim_point_symbol.cast_const(), PEELED_COORDINATES),
        )
        .try_into()
        .expect("legacy diagnostic writes three claim-point slots");
        let seed: [u32; 8] = download(self.context, &seed[..])
            .try_into()
            .expect("transcript seed has eight words");
        let claim = download(self.context, &claim[..]);
        let eq_prefactor = download(self.context, &eq_prefactor[..]);
        let remaining_eq_values = download(
            self.context,
            raw_device_slice(
                remaining_eq_slot.cast_const(),
                1usize << remaining_eq_size as usize,
            ),
        );
        let source_after = self.source_snapshot();
        self.context.get_exec_stream().synchronize().unwrap();
        assert_eq!(remaining_eq_size, (self.folding_steps - 4) as u32);
        assert_eq!(
            remaining_eq_values,
            self.eq_table_from(PEELED_COORDINATES + 1),
            "legacy remaining Eq function",
        );

        ThreeRoundStateObservation {
            r0_output,
            coefficients,
            challenges,
            seed,
            claim: claim[0],
            eq_prefactor: eq_prefactor[0],
            claim_point_slots: challenges,
            source_before,
            source_after,
            remaining_eq_values,
        }
    }

    fn run_tail(&self, arm: WindowTailArm) {
        let mut prepared = self.prepare();
        let expected_tensor = self.expected_tensor();
        let partials_len = TENSOR_CELLS * prepared.hook.r0_launch.row_tiles;
        let partials = download(self.context, &prepared.scratch[..partials_len]);
        let (active_eq_slot, active_eq_size) = resolve_active_eq_slot(
            &prepared.hook.r0_eq.eq_sizes,
            prepared.hook.r0_eq.eq_low.as_mut_ptr(),
        );
        assert_eq!(
            active_eq_size as usize,
            self.folding_steps - PEELED_COORDINATES
        );
        let active_eq_len = 1usize << active_eq_size;
        let eq_before = download(
            self.context,
            raw_device_slice(active_eq_slot.cast_const(), active_eq_len),
        );
        self.context.get_exec_stream().synchronize().unwrap();

        let mut gpu_tensor = [E4::ZERO; TENSOR_CELLS];
        for (index, value) in partials.into_iter().enumerate() {
            gpu_tensor[index % TENSOR_CELLS].add_assign(&value);
        }
        compare_dr_tensors(&expected_tensor, &gpu_tensor)
            .unwrap_or_else(|error| panic!("{arm:?} producer tensor mismatch: {error:?}"));
        assert_eq!(
            eq_before,
            self.suffix_eq_table(),
            "{arm:?} offset-3 Eq table"
        );

        let mut seed = upload(self.context, &self.tail_seed);
        let initial_claim = self.initial_claim(&expected_tensor);
        let mut claim = upload(self.context, &[initial_claim]);
        let mut eq_prefactor = upload(self.context, &[E4::ONE]);
        let mut coefficients: DeviceAllocation<E4> = self
            .context
            .alloc(12, AllocationPlacement::BestFit)
            .unwrap();
        let mut challenges: DeviceAllocation<E4> = self
            .context
            .alloc(PEELED_COORDINATES, AllocationPlacement::BestFit)
            .unwrap();
        let state = WindowTailState {
            partials: prepared.scratch.as_ptr(),
            row_tiles: prepared.hook.r0_launch.row_tiles,
            reduced_tensor: prepared.hook.r0_launch.reduced_tensor,
            prev_claim_coords: prepared.claim_point.as_ptr(),
            seed: seed.as_mut_ptr(),
            claim: claim.as_mut_ptr(),
            eq_prefactor: eq_prefactor.as_mut_ptr(),
            coeffs_out: coefficients.as_mut_ptr(),
            challenges_out: challenges.as_mut_ptr(),
            active_eq_slot_base: active_eq_slot,
            active_eq_size_before_fold: active_eq_size,
        };
        launch_window_tensor_round_tail(arm, &state, self.context).unwrap();

        let gpu_coefficients = download(self.context, &coefficients[..]);
        let gpu_challenges = download(self.context, &challenges[..]);
        let gpu_seed = download(self.context, &seed[..]);
        let gpu_claim = download(self.context, &claim[..]);
        let gpu_eq_prefactor = download(self.context, &eq_prefactor[..]);
        let folded_eq_len = active_eq_len / 2;
        let folded_eq = download(
            self.context,
            raw_device_slice(active_eq_slot.cast_const(), folded_eq_len),
        );
        self.context.get_exec_stream().synchronize().unwrap();

        let mut expected_seed = self.tail_seed;
        let mut expected_claim = initial_claim;
        let mut expected_eq_prefactor = E4::ONE;
        let rho: [E4; PEELED_COORDINATES] = core::array::from_fn(|index| self.claim_point[index]);
        let (expected_coefficients, expected_challenges) = tensor_round_tail_reference(
            expected_tensor,
            &rho,
            &mut expected_seed,
            &mut expected_claim,
            &mut expected_eq_prefactor,
        );
        assert_eq!(
            gpu_coefficients.as_slice(),
            expected_coefficients.as_slice()
        );
        assert_eq!(gpu_challenges.as_slice(), expected_challenges.as_slice());
        assert_eq!(gpu_seed.as_slice(), expected_seed.as_slice());
        assert_eq!(gpu_claim, vec![expected_claim]);
        assert_eq!(gpu_eq_prefactor, vec![expected_eq_prefactor]);
        let expected_folded = eq_before
            .chunks_exact(2)
            .map(|pair| add(pair[0], pair[1]))
            .collect::<Vec<_>>();
        assert_eq!(folded_eq, expected_folded, "{arm:?} one active Eq fold");
    }

    fn perturb_first_materialized_output(&self) {
        let output_id = self.program.slots()[0].source_ids()[2];
        let output = self.program.sources()[usize::from(output_id)];
        let poly_index = match output {
            GKRAddress::InnerLayer { layer, offset } => {
                assert_eq!(layer, OUTPUT_LAYER);
                offset
            }
            _ => panic!("fixture outputs are inner-layer addresses"),
        };
        let mut value = self.columns[&output][0];
        value.add_assign(&E4::ONE);
        // SAFETY: the output backing owns ten `output_stride`-sized columns;
        // this points at the selected column's first live E4.
        let destination = unsafe {
            DeviceSlice::from_raw_parts_mut(
                self.output_backing
                    .as_ptr()
                    .cast_mut()
                    .add(poly_index * self.output_stride),
                1,
            )
        };
        let value = [value];
        memory_copy_async(destination, &value, self.context.get_exec_stream()).unwrap();
        self.context.get_exec_stream().synchronize().unwrap();
    }
}

#[test]
#[ignore = "requires CUDA; build/list outside the lock and execute through .agents/bin/with_gpu_lock.sh"]
fn gpu_dr_window_r0_tensor_matches_cpu() {
    let context = make_test_context(256, 64);
    let masks = OBSERVED_MASKS
        .into_iter()
        .chain([UNOBSERVED_WELL_FORMED_MASK])
        .collect::<Vec<_>>();
    assert_eq!(masks, vec![0x01, 0x0d, 0x0f, 0x1f, 0x02]);
    let mut slot_instances = [0usize; DR_SLOT_COUNT];
    let mut row_tiles_seen = BTreeSet::new();
    let mut symbols = BTreeSet::new();

    for mask in masks {
        for instance in 0..TENSOR_INSTANCES_PER_MASK {
            let folding_steps = if instance % 2 == 0 { 4 } else { 9 };
            let fixture = DrGpuFixture::new(
                &context,
                mask,
                folding_steps,
                0xd120_0000_0000_0000 ^ ((mask as u64) << 32) ^ instance as u64,
            );
            let expected = fixture.expected_tensor();
            let (observed, symbol, row_tiles) = fixture.run_producer();
            compare_dr_tensors(&expected, &observed).unwrap_or_else(|error| {
                panic!(
                    "mask {mask:#04x} instance {instance} f={folding_steps} tensor mismatch: {error:?}"
                )
            });
            assert_eq!(symbol, DR_WINDOWED_R0_KERNEL_SYMBOL);
            symbols.insert(symbol);
            row_tiles_seen.insert(row_tiles);
            for (slot, count) in slot_instances.iter_mut().enumerate() {
                *count += usize::from(mask & (1 << slot) != 0);
            }
        }
    }

    assert_eq!(
        slot_instances,
        [128, 96, 96, 96, 32],
        "both pairwise and all three lookup chunks have at least 32 instances",
    );
    assert_eq!(row_tiles_seen, BTreeSet::from([1, 2]));
    assert_eq!(symbols, BTreeSet::from([DR_WINDOWED_R0_KERNEL_SYMBOL]));

    let perturbation = DrGpuFixture::new(&context, 0x1f, 4, 0xd120_ffff_0000_0001);
    let expected = perturbation.expected_tensor();
    let (baseline, _, _) = perturbation.run_producer();
    compare_dr_tensors(&expected, &baseline).expect("unperturbed production tensor");
    perturbation.perturb_first_materialized_output();
    let (mutated, _, _) = perturbation.run_producer();
    assert!(matches!(
        compare_dr_tensors(&expected, &mutated),
        Err(DrTensorMismatch::Cell { .. })
    ));
}

#[test]
#[ignore = "requires CUDA; build/list outside the lock and execute through .agents/bin/with_gpu_lock.sh"]
fn gpu_dr_window_r0_tail_arms_match_cpu() {
    let context = make_test_context(256, 64);
    let cases = [(0x1f, 4), (UNOBSERVED_WELL_FORMED_MASK, 9)];
    for (arm_index, arm) in [WindowTailArm::Absorbed, WindowTailArm::Split]
        .into_iter()
        .enumerate()
    {
        for (case_index, (mask, folding_steps)) in cases.into_iter().enumerate() {
            let fixture = DrGpuFixture::new(
                &context,
                mask,
                folding_steps,
                0xd121_0000_0000_0000 ^ ((arm_index as u64) << 40) ^ ((case_index as u64) << 24),
            );
            fixture.run_tail(arm);
        }
    }
}

#[test]
#[ignore = "requires CUDA; build/list outside the lock and execute through .agents/bin/with_gpu_lock.sh"]
fn gpu_dr_window_r0_three_round_state_matches_legacy() {
    let context = make_test_context(256, 64);
    const SEED: u64 = 0xd122_0000_0000_0001;
    let legacy_fixture = DrGpuFixture::new(&context, 0x1f, 9, SEED);
    let legacy = legacy_fixture.run_legacy_three_round_diagnostic();

    for arm in [WindowTailArm::Absorbed, WindowTailArm::Split] {
        let window_fixture = DrGpuFixture::new(&context, 0x1f, 9, SEED);
        assert_eq!(legacy_fixture.claim_point, window_fixture.claim_point);
        assert_eq!(legacy_fixture.batch_base, window_fixture.batch_base);
        assert_eq!(legacy_fixture.tail_seed, window_fixture.tail_seed);
        let window = window_fixture.run_window_three_rounds(arm);
        compare_three_round_states(&legacy, &window)
            .unwrap_or_else(|error| panic!("{arm:?} three-round state mismatch: {error:?}"));
    }

    let perturbed_fixture = DrGpuFixture::new(&context, 0x1f, 9, SEED);
    perturbed_fixture.perturb_first_materialized_output();
    let perturbed = perturbed_fixture.run_window_three_rounds(WindowTailArm::Split);
    assert!(matches!(
        compare_three_round_states(&legacy, &perturbed),
        Err(ThreeRoundStateMismatch::R0Output { .. })
    ));
}

fn active_factored_eq_physical_slot(sizes: GkrEqSizes) -> (usize, u32) {
    if sizes.low > 0 {
        (2, sizes.low)
    } else if sizes.high[1] > 0 {
        (1, sizes.high[1])
    } else {
        assert!(sizes.high[0] > 0);
        (0, sizes.high[0])
    }
}

fn active_factored_eq_logical_group(challenge_count: usize) -> usize {
    eq_group_count(challenge_count)
        .checked_sub(1)
        .expect("a continuation Eq suffix always has at least one logical group")
}

fn factored_eq_group_reference(
    claim_point: &[E4],
    challenge_offset: usize,
    challenge_count: usize,
    group_index: usize,
) -> Vec<E4> {
    let group_start = group_index * 8;
    let group_size = (challenge_count - group_start).min(8);
    (0..1usize << group_size)
        .map(|local_index| {
            (0..group_size).fold(E4::ONE, |mut product, variable| {
                let coordinate =
                    claim_point[challenge_offset + challenge_count - 1 - group_start - variable];
                let bit = (local_index >> (group_size - 1 - variable)) & 1;
                product.mul_assign(&eq_weight(bit, coordinate));
                product
            })
        })
        .collect()
}

#[test]
fn cpu_dr_window_continuation_factored_eq_reference_maps_logical_groups() {
    let mut rng = StdRng::seed_from_u64(0xd331_0000_0000_0001);
    let claim_point = (0..32).map(|_| random_e4(&mut rng)).collect::<Vec<_>>();
    let challenge_offset = 4usize;
    let mut logical_group_reachability = [0usize; 3];
    let mut physical_low_mutations_rejected = 0usize;

    for challenge_count in 1usize..=24 {
        let sizes = make_eq_sizes(challenge_count);
        let logical_group = (challenge_count - 1) / 8;
        let logical_group_start = logical_group * 8;
        let logical_group_size = (challenge_count - logical_group_start).min(8);
        let (physical_slot, mapped_size) = active_factored_eq_physical_slot(sizes);
        let mapped_group = active_factored_eq_logical_group(challenge_count);

        assert_eq!(sizes.low as usize, logical_group_size);
        assert_eq!(physical_slot, 2);
        assert_eq!(mapped_group, logical_group);
        assert_eq!(mapped_size as usize, logical_group_size);

        let observed = factored_eq_group_reference(
            &claim_point,
            challenge_offset,
            challenge_count,
            mapped_group,
        );
        let expected = (0..1usize << logical_group_size)
            .map(|local_index| {
                (0..logical_group_size).fold(E4::ONE, |mut product, local_variable| {
                    let logical_variable = logical_group_start + local_variable;
                    let coordinate =
                        claim_point[challenge_offset + challenge_count - 1 - logical_variable];
                    let bit = (local_index >> (logical_group_size - 1 - local_variable)) & 1;
                    product.mul_assign(&eq_weight(bit, coordinate));
                    product
                })
            })
            .collect::<Vec<_>>();
        assert_eq!(observed, expected);

        // Historical mutation: physical slot 2 (`low`) was passed as logical
        // builder group 2. It must be rejected for one- and two-group Eq
        // builds, where the last logical group is 0 or 1 respectively.
        if logical_group < 2 {
            assert_ne!(
                physical_slot, mapped_group,
                "physical-low-as-logical-group mutation survived count={challenge_count}",
            );
            physical_low_mutations_rejected += 1;
        }
        logical_group_reachability[logical_group] += 1;
    }

    assert_eq!(logical_group_reachability, [8, 8, 8]);
    assert_eq!(physical_low_mutations_rejected, 16);
}

#[test]
#[ignore = "requires CUDA; execute only through an independently approved locked D2 packet"]
fn dr_window_continuation_first_raw_matches_legacy() {
    let context = make_test_context(256, 64);
    let fixture = DrGpuFixture::new(&context, 0x1f, 10, 0xd220_0000_0000_0001);
    let (destination_allocation, destination) = fixture.continuation_arena(3);
    let eq_scratch = continuation_eq_scratch(&context, fixture.folding_steps);
    let mut partials: DeviceAllocation<E4> = context
        .alloc(dr_window_partials_len(7), AllocationPlacement::BestFit)
        .unwrap();
    let claim_point = upload(&context, &fixture.claim_point);
    let observed = fixture.run_continuation_pass(
        3,
        DrWindowContinuationSource::Storage(&fixture.storage),
        &destination,
        destination_allocation.as_ref(),
        &eq_scratch,
        &mut partials,
        &claim_point,
    );
    let folded = fixture.folded_continuation_columns(&fixture.columns, 3);
    fixture.assert_published_columns(&folded, &observed.published);
    let expected = dr_continuation_tensor_reference(
        &fixture.oracle_program,
        &folded,
        fixture.batch_base,
        &fixture.claim_point[6..],
    )
    .unwrap();
    compare_dr_tensors(&expected, &observed.tensor).unwrap();
}

#[test]
#[ignore = "requires CUDA; execute only through an independently approved locked D2 packet"]
fn dr_window_continuation_later_arena_matches_legacy() {
    let context = make_test_context(256, 64);
    let fixture = DrGpuFixture::new(&context, 0x1f, 10, 0xd221_0000_0000_0001);
    let (first_allocation, first_arena) = fixture.continuation_arena(3);
    let (second_allocation, second_arena) = fixture.continuation_arena(6);
    let eq_scratch = continuation_eq_scratch(&context, fixture.folding_steps);
    let mut partials: DeviceAllocation<E4> = context
        .alloc(dr_window_partials_len(7), AllocationPlacement::BestFit)
        .unwrap();
    let claim_point = upload(&context, &fixture.claim_point);
    let first = fixture.run_continuation_pass(
        3,
        DrWindowContinuationSource::Storage(&fixture.storage),
        &first_arena,
        first_allocation.as_ref(),
        &eq_scratch,
        &mut partials,
        &claim_point,
    );
    let folded_once = fixture.folded_continuation_columns(&fixture.columns, 3);
    fixture.assert_published_columns(&folded_once, &first.published);

    let second = fixture.run_continuation_pass(
        6,
        DrWindowContinuationSource::Arena(&first_arena),
        &second_arena,
        second_allocation.as_ref(),
        &eq_scratch,
        &mut partials,
        &claim_point,
    );
    let folded_twice = fixture.folded_continuation_columns(&folded_once, 6);
    fixture.assert_published_columns(&folded_twice, &second.published);
    let expected = dr_continuation_tensor_reference(
        &fixture.oracle_program,
        &folded_twice,
        fixture.batch_base,
        &fixture.claim_point[9..],
    )
    .unwrap();
    compare_dr_tensors(&expected, &second.tensor).unwrap();
}

#[test]
#[ignore = "requires CUDA; execute only through an independently approved locked D2 packet"]
fn dr_window_continuation_eq_is_independent() {
    let context = make_test_context(256, 64);
    let fixture = DrGpuFixture::new(&context, 0x1f, 10, 0xd222_0000_0000_0001);
    let claim_point = upload(&context, &fixture.claim_point);
    let r0_eq = DrWindowPassEqState::allocate(&context, 3, fixture.folding_steps - 3).unwrap();
    launch_build_eq_high_and_low_groups_from_point(
        claim_point.as_ptr(),
        3,
        fixture.folding_steps - 3,
        get_eq_high_constant_device_ptr(),
        r0_eq.eq_low.as_ptr().cast_mut(),
        &context,
    )
    .unwrap();
    let constant_before = download(
        &context,
        raw_device_slice(
            get_eq_high_constant_device_ptr(),
            2 * GKR_EQ_GROUP_TABLE_LEN,
        ),
    );
    let r0_low_before = download(&context, &r0_eq.eq_low[..]);
    context.get_exec_stream().synchronize().unwrap();

    let (destination_allocation, destination) = fixture.continuation_arena(3);
    let eq_scratch = continuation_eq_scratch(&context, fixture.folding_steps);
    let mut partials: DeviceAllocation<E4> = context
        .alloc(dr_window_partials_len(7), AllocationPlacement::BestFit)
        .unwrap();
    let _ = fixture.run_continuation_pass(
        3,
        DrWindowContinuationSource::Storage(&fixture.storage),
        &destination,
        destination_allocation.as_ref(),
        &eq_scratch,
        &mut partials,
        &claim_point,
    );
    let constant_after = download(
        &context,
        raw_device_slice(
            get_eq_high_constant_device_ptr(),
            2 * GKR_EQ_GROUP_TABLE_LEN,
        ),
    );
    let r0_low_after = download(&context, &r0_eq.eq_low[..]);
    context.get_exec_stream().synchronize().unwrap();
    assert_eq!(constant_after, constant_before);
    assert_eq!(r0_low_after, r0_low_before);
}

#[test]
#[ignore = "requires CUDA; execute only through an independently approved locked D2 packet"]
fn dr_window_continuation_global_eq_builder_matches_reference() {
    let context = make_test_context(64, 16);
    let folding_steps = 23;
    let start_round = 3;
    let challenge_offset = start_round + 3;
    let challenge_count = folding_steps - challenge_offset;
    let mut rng = StdRng::seed_from_u64(0xd223_0000_0000_0001);
    let claim_host = (0..folding_steps)
        .map(|_| random_e4(&mut rng))
        .collect::<Vec<_>>();
    let claim_point = upload(&context, &claim_host);
    let eq_scratch = continuation_eq_scratch(&context, folding_steps);
    let view = eq_scratch
        .view_for_pass(folding_steps, start_round)
        .unwrap();
    launch_build_eq_independent_groups_from_point(
        claim_point.as_ptr(),
        challenge_offset,
        challenge_count,
        view.high_0,
        view.high_1,
        view.low,
        &context,
    )
    .unwrap();
    let high_0 = download(
        &context,
        raw_device_slice(view.high_0, GKR_EQ_GROUP_TABLE_LEN),
    );
    let high_1 = download(
        &context,
        raw_device_slice(view.high_1, GKR_EQ_GROUP_TABLE_LEN),
    );
    let low = download(&context, raw_device_slice(view.low, GKR_EQ_GROUP_TABLE_LEN));
    context.get_exec_stream().synchronize().unwrap();

    assert_eq!(view.sizes, make_eq_sizes(challenge_count));
    assert_eq!(
        &high_0[..1usize << view.sizes.high[0]],
        factored_eq_group_reference(&claim_host, challenge_offset, challenge_count, 0),
    );
    assert_eq!(
        &high_1[..1usize << view.sizes.high[1]],
        factored_eq_group_reference(&claim_host, challenge_offset, challenge_count, 1),
    );
    assert_eq!(
        &low[..1usize << view.sizes.low],
        factored_eq_group_reference(&claim_host, challenge_offset, challenge_count, 2),
    );
}

#[test]
#[ignore = "requires CUDA; execute only through the independently approved D3 GPU lock packet"]
fn dr_window_continuation_chain_matches_legacy() {
    let context = make_test_context(256, 64);
    let masks = OBSERVED_MASKS
        .into_iter()
        .chain([UNOBSERVED_WELL_FORMED_MASK]);

    for (case_index, mask) in masks.enumerate() {
        let fixture = DrGpuFixture::new(
            &context,
            mask,
            12,
            0xd330_0000_0000_0001 ^ ((case_index as u64) << 40) ^ u64::from(mask),
        );
        let source_before = fixture.source_snapshot();
        let expected_r0_tensor = fixture.expected_tensor();
        let mut prepared = fixture.prepare();
        let claim_point_base = prepared.claim_point.as_ptr();
        bind_dr_window_continuations(
            &mut prepared.hook,
            &fixture.storage,
            claim_point_base,
            &context,
        )
        .expect("D3 binds the landed W'=2 prefix");
        assert_eq!(prepared.hook.continuation_launches.len(), 2);
        assert_eq!(
            prepared
                .hook
                .continuation_launches
                .iter()
                .map(|pass| pass.launch.row_tiles)
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([1, 2]),
        );
        assert!(prepared.hook.continuation_eq.is_some());
        assert!(prepared.hook.continuation_arenas.even.is_some());
        assert!(prepared.hook.continuation_arenas.odd.is_some());
        assert_eq!(prepared.hook.continuation_keepalives.len(), 2);
        let poly_count = fixture.projection.canonical_sources().len();
        let even = prepared.hook.continuation_arenas.even.as_ref().unwrap();
        let odd = prepared.hook.continuation_arenas.odd.as_ref().unwrap();
        assert_eq!(even.log2_stride(), fixture.folding_steps as u32 - 2);
        assert_eq!(odd.log2_stride(), fixture.folding_steps as u32 - 5);
        assert_eq!(even.capacity(), poly_count << (fixture.folding_steps - 2));
        assert_eq!(odd.capacity(), poly_count << (fixture.folding_steps - 5));

        let entry_round = prepared.hook.megakernel_entry_round;
        let mut seed = upload(&context, &fixture.tail_seed);
        let initial_claim = fixture.initial_claim(&expected_r0_tensor);
        let mut claim = upload(&context, &[initial_claim]);
        let mut eq_prefactor = upload(&context, &[E4::ONE]);
        let mut coefficients: DeviceAllocation<E4> = context
            .alloc(4 * entry_round, AllocationPlacement::BestFit)
            .unwrap();

        let (r0_active_slot, r0_active_size) = resolve_active_eq_slot(
            &prepared.hook.r0_eq.eq_sizes,
            prepared.hook.r0_eq.eq_low.as_mut_ptr(),
        );
        let r0_tail = WindowTailState {
            partials: prepared.scratch.as_ptr(),
            row_tiles: prepared.hook.r0_launch.row_tiles,
            reduced_tensor: prepared.hook.r0_launch.reduced_tensor,
            prev_claim_coords: prepared.claim_point.as_ptr(),
            seed: seed.as_mut_ptr(),
            claim: claim.as_mut_ptr(),
            eq_prefactor: eq_prefactor.as_mut_ptr(),
            coeffs_out: coefficients.as_mut_ptr(),
            challenges_out: prepared.claim_point.as_mut_ptr(),
            active_eq_slot_base: r0_active_slot,
            active_eq_size_before_fold: r0_active_size,
        };
        launch_window_tensor_round_tail(WindowTailArm::Split, &r0_tail, &context).unwrap();
        context.get_exec_stream().synchronize().unwrap();

        let constant_before = download(
            &context,
            raw_device_slice(
                get_eq_high_constant_device_ptr(),
                2 * GKR_EQ_GROUP_TABLE_LEN,
            ),
        );
        let r0_low_before = download(&context, &prepared.hook.r0_eq.eq_low[..]);
        context.get_exec_stream().synchronize().unwrap();

        let mut expected_seed = fixture.tail_seed;
        let mut expected_claim = initial_claim;
        let mut expected_eq_prefactor = E4::ONE;
        let mut expected_claim_point = fixture.claim_point.clone();
        let r0_rho: [E4; 3] = expected_claim_point[..3].try_into().unwrap();
        let (r0_coefficients, r0_challenges) = tensor_round_tail_reference(
            expected_r0_tensor,
            &r0_rho,
            &mut expected_seed,
            &mut expected_claim,
            &mut expected_eq_prefactor,
        );
        let mut expected_coefficients = vec![E4::ZERO; 4 * entry_round];
        expected_coefficients[..12].copy_from_slice(&r0_coefficients);
        expected_claim_point[..3].copy_from_slice(&r0_challenges);

        let claim_point_ptr = prepared.claim_point.as_mut_ptr();
        let coeffs_ptr = coefficients.as_mut_ptr();
        let seed_ptr = seed.as_mut_ptr();
        let claim_ptr = claim.as_mut_ptr();
        let eq_prefactor_ptr = eq_prefactor.as_mut_ptr();
        let mut expected_columns = fixture.columns.clone();
        let mut expected_published = Vec::new();
        let mut observed_published = Vec::new();
        let mut expected_tensors = Vec::new();
        let mut observed_tensors = Vec::new();
        let mut expected_eq_entries = Vec::new();
        let mut expected_eq_boundaries = Vec::new();
        let mut expected_eq_entry_active_sizes = Vec::new();
        let mut expected_eq_entry_active_values = Vec::new();
        let mut expected_eq_boundary_active_sizes = Vec::new();
        let mut expected_eq_boundary_active_values = Vec::new();

        let eq_snapshots = launch_dr_window_continuation_chain_for_test(
            &prepared.hook,
            WindowTailArm::Split,
            claim_point_ptr,
            coeffs_ptr,
            seed_ptr,
            claim_ptr,
            eq_prefactor_ptr,
            &context,
            |pass| {
                let start_round = pass.geometry.start_round;
                let folding_challenges: [E4; 3] = expected_claim_point
                    [start_round - 3..start_round]
                    .try_into()
                    .unwrap();
                expected_columns = fixture
                    .projection
                    .canonical_sources()
                    .iter()
                    .copied()
                    .map(|address| {
                        let folded = fold_dr_continuation_depth3(
                            &expected_columns[&address],
                            folding_challenges,
                        )
                        .unwrap();
                        (address, folded)
                    })
                    .collect();
                let expected_tensor = dr_continuation_tensor_reference(
                    &fixture.oracle_program,
                    &expected_columns,
                    fixture.batch_base,
                    &expected_claim_point[start_round + 3..fixture.folding_steps],
                )
                .unwrap();

                let partial_values = download(
                    &context,
                    raw_device_slice(
                        pass.launch.binding.partials,
                        TENSOR_CELLS * pass.launch.row_tiles,
                    ),
                );
                let first_slot = pass.launch.binding.batch.enabled_mask.trailing_zeros() as usize;
                let destination_record = pass.launch.binding.batch.slots[first_slot].io[0];
                let destination_slot = usize::from((destination_record.cache >> 11) & 0x0f);
                assert_eq!(
                    pass.launch.binding.batch.tables.log2_stride[destination_slot],
                    pass.geometry.log2_stride,
                );
                let destination_base =
                    pass.launch.binding.batch.tables.bases[destination_slot].cast::<E4>();
                let published_len =
                    fixture.projection.canonical_sources().len() * pass.geometry.per_poly_len;
                let published =
                    download(&context, raw_device_slice(destination_base, published_len));

                let rho: [E4; 3] = expected_claim_point[start_round..start_round + 3]
                    .try_into()
                    .unwrap();
                let (tail_coefficients, tail_challenges) = tensor_round_tail_reference(
                    expected_tensor,
                    &rho,
                    &mut expected_seed,
                    &mut expected_claim,
                    &mut expected_eq_prefactor,
                );
                expected_coefficients[4 * start_round..4 * (start_round + 3)]
                    .copy_from_slice(&tail_coefficients);
                expected_claim_point[start_round..start_round + 3]
                    .copy_from_slice(&tail_challenges);

                let observed_coefficients = download(
                    &context,
                    raw_device_slice(coeffs_ptr.cast_const(), 4 * (start_round + 3)),
                );
                let observed_claim_point = download(
                    &context,
                    raw_device_slice(claim_point_ptr.cast_const(), fixture.folding_steps),
                );
                let observed_seed = download(&context, raw_device_slice(seed_ptr.cast_const(), 8));
                let observed_claim =
                    download(&context, raw_device_slice(claim_ptr.cast_const(), 1));
                let observed_eq_prefactor =
                    download(&context, raw_device_slice(eq_prefactor_ptr.cast_const(), 1));
                context.get_exec_stream().synchronize().unwrap();

                let mut observed_tensor = [E4::ZERO; TENSOR_CELLS];
                for (index, value) in partial_values.into_iter().enumerate() {
                    observed_tensor[index % TENSOR_CELLS].add_assign(&value);
                }
                compare_dr_tensors(&expected_tensor, &observed_tensor).unwrap();
                let expected_publication = fixture
                    .projection
                    .canonical_sources()
                    .iter()
                    .flat_map(|address| expected_columns[address].iter().copied())
                    .collect::<Vec<_>>();
                assert_eq!(published, expected_publication);
                assert_eq!(
                    observed_coefficients,
                    expected_coefficients[..4 * (start_round + 3)],
                );
                assert_eq!(observed_claim_point, expected_claim_point);
                assert_eq!(observed_seed, expected_seed);
                assert_eq!(observed_claim, vec![expected_claim]);
                assert_eq!(observed_eq_prefactor, vec![expected_eq_prefactor]);

                let expected_entry = make_eq_sizes(fixture.folding_steps - start_round - 3);
                let mut expected_boundary = expected_entry;
                record_active_eq_slot_fold(&mut expected_boundary);
                let (_, entry_active_size) = active_factored_eq_physical_slot(expected_entry);
                let active_group =
                    active_factored_eq_logical_group(fixture.folding_steps - start_round - 3);
                let expected_entry_active_values = factored_eq_group_reference(
                    &expected_claim_point,
                    start_round + 3,
                    fixture.folding_steps - start_round - 3,
                    active_group,
                );
                assert_eq!(
                    expected_entry_active_values.len(),
                    1usize << entry_active_size,
                );
                let expected_boundary_active_values = expected_entry_active_values
                    .chunks_exact(2)
                    .map(|pair| add(pair[0], pair[1]))
                    .collect::<Vec<_>>();
                assert_eq!(pass.eq_entry.sizes, expected_entry);
                assert_eq!(pass.one_fold_boundary_sizes, expected_boundary);
                expected_published.push(expected_publication);
                observed_published.push(published);
                expected_tensors.push(expected_tensor);
                observed_tensors.push(observed_tensor);
                expected_eq_entries.push(expected_entry);
                expected_eq_boundaries.push(expected_boundary);
                expected_eq_entry_active_sizes.push(entry_active_size);
                expected_eq_entry_active_values.push(expected_entry_active_values);
                expected_eq_boundary_active_sizes.push(entry_active_size - 1);
                expected_eq_boundary_active_values.push(expected_boundary_active_values);
                Ok(())
            },
        )
        .unwrap();

        let constant_after = download(
            &context,
            raw_device_slice(
                get_eq_high_constant_device_ptr(),
                2 * GKR_EQ_GROUP_TABLE_LEN,
            ),
        );
        let r0_low_after = download(&context, &prepared.hook.r0_eq.eq_low[..]);
        let observed_coefficients = download(&context, &coefficients[..4 * entry_round]);
        let observed_claim_point = download(&context, &prepared.claim_point[..]);
        let observed_seed: [u32; 8] = download(&context, &seed[..]).try_into().unwrap();
        let observed_claim = download(&context, &claim[..])[0];
        let observed_eq_prefactor = download(&context, &eq_prefactor[..])[0];
        let source_after = fixture.source_snapshot();
        context.get_exec_stream().synchronize().unwrap();

        assert_eq!(source_after, source_before);
        assert_eq!(constant_after, constant_before);
        assert_eq!(r0_low_after, r0_low_before);
        assert_eq!(eq_snapshots.len(), expected_eq_entries.len());
        for (pass_index, snapshot) in eq_snapshots.iter().enumerate() {
            assert_eq!(snapshot.entry_sizes, expected_eq_entries[pass_index]);
            assert_eq!(
                snapshot.entry_active_size,
                expected_eq_entry_active_sizes[pass_index],
            );
            assert_eq!(
                snapshot.entry_active_values,
                expected_eq_entry_active_values[pass_index],
            );
            assert_eq!(snapshot.one_fold_sizes, expected_eq_boundaries[pass_index],);
            assert_eq!(
                snapshot.one_fold_active_size,
                expected_eq_boundary_active_sizes[pass_index],
            );
            assert_eq!(
                snapshot.one_fold_active_values,
                expected_eq_boundary_active_values[pass_index],
            );
        }
        let expected = DrContinuationChainObservation {
            published: expected_published,
            tensors: expected_tensors,
            coefficients: expected_coefficients,
            claim_point: expected_claim_point,
            seed: expected_seed,
            claim: expected_claim,
            eq_prefactor: expected_eq_prefactor,
            eq_entries: expected_eq_entries,
            eq_boundaries: expected_eq_boundaries,
            eq_entry_active_sizes: expected_eq_entry_active_sizes,
            eq_entry_active_values: expected_eq_entry_active_values,
            eq_boundary_active_sizes: expected_eq_boundary_active_sizes,
            eq_boundary_active_values: expected_eq_boundary_active_values,
            constant_slab: constant_before,
            r0_low: r0_low_before,
        };
        let observed = DrContinuationChainObservation {
            published: observed_published,
            tensors: observed_tensors,
            coefficients: observed_coefficients,
            claim_point: observed_claim_point,
            seed: observed_seed,
            claim: observed_claim,
            eq_prefactor: observed_eq_prefactor,
            eq_entries: prepared
                .hook
                .continuation_launches
                .iter()
                .map(|pass| pass.eq_entry.sizes)
                .collect(),
            eq_boundaries: eq_snapshots
                .iter()
                .map(|snapshot| snapshot.one_fold_sizes)
                .collect(),
            eq_entry_active_sizes: eq_snapshots
                .iter()
                .map(|snapshot| snapshot.entry_active_size)
                .collect(),
            eq_entry_active_values: eq_snapshots
                .iter()
                .map(|snapshot| snapshot.entry_active_values.clone())
                .collect(),
            eq_boundary_active_sizes: eq_snapshots
                .iter()
                .map(|snapshot| snapshot.one_fold_active_size)
                .collect(),
            eq_boundary_active_values: eq_snapshots
                .iter()
                .map(|snapshot| snapshot.one_fold_active_values.clone())
                .collect(),
            constant_slab: constant_after,
            r0_low: r0_low_after,
        };
        assert_eq!(observed, expected);
        assert!(
            (0..2).any(|a0| (0..2).any(
                |a1| (0..2).any(|a2| { expected.tensors[0][9 * a0 + 3 * a1 + a2] != E4::ZERO })
            )),
            "Boolean continuation cells must make product-excess mutation non-vacuous",
        );
        for mutation in [
            DrContinuationChainMutation::Publication,
            DrContinuationChainMutation::Axis,
            DrContinuationChainMutation::BatchExponent,
            DrContinuationChainMutation::ProductExcess,
            DrContinuationChainMutation::EqSuffix,
            DrContinuationChainMutation::ConstantPointer,
            DrContinuationChainMutation::PriorViewReuse,
            DrContinuationChainMutation::CumulativeDrain,
        ] {
            assert_ne!(
                mutate_dr_continuation_chain(&expected, mutation),
                observed,
                "{mutation:?} mutation survived mask={mask:#04x}",
            );
        }
    }
}

#[test]
#[ignore = "requires CUDA; execute only through an independently approved D5 GPU lock packet"]
fn dr_window_continuation_mismatch_lsb_seam_matches_legacy() {
    let mismatch = production_dr_final_order_mismatches()
        .into_iter()
        .next()
        .expect("the production corpus has nine canonical/raw mismatch layers");
    assert_ne!(
        mismatch.publication_indices,
        (0..mismatch.publication_indices.len()).collect::<Vec<_>>(),
    );

    let context = make_test_context(256, 64);
    let fixture = DrGpuFixture::new_with_publication_permutation(
        &context,
        mismatch.enabled_mask,
        7,
        0xd500_0000_0000_0001,
        Some(&mismatch.publication_indices),
    );
    let canonical = fixture.projection.canonical_sources();
    let raw = fixture.legacy_slots.input_addresses().collect::<Vec<_>>();
    assert_eq!(canonical.len(), raw.len());
    let identity = (0..canonical.len()).collect::<Vec<_>>();
    let zero_cells = vec![E4::ZERO; 4 * canonical.len()];
    let lookup_shape =
        dr_final_lookup_four_cells(canonical, &raw, &fixture.aliases, &zero_cells).unwrap();
    assert_eq!(
        lookup_shape.publication_indices, mismatch.publication_indices,
        "{} layer {} permutation must reach the GPU fixture unchanged",
        mismatch.layout_name, mismatch.absolute_layer,
    );
    assert_ne!(lookup_shape.publication_indices, identity);

    let source_before = fixture.source_snapshot();
    let expected_r0_tensor = fixture.expected_tensor();
    let mut prepared = fixture.prepare();
    bind_dr_window_continuations(
        &mut prepared.hook,
        &fixture.storage,
        prepared.claim_point.as_ptr(),
        &context,
    )
    .unwrap();
    assert_eq!(prepared.hook.continuation_launches.len(), 1);
    assert_eq!(prepared.hook.megakernel_entry_round, 6);

    let mut seed = upload(&context, &fixture.tail_seed);
    let initial_claim = fixture.initial_claim(&expected_r0_tensor);
    let mut claim = upload(&context, &[initial_claim]);
    let mut eq_prefactor = upload(&context, &[E4::ONE]);
    let mut coefficients: DeviceAllocation<E4> = context
        .alloc(
            4 * prepared.hook.megakernel_entry_round,
            AllocationPlacement::BestFit,
        )
        .unwrap();

    let (r0_active_slot, r0_active_size) = resolve_active_eq_slot(
        &prepared.hook.r0_eq.eq_sizes,
        prepared.hook.r0_eq.eq_low.as_mut_ptr(),
    );
    let r0_tail = WindowTailState {
        partials: prepared.scratch.as_ptr(),
        row_tiles: prepared.hook.r0_launch.row_tiles,
        reduced_tensor: prepared.hook.r0_launch.reduced_tensor,
        prev_claim_coords: prepared.claim_point.as_ptr(),
        seed: seed.as_mut_ptr(),
        claim: claim.as_mut_ptr(),
        eq_prefactor: eq_prefactor.as_mut_ptr(),
        coeffs_out: coefficients.as_mut_ptr(),
        challenges_out: prepared.claim_point.as_mut_ptr(),
        active_eq_slot_base: r0_active_slot,
        active_eq_size_before_fold: r0_active_size,
    };
    launch_window_tensor_round_tail(WindowTailArm::Split, &r0_tail, &context).unwrap();

    let mut expected_seed = fixture.tail_seed;
    let mut expected_claim = initial_claim;
    let mut expected_eq_prefactor = E4::ONE;
    let mut expected_claim_point = fixture.claim_point.clone();
    let r0_rho: [E4; 3] = expected_claim_point[..3].try_into().unwrap();
    let (r0_coefficients, r0_challenges) = tensor_round_tail_reference(
        expected_r0_tensor,
        &r0_rho,
        &mut expected_seed,
        &mut expected_claim,
        &mut expected_eq_prefactor,
    );
    let mut expected_coefficients = vec![E4::ZERO; 24];
    expected_coefficients[..12].copy_from_slice(&r0_coefficients);
    expected_claim_point[..3].copy_from_slice(&r0_challenges);

    let claim_point_ptr = prepared.claim_point.as_mut_ptr();
    let coeffs_ptr = coefficients.as_mut_ptr();
    let seed_ptr = seed.as_mut_ptr();
    let claim_ptr = claim.as_mut_ptr();
    let eq_prefactor_ptr = eq_prefactor.as_mut_ptr();
    let mut expected_publication = None;
    let mut observed_publication = None;
    let snapshots = launch_dr_window_continuation_chain_for_test(
        &prepared.hook,
        WindowTailArm::Split,
        claim_point_ptr,
        coeffs_ptr,
        seed_ptr,
        claim_ptr,
        eq_prefactor_ptr,
        &context,
        |pass| {
            assert_eq!(pass.geometry.start_round, 3);
            let folding_challenges: [E4; 3] = expected_claim_point[..3].try_into().unwrap();
            let expected_canonical = canonical
                .iter()
                .copied()
                .map(|address| {
                    (
                        address,
                        fold_dr_continuation_depth3(&fixture.columns[&address], folding_challenges)
                            .unwrap(),
                    )
                })
                .collect::<BTreeMap<_, _>>();
            let mut expected_columns = expected_canonical.clone();
            for raw_address in fixture.legacy_slots.input_addresses() {
                let canonical_address = fixture
                    .aliases
                    .get(&raw_address)
                    .copied()
                    .unwrap_or(raw_address);
                expected_columns
                    .insert(raw_address, expected_canonical[&canonical_address].clone());
            }
            let expected_tensor = dr_continuation_tensor_reference(
                &fixture.oracle_program,
                &expected_columns,
                fixture.batch_base,
                &expected_claim_point[6..fixture.folding_steps],
            )
            .unwrap();

            let partial_values = download(
                &context,
                raw_device_slice(
                    pass.launch.binding.partials,
                    TENSOR_CELLS * pass.launch.row_tiles,
                ),
            );
            let first_slot = pass.launch.binding.batch.enabled_mask.trailing_zeros() as usize;
            let destination_record = pass.launch.binding.batch.slots[first_slot].io[0];
            let destination_slot = usize::from((destination_record.cache >> 11) & 0x0f);
            let destination_base =
                pass.launch.binding.batch.tables.bases[destination_slot].cast::<E4>();
            let published_len = canonical.len() * pass.geometry.per_poly_len;
            let published = download(&context, raw_device_slice(destination_base, published_len));

            let rho: [E4; 3] = expected_claim_point[3..6].try_into().unwrap();
            let (tail_coefficients, tail_challenges) = tensor_round_tail_reference(
                expected_tensor,
                &rho,
                &mut expected_seed,
                &mut expected_claim,
                &mut expected_eq_prefactor,
            );
            expected_coefficients[12..24].copy_from_slice(&tail_coefficients);
            expected_claim_point[3..6].copy_from_slice(&tail_challenges);

            let observed_coefficients = download(
                &context,
                raw_device_slice(coeffs_ptr.cast_const(), expected_coefficients.len()),
            );
            let observed_claim_point = download(
                &context,
                raw_device_slice(claim_point_ptr.cast_const(), fixture.folding_steps),
            );
            let observed_seed = download(&context, raw_device_slice(seed_ptr.cast_const(), 8));
            let observed_claim = download(&context, raw_device_slice(claim_ptr.cast_const(), 1));
            let observed_eq_prefactor =
                download(&context, raw_device_slice(eq_prefactor_ptr.cast_const(), 1));
            context.get_exec_stream().synchronize().unwrap();

            let mut observed_tensor = [E4::ZERO; TENSOR_CELLS];
            for (index, value) in partial_values.into_iter().enumerate() {
                observed_tensor[index % TENSOR_CELLS].add_assign(&value);
            }
            compare_dr_tensors(&expected_tensor, &observed_tensor).unwrap();
            let expected_flat = canonical
                .iter()
                .flat_map(|address| expected_canonical[address].iter().copied())
                .collect::<Vec<_>>();
            assert_eq!(published, expected_flat);
            assert_eq!(observed_coefficients, expected_coefficients);
            assert_eq!(observed_claim_point, expected_claim_point);
            assert_eq!(observed_seed, expected_seed);
            assert_eq!(observed_claim, vec![expected_claim]);
            assert_eq!(observed_eq_prefactor, vec![expected_eq_prefactor]);
            expected_publication = Some(expected_flat);
            observed_publication = Some(published);
            Ok(())
        },
    )
    .unwrap();
    assert_eq!(snapshots.len(), 1);

    let expected_publication = expected_publication.unwrap();
    let observed_publication = observed_publication.unwrap();
    assert_eq!(observed_publication, expected_publication);
    let continuation_stride = observed_publication.len() / canonical.len();
    assert_eq!(continuation_stride, 32);
    let close_challenges: [E4; 3] = expected_claim_point[3..6].try_into().unwrap();
    let observed_canonical_four = observed_publication
        .chunks_exact(continuation_stride)
        .flat_map(|column| fold_dr_continuation_depth3(column, close_challenges).unwrap())
        .collect::<Vec<_>>();
    let expected_canonical_four = canonical
        .iter()
        .flat_map(|address| {
            let after_r0 = fold_dr_continuation_depth3(
                &fixture.columns[address],
                expected_claim_point[..3].try_into().unwrap(),
            )
            .unwrap();
            fold_dr_continuation_depth3(&after_r0, close_challenges).unwrap()
        })
        .collect::<Vec<_>>();
    assert_eq!(observed_canonical_four, expected_canonical_four);
    assert_eq!(observed_canonical_four.len(), 4 * canonical.len());

    let lookup =
        dr_final_lookup_four_cells(canonical, &raw, &fixture.aliases, &observed_canonical_four)
            .unwrap();
    assert_eq!(lookup.publication_indices, mismatch.publication_indices);
    assert_ne!(lookup.cells, observed_canonical_four);
    assert!(dr_final_lookup_four_cells(
        canonical,
        &raw,
        &fixture.aliases,
        &observed_canonical_four[..2 * canonical.len()],
    )
    .is_err());

    let mut permuted_four = observed_canonical_four.clone();
    for cells in permuted_four.chunks_exact_mut(4) {
        cells.swap(1, 2);
    }
    let permuted_lookup =
        dr_final_lookup_four_cells(canonical, &raw, &fixture.aliases, &permuted_four).unwrap();
    assert_ne!(permuted_lookup.cells, lookup.cells);
    let mut wrong_indices = lookup.publication_indices.clone();
    wrong_indices.rotate_left(1);
    let wrong_lookup_cells = wrong_indices
        .iter()
        .flat_map(|index| {
            observed_canonical_four[4 * index..4 * index + 4]
                .iter()
                .copied()
        })
        .collect::<Vec<_>>();
    assert_ne!(wrong_lookup_cells, lookup.cells);

    let r_before_last = expected_claim_point[6];
    let r_last = fixture.batch_base;
    let d_last_evals = upload(&context, &lookup.cells);
    let d_challenges = upload(&context, &[r_before_last, r_last]);
    let mut d_lines: DeviceAllocation<E4> = context
        .alloc(2 * canonical.len(), AllocationPlacement::BestFit)
        .unwrap();
    crate::gkr_ops::backward_dim_reducing_lsb_lines(
        &d_last_evals[..],
        &d_challenges[..1],
        &mut d_lines[..],
        context.get_exec_stream(),
    )
    .unwrap();
    let mut d_two_var: DeviceAllocation<E4> = context
        .alloc(canonical.len(), AllocationPlacement::BestFit)
        .unwrap();
    crate::gkr_ops::backward_new_claims_two_var(
        &d_last_evals[..],
        &d_challenges[..],
        &mut d_two_var[..],
        context.get_exec_stream(),
    )
    .unwrap();
    let mut d_from_lines: DeviceAllocation<E4> = context
        .alloc(canonical.len(), AllocationPlacement::BestFit)
        .unwrap();
    crate::gkr_ops::backward_new_claims_linear(
        &d_lines[..],
        &d_challenges[1..],
        &mut d_from_lines[..],
        context.get_exec_stream(),
    )
    .unwrap();
    let observed_lines = download(&context, &d_lines[..]);
    let observed_two_var = download(&context, &d_two_var[..]);
    let observed_from_lines = download(&context, &d_from_lines[..]);
    let observed_seed: [u32; 8] = download(&context, &seed[..]).try_into().unwrap();
    let observed_claim = download(&context, &claim[..])[0];
    let observed_eq_prefactor = download(&context, &eq_prefactor[..])[0];
    let source_after = fixture.source_snapshot();
    context.get_exec_stream().synchronize().unwrap();

    let one_minus_r_before_last = {
        let mut value = E4::ONE;
        value.sub_assign(&r_before_last);
        value
    };
    let one_minus_r_last = {
        let mut value = E4::ONE;
        value.sub_assign(&r_last);
        value
    };
    let expected_lines = lookup
        .cells
        .chunks_exact(4)
        .flat_map(|cells| {
            [0, 1].map(|gate_bit| {
                add(
                    mul(cells[gate_bit], one_minus_r_before_last),
                    mul(cells[2 + gate_bit], r_before_last),
                )
            })
        })
        .collect::<Vec<_>>();
    let expected_claims = expected_lines
        .chunks_exact(2)
        .map(|line| add(mul(line[0], one_minus_r_last), mul(line[1], r_last)))
        .collect::<Vec<_>>();
    assert_eq!(observed_lines, expected_lines);
    assert_eq!(observed_two_var, expected_claims);
    assert_eq!(observed_from_lines, expected_claims);
    assert_eq!(observed_seed, expected_seed);
    assert_eq!(observed_claim, expected_claim);
    assert_eq!(observed_eq_prefactor, expected_eq_prefactor);
    assert_eq!(source_after, source_before);

    let canonical_iteration_lines = observed_canonical_four
        .chunks_exact(4)
        .flat_map(|cells| {
            [0, 1].map(|gate_bit| {
                add(
                    mul(cells[gate_bit], one_minus_r_before_last),
                    mul(cells[2 + gate_bit], r_before_last),
                )
            })
        })
        .collect::<Vec<_>>();
    assert_ne!(canonical_iteration_lines, expected_lines);
}
