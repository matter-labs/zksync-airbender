use std::collections::{BTreeMap, VecDeque};
use std::sync::{Arc, Mutex};

use cs::definitions::GKRAddress;
use cs::gkr_compiler::OutputType;
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::memory_copy_async;
use era_cudart::paste::paste;
use era_cudart::result::CudaResult;
use era_cudart::slice::{CudaSliceMut, DeviceSlice};
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use field::{Field, FieldExtension};
use prover::gkr::prover::dimension_reduction::forward::DimensionReducingInputOutput;
use prover::gkr::prover::transcript_utils::{commit_field_els, draw_random_field_els};
use prover::gkr::prover::SumcheckIntermediateProofValues;
use prover::gkr::sumcheck::evaluation_kernels::GKRInputs;
use prover::gkr::sumcheck::{
    evaluate_eq_poly, evaluate_small_univariate_poly, output_univariate_monomial_form_max_quadratic,
};
use prover::transcript::Seed;

use super::forward::GpuGKRForwardScratch;
use super::{
    alloc_host_and_copy, GpuExtensionFieldPolyContinuingLaunchDescriptor,
    GpuExtensionFieldPolyInitialSource, GpuGKRStorage, GpuSumcheckRound0ScheduledLaunchDescriptors,
    GpuSumcheckRound1PreparedStorage, GpuSumcheckRound1ScheduledLaunchDescriptors,
    GpuSumcheckRound2PreparedStorage, GpuSumcheckRound2ScheduledLaunchDescriptors,
    GpuSumcheckRound3AndBeyondPreparedStorage,
    GpuSumcheckRound3AndBeyondScheduledLaunchDescriptors,
};
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::cub::device_reduce::{
    batch_reduce, get_batch_reduce_temp_storage_bytes, Reduce, ReduceOperation,
};
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{DeviceAllocation, HostAllocation, ProverContext, UnsafeAccessor};
use crate::primitives::device_structures::DeviceMatrix;
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E2, E4, E6};
use crate::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};

#[derive(Debug, Clone, PartialEq, Eq)]
struct DimensionReducingKernelBlueprint<E> {
    inputs: GKRInputs,
    batch_challenges: Vec<E>,
}

#[derive(Clone, Debug)]
struct GpuGKRDimensionReducingRound3Prepared<E> {
    step: usize,
    prepared: GpuSumcheckRound3AndBeyondPreparedStorage<E>,
}

struct GpuGKRDimensionReducingRoundScratch<E> {
    claim_point: DeviceAllocation<E>,
    eq_values: DeviceAllocation<E>,
    contributions: DeviceAllocation<E>,
    weighted_rows: DeviceAllocation<E>,
    reduction_output: DeviceAllocation<E>,
    reduction_temp_storage: DeviceAllocation<u8>,
}

#[derive(Clone, Debug)]
pub(crate) struct GpuGKRDimensionReducingKernelPlan<B, E> {
    pub(crate) inputs: GKRInputs,
    pub(crate) batch_challenges: Vec<E>,
    round1_prepared: GpuSumcheckRound1PreparedStorage<B, E>,
    round2_prepared: Option<GpuSumcheckRound2PreparedStorage<B, E>>,
    round3_and_beyond_prepared: Vec<GpuGKRDimensionReducingRound3Prepared<E>>,
}

pub(crate) struct GpuGKRDimensionReducingSumcheckLayerPlan<B, E> {
    pub(crate) layer_idx: usize,
    pub(crate) trace_len_after_reduction: usize,
    pub(crate) folding_steps: usize,
    kernel_plans: Vec<GpuGKRDimensionReducingKernelPlan<B, E>>,
    round0_descriptors: Vec<GpuSumcheckRound0ScheduledLaunchDescriptors<B, E>>,
    round_scratch: GpuGKRDimensionReducingRoundScratch<E>,
}

pub(crate) struct GpuGKRDimensionReducingBackwardState<B, E> {
    #[allow(dead_code)] // Keeps queued forward ranges alive until the stream consumes them.
    forward_tracing_ranges: Vec<Range>,
    #[allow(dead_code)] // Keeps queued forward scratch alive until the stream consumes it.
    forward_scratch: GpuGKRForwardScratch,
    storage: GpuGKRStorage<B, E>,
    pending_layers: VecDeque<(usize, BTreeMap<OutputType, DimensionReducingInputOutput>)>,
    next_trace_len_after_reduction: usize,
}

pub(crate) struct GpuGKRDimensionReducingLayerExecution<E: FieldExtension<BF> + Field> {
    pub(crate) proof: SumcheckIntermediateProofValues<BF, E>,
    pub(crate) new_claims: BTreeMap<GKRAddress, E>,
    pub(crate) new_claim_point: Vec<E>,
    pub(crate) next_batching_challenge: E,
    pub(crate) updated_seed: Seed,
}

enum ScheduledDimensionReducingRoundState<B, E> {
    Round1 {
        callbacks: Callbacks<'static>,
        scheduled: Vec<GpuSumcheckRound1ScheduledLaunchDescriptors<B, E>>,
    },
    Round2 {
        callbacks: Callbacks<'static>,
        scheduled: Vec<GpuSumcheckRound2ScheduledLaunchDescriptors<B, E>>,
    },
    Round3AndBeyond {
        callbacks: Callbacks<'static>,
        scheduled: Vec<GpuSumcheckRound3AndBeyondScheduledLaunchDescriptors<E>>,
    },
}

struct ScheduledDimensionReducingReductionState<E> {
    callbacks: Callbacks<'static>,
    reduction_output: HostAllocation<[E]>,
}

struct ScheduledDimensionReducingFinalReadback<E> {
    callbacks: Callbacks<'static>,
    evaluations: BTreeMap<GKRAddress, HostAllocation<[E]>>,
}

struct ScheduledDimensionReducingLayerExecutionState<E: FieldExtension<BF> + Field> {
    seed: Seed,
    claim: E,
    eq_prefactor: E,
    folding_challenges: Vec<E>,
    internal_round_coefficients: Vec<[E; 4]>,
    result: Option<GpuGKRDimensionReducingLayerExecution<E>>,
}

pub(crate) struct GpuGKRDimensionReducingScheduledLayerExecution<B, E: FieldExtension<BF> + Field> {
    #[allow(dead_code)]
    // Keeps the async claim-point upload source alive until the stream consumes it.
    claim_point_host: HostAllocation<[E]>,
    #[allow(dead_code)]
    // Keeps queued challenge-dependent host buffers alive until the stream consumes them.
    round_challenge_buffers: Vec<HostAllocation<[E]>>,
    #[allow(dead_code)]
    // Keeps queued descriptor uploads and their callbacks alive until the stream consumes them.
    round_states: Vec<ScheduledDimensionReducingRoundState<B, E>>,
    #[allow(dead_code)]
    // Keeps round reduction uploads/readbacks and callbacks alive until the stream consumes them.
    reduction_states: Vec<ScheduledDimensionReducingReductionState<E>>,
    #[allow(dead_code)]
    // Keeps final-step readbacks and callback alive until the stream consumes them.
    final_readback: ScheduledDimensionReducingFinalReadback<E>,
    shared_state: Arc<Mutex<ScheduledDimensionReducingLayerExecutionState<E>>>,
}

const GKR_DIM_REDUCING_THREADS_PER_BLOCK: u32 = WARP_SIZE * 4;

cuda_kernel_signature_arguments_and_function!(
    GpuDimensionReducingPairwiseRound0<T>,
    inputs: *const GpuExtensionFieldPolyInitialSource<T>,
    outputs: *const GpuExtensionFieldPolyInitialSource<T>,
    batch_challenge: T,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_signature_arguments_and_function!(
    GpuDimensionReducingLookupRound0<T>,
    inputs: *const GpuExtensionFieldPolyInitialSource<T>,
    outputs: *const GpuExtensionFieldPolyInitialSource<T>,
    batch_challenge_0: T,
    batch_challenge_1: T,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_signature_arguments_and_function!(
    GpuDimensionReducingPairwiseContinuation<T>,
    inputs: *const GpuExtensionFieldPolyContinuingLaunchDescriptor<T>,
    batch_challenge: T,
    explicit_form: bool,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_signature_arguments_and_function!(
    GpuDimensionReducingLookupContinuation<T>,
    inputs: *const GpuExtensionFieldPolyContinuingLaunchDescriptor<T>,
    batch_challenge_0: T,
    batch_challenge_1: T,
    explicit_form: bool,
    contributions: *mut T,
    acc_size: u32,
);

cuda_kernel_signature_arguments_and_function!(
    GpuDimensionReducingBuildEq<T>,
    claim_point: *const T,
    challenge_offset: u32,
    challenge_count: u32,
    eq_values: *mut T,
    acc_size: u32,
);

cuda_kernel_signature_arguments_and_function!(
    GpuDimensionReducingWeightContributions<T>,
    contributions: *const T,
    kernel_count: u32,
    eq_values: *const T,
    weighted_rows: *mut T,
    acc_size: u32,
);

trait GpuDimensionReducingKernelSet: Reduce + Copy + Sized {
    const PAIRWISE_ROUND0: GpuDimensionReducingPairwiseRound0Signature<Self>;
    const LOOKUP_ROUND0: GpuDimensionReducingLookupRound0Signature<Self>;
    const PAIRWISE_CONTINUATION: GpuDimensionReducingPairwiseContinuationSignature<Self>;
    const LOOKUP_CONTINUATION: GpuDimensionReducingLookupContinuationSignature<Self>;
    const BUILD_EQ: GpuDimensionReducingBuildEqSignature<Self>;
    const WEIGHT_CONTRIBUTIONS: GpuDimensionReducingWeightContributionsSignature<Self>;
}

macro_rules! gkr_dim_reducing_kernels {
    ($type:ty) => {
        paste! {
            cuda_kernel_declaration!(
                [<ab_gkr_dim_reducing_pairwise_round0_ $type:lower _kernel>](
                    inputs: *const GpuExtensionFieldPolyInitialSource<$type>,
                    outputs: *const GpuExtensionFieldPolyInitialSource<$type>,
                    batch_challenge: $type,
                    contributions: *mut $type,
                    acc_size: u32,
                )
            );
            cuda_kernel_declaration!(
                [<ab_gkr_dim_reducing_lookup_round0_ $type:lower _kernel>](
                    inputs: *const GpuExtensionFieldPolyInitialSource<$type>,
                    outputs: *const GpuExtensionFieldPolyInitialSource<$type>,
                    batch_challenge_0: $type,
                    batch_challenge_1: $type,
                    contributions: *mut $type,
                    acc_size: u32,
                )
            );
            cuda_kernel_declaration!(
                [<ab_gkr_dim_reducing_pairwise_continuation_ $type:lower _kernel>](
                    inputs: *const GpuExtensionFieldPolyContinuingLaunchDescriptor<$type>,
                    batch_challenge: $type,
                    explicit_form: bool,
                    contributions: *mut $type,
                    acc_size: u32,
                )
            );
            cuda_kernel_declaration!(
                [<ab_gkr_dim_reducing_lookup_continuation_ $type:lower _kernel>](
                    inputs: *const GpuExtensionFieldPolyContinuingLaunchDescriptor<$type>,
                    batch_challenge_0: $type,
                    batch_challenge_1: $type,
                    explicit_form: bool,
                    contributions: *mut $type,
                    acc_size: u32,
                )
            );
            cuda_kernel_declaration!(
                [<ab_gkr_dim_reducing_build_eq_ $type:lower _kernel>](
                    claim_point: *const $type,
                    challenge_offset: u32,
                    challenge_count: u32,
                    eq_values: *mut $type,
                    acc_size: u32,
                )
            );
            cuda_kernel_declaration!(
                [<ab_gkr_dim_reducing_weight_contributions_ $type:lower _kernel>](
                    contributions: *const $type,
                    kernel_count: u32,
                    eq_values: *const $type,
                    weighted_rows: *mut $type,
                    acc_size: u32,
                )
            );

            impl GpuDimensionReducingKernelSet for $type {
                const PAIRWISE_ROUND0: GpuDimensionReducingPairwiseRound0Signature<Self> =
                    [<ab_gkr_dim_reducing_pairwise_round0_ $type:lower _kernel>];
                const LOOKUP_ROUND0: GpuDimensionReducingLookupRound0Signature<Self> =
                    [<ab_gkr_dim_reducing_lookup_round0_ $type:lower _kernel>];
                const PAIRWISE_CONTINUATION: GpuDimensionReducingPairwiseContinuationSignature<Self> =
                    [<ab_gkr_dim_reducing_pairwise_continuation_ $type:lower _kernel>];
                const LOOKUP_CONTINUATION: GpuDimensionReducingLookupContinuationSignature<Self> =
                    [<ab_gkr_dim_reducing_lookup_continuation_ $type:lower _kernel>];
                const BUILD_EQ: GpuDimensionReducingBuildEqSignature<Self> =
                    [<ab_gkr_dim_reducing_build_eq_ $type:lower _kernel>];
                const WEIGHT_CONTRIBUTIONS: GpuDimensionReducingWeightContributionsSignature<Self> =
                    [<ab_gkr_dim_reducing_weight_contributions_ $type:lower _kernel>];
            }
        }
    };
}

gkr_dim_reducing_kernels!(E2);
gkr_dim_reducing_kernels!(E4);
gkr_dim_reducing_kernels!(E6);

fn gkr_dim_reducing_launch_config(count: u32, context: &ProverContext) -> CudaLaunchConfig<'_> {
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(GKR_DIM_REDUCING_THREADS_PER_BLOCK, count.max(1));
    CudaLaunchConfig::basic(grid_dim, block_dim, context.get_exec_stream())
}

fn launch_pairwise_round0<E: GpuDimensionReducingKernelSet>(
    descriptors: &GpuSumcheckRound0ScheduledLaunchDescriptors<impl Sized, E>,
    batch_challenge: E,
    contributions: *mut E,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let inputs = descriptors.device.extension_field_inputs.as_ptr();
    let outputs = descriptors.device.extension_field_outputs.as_ptr();
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuDimensionReducingPairwiseRound0Arguments::new(
        inputs,
        outputs,
        batch_challenge,
        contributions,
        acc_size as u32,
    );

    GpuDimensionReducingPairwiseRound0Function(E::PAIRWISE_ROUND0).launch(&config, &args)
}

fn launch_lookup_round0<E: GpuDimensionReducingKernelSet>(
    descriptors: &GpuSumcheckRound0ScheduledLaunchDescriptors<impl Sized, E>,
    batch_challenges: &[E],
    contributions: *mut E,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let batch_challenge_0 = batch_challenges[0];
    let batch_challenge_1 = batch_challenges[1];
    let inputs = descriptors.device.extension_field_inputs.as_ptr();
    let outputs = descriptors.device.extension_field_outputs.as_ptr();
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuDimensionReducingLookupRound0Arguments::new(
        inputs,
        outputs,
        batch_challenge_0,
        batch_challenge_1,
        contributions,
        acc_size as u32,
    );

    GpuDimensionReducingLookupRound0Function(E::LOOKUP_ROUND0).launch(&config, &args)
}

fn launch_pairwise_continuation<E: GpuDimensionReducingKernelSet>(
    descriptors: *const GpuExtensionFieldPolyContinuingLaunchDescriptor<E>,
    batch_challenge: E,
    explicit_form: bool,
    contributions: *mut E,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuDimensionReducingPairwiseContinuationArguments::new(
        descriptors,
        batch_challenge,
        explicit_form,
        contributions,
        acc_size as u32,
    );

    GpuDimensionReducingPairwiseContinuationFunction(E::PAIRWISE_CONTINUATION)
        .launch(&config, &args)
}

fn launch_lookup_continuation<E: GpuDimensionReducingKernelSet>(
    descriptors: *const GpuExtensionFieldPolyContinuingLaunchDescriptor<E>,
    batch_challenges: &[E],
    explicit_form: bool,
    contributions: *mut E,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let batch_challenge_0 = batch_challenges[0];
    let batch_challenge_1 = batch_challenges[1];
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuDimensionReducingLookupContinuationArguments::new(
        descriptors,
        batch_challenge_0,
        batch_challenge_1,
        explicit_form,
        contributions,
        acc_size as u32,
    );

    GpuDimensionReducingLookupContinuationFunction(E::LOOKUP_CONTINUATION).launch(&config, &args)
}

fn launch_weight_contributions<E: GpuDimensionReducingKernelSet>(
    contributions: *const E,
    kernel_count: usize,
    eq_values: *const E,
    weighted_rows: *mut E,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuDimensionReducingWeightContributionsArguments::new(
        contributions,
        kernel_count as u32,
        eq_values,
        weighted_rows,
        acc_size as u32,
    );

    GpuDimensionReducingWeightContributionsFunction(E::WEIGHT_CONTRIBUTIONS).launch(&config, &args)
}

fn launch_build_eq_values<E: GpuDimensionReducingKernelSet>(
    claim_point: *const E,
    challenge_offset: usize,
    challenge_count: usize,
    eq_values: *mut E,
    acc_size: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    let config = gkr_dim_reducing_launch_config(acc_size as u32, context);
    let args = GpuDimensionReducingBuildEqArguments::new(
        claim_point,
        challenge_offset as u32,
        challenge_count as u32,
        eq_values,
        acc_size as u32,
    );

    GpuDimensionReducingBuildEqFunction(E::BUILD_EQ).launch(&config, &args)
}

fn build_dimension_reducing_kernel_blueprints<E: Field>(
    layer: &BTreeMap<OutputType, DimensionReducingInputOutput>,
    batch_challenge_base: E,
) -> Vec<DimensionReducingKernelBlueprint<E>> {
    let mut current_batch_challenge = E::ONE;
    let mut get_challenge = || {
        let challenge = current_batch_challenge;
        current_batch_challenge.mul_assign(&batch_challenge_base);
        challenge
    };

    let mut blueprints = Vec::new();
    for (output_type, reduced_io) in layer.iter() {
        match *output_type {
            OutputType::PermutationProduct => {
                for (input, output) in reduced_io.inputs.iter().zip(reduced_io.output.iter()) {
                    blueprints.push(DimensionReducingKernelBlueprint {
                        inputs: GKRInputs {
                            inputs_in_base: Vec::new(),
                            inputs_in_extension: vec![*input],
                            outputs_in_base: Vec::new(),
                            outputs_in_extension: vec![*output],
                        },
                        batch_challenges: vec![get_challenge()],
                    });
                }
            }
            OutputType::Lookup16Bits | OutputType::LookupTimestamps | OutputType::GenericLookup => {
                let inputs: [GKRAddress; 2] = reduced_io
                    .inputs
                    .clone()
                    .try_into()
                    .expect("dimension-reducing lookup kernels expect exactly two inputs");
                let outputs: [GKRAddress; 2] = reduced_io
                    .output
                    .clone()
                    .try_into()
                    .expect("dimension-reducing lookup kernels expect exactly two outputs");
                blueprints.push(DimensionReducingKernelBlueprint {
                    inputs: GKRInputs {
                        inputs_in_base: Vec::new(),
                        inputs_in_extension: inputs.to_vec(),
                        outputs_in_base: Vec::new(),
                        outputs_in_extension: outputs.to_vec(),
                    },
                    batch_challenges: vec![get_challenge(), get_challenge()],
                });
            }
        }
    }

    blueprints
}

impl<B, E> GpuGKRDimensionReducingBackwardState<B, E> {
    pub(super) fn new(
        forward_tracing_ranges: Vec<Range>,
        forward_scratch: GpuGKRForwardScratch,
        storage: GpuGKRStorage<B, E>,
        initial_layer_for_sumcheck: usize,
        dimension_reducing_inputs: BTreeMap<
            usize,
            BTreeMap<OutputType, DimensionReducingInputOutput>,
        >,
    ) -> Self {
        let first_output_addr = dimension_reducing_inputs[&initial_layer_for_sumcheck]
            .values()
            .next()
            .and_then(|io| io.output.first())
            .copied()
            .expect("dimension-reducing backward state requires at least one reduced output");
        let next_trace_len_after_reduction = storage.get_ext_poly(first_output_addr).len();
        let pending_layers = dimension_reducing_inputs.into_iter().rev().collect();

        Self {
            forward_tracing_ranges,
            forward_scratch,
            storage,
            pending_layers,
            next_trace_len_after_reduction,
        }
    }

    pub(crate) fn storage(&self) -> &GpuGKRStorage<B, E> {
        &self.storage
    }
}

impl<B, E: Field + Reduce> GpuGKRDimensionReducingBackwardState<B, E> {
    pub(crate) fn prepare_next_layer(
        &mut self,
        batch_challenge_base: E,
        context: &ProverContext,
    ) -> CudaResult<Option<GpuGKRDimensionReducingSumcheckLayerPlan<B, E>>> {
        let Some((layer_idx, layer)) = self.pending_layers.pop_front() else {
            return Ok(None);
        };

        let trace_len_after_reduction = self.next_trace_len_after_reduction;
        assert!(trace_len_after_reduction.is_power_of_two());
        let folding_steps = trace_len_after_reduction.trailing_zeros() as usize;
        assert!(folding_steps >= 2);

        let blueprints = build_dimension_reducing_kernel_blueprints(&layer, batch_challenge_base);
        let mut kernel_plans = Vec::with_capacity(blueprints.len());
        let mut round0_descriptors = Vec::with_capacity(blueprints.len());

        for blueprint in blueprints {
            let round0 = self
                .storage
                .schedule_upload_for_sumcheck_round_0(&blueprint.inputs, context)?;
            let round1_prepared = self
                .storage
                .prepare_for_sumcheck_round_1(&blueprint.inputs, context)?;
            let round2_prepared = if folding_steps >= 3 {
                Some(
                    self.storage
                        .prepare_for_sumcheck_round_2(&blueprint.inputs, context)?,
                )
            } else {
                None
            };
            let mut round3_and_beyond_prepared = Vec::new();
            for step in 3..folding_steps {
                let prepared = self.storage.prepare_for_sumcheck_round_3_and_beyond(
                    &blueprint.inputs,
                    step,
                    context,
                )?;
                round3_and_beyond_prepared
                    .push(GpuGKRDimensionReducingRound3Prepared { step, prepared });
            }

            round0_descriptors.push(round0);
            kernel_plans.push(GpuGKRDimensionReducingKernelPlan {
                inputs: blueprint.inputs,
                batch_challenges: blueprint.batch_challenges,
                round1_prepared,
                round2_prepared,
                round3_and_beyond_prepared,
            });
        }

        let kernel_count = kernel_plans.len();
        let max_acc_size = trace_len_after_reduction / 2;
        let weighted_rows_len = max_acc_size * 2;
        let contributions_len = kernel_count * weighted_rows_len;
        let reduction_temp_storage_bytes =
            get_batch_reduce_temp_storage_bytes::<E>(ReduceOperation::Sum, 2, max_acc_size as i32)?;

        let round_scratch = GpuGKRDimensionReducingRoundScratch {
            claim_point: context.alloc(folding_steps, AllocationPlacement::Top)?,
            eq_values: context.alloc(max_acc_size, AllocationPlacement::Top)?,
            contributions: context.alloc(contributions_len, AllocationPlacement::Top)?,
            weighted_rows: context.alloc(weighted_rows_len, AllocationPlacement::Top)?,
            reduction_output: context.alloc(2, AllocationPlacement::Top)?,
            reduction_temp_storage: context
                .alloc(reduction_temp_storage_bytes, AllocationPlacement::Top)?,
        };

        self.next_trace_len_after_reduction *= 2;

        Ok(Some(GpuGKRDimensionReducingSumcheckLayerPlan {
            layer_idx,
            trace_len_after_reduction,
            folding_steps,
            kernel_plans,
            round0_descriptors,
            round_scratch,
        }))
    }
}

impl<B, E> GpuGKRDimensionReducingSumcheckLayerPlan<B, E> {
    pub(crate) fn kernel_plans(&self) -> &[GpuGKRDimensionReducingKernelPlan<B, E>] {
        &self.kernel_plans
    }

    pub(crate) fn round0_descriptors(
        &self,
    ) -> &[GpuSumcheckRound0ScheduledLaunchDescriptors<B, E>] {
        &self.round0_descriptors
    }
}

impl<B, E: Field> GpuGKRDimensionReducingSumcheckLayerPlan<B, E> {
    pub(crate) fn schedule_round_1<'a>(
        &self,
        folding_challenges: UnsafeAccessor<[E]>,
        callbacks: &mut Callbacks<'a>,
        context: &ProverContext,
    ) -> CudaResult<Vec<GpuSumcheckRound1ScheduledLaunchDescriptors<B, E>>>
    where
        B: 'a,
        E: 'a,
    {
        self.kernel_plans
            .iter()
            .map(|kernel| {
                kernel.round1_prepared.schedule_upload_launch_descriptors(
                    folding_challenges,
                    callbacks,
                    context,
                )
            })
            .collect()
    }

    pub(crate) fn schedule_round_2<'a>(
        &self,
        folding_challenges: UnsafeAccessor<[E]>,
        callbacks: &mut Callbacks<'a>,
        context: &ProverContext,
    ) -> CudaResult<Vec<GpuSumcheckRound2ScheduledLaunchDescriptors<B, E>>>
    where
        B: 'a,
        E: 'a,
    {
        assert!(
            self.folding_steps >= 3,
            "round 2 scheduling requires at least three folding steps"
        );
        self.kernel_plans
            .iter()
            .map(|kernel| {
                kernel
                    .round2_prepared
                    .as_ref()
                    .expect("round 2 storage must be prepared")
                    .schedule_upload_launch_descriptors(folding_challenges, callbacks, context)
            })
            .collect()
    }

    pub(crate) fn schedule_round_3_and_beyond<'a>(
        &self,
        step: usize,
        folding_challenges: UnsafeAccessor<[E]>,
        callbacks: &mut Callbacks<'a>,
        context: &ProverContext,
    ) -> CudaResult<Vec<GpuSumcheckRound3AndBeyondScheduledLaunchDescriptors<E>>>
    where
        E: 'a,
    {
        assert!(step >= 3, "round 3+ scheduling starts at step 3");
        self.kernel_plans
            .iter()
            .map(|kernel| {
                kernel
                    .round3_and_beyond_prepared
                    .iter()
                    .find(|prepared| prepared.step == step)
                    .unwrap_or_else(|| panic!("missing prepared round 3+ storage for step {step}"))
                    .prepared
                    .schedule_upload_launch_descriptors(folding_challenges, callbacks, context)
            })
            .collect()
    }
}

impl<B: 'static, E> GpuGKRDimensionReducingSumcheckLayerPlan<B, E>
where
    E: Field + FieldExtension<BF> + Reduce + GpuDimensionReducingKernelSet,
    [(); E::DEGREE]: Sized,
{
    fn evaluate_with_precomputed_eq_ext(values: &[E], eq: &[E]) -> E {
        assert_eq!(values.len(), eq.len());
        let mut result = E::ZERO;
        for (value, eq_value) in values.iter().zip(eq.iter()) {
            let mut term = *eq_value;
            term.mul_assign(value);
            result.add_assign(&term);
        }

        result
    }

    fn compute_combined_claim(&self, output_claims: &BTreeMap<GKRAddress, E>) -> E {
        let mut result = E::ZERO;
        for kernel in self.kernel_plans.iter() {
            for (output, challenge) in kernel
                .inputs
                .outputs_in_extension
                .iter()
                .zip(kernel.batch_challenges.iter())
            {
                let mut term = output_claims
                    .get(output)
                    .copied()
                    .unwrap_or_else(|| panic!("missing output claim for {output:?}"));
                term.mul_assign(challenge);
                result.add_assign(&term);
            }
        }

        result
    }

    fn launch_round0_kernels(
        &mut self,
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let contributions_base = self.round_scratch.contributions.as_mut_ptr();
        for (idx, (kernel, descriptors)) in self
            .kernel_plans
            .iter()
            .zip(self.round0_descriptors.iter())
            .enumerate()
        {
            let contributions = unsafe { contributions_base.add(idx * acc_size * 2) };
            match kernel.batch_challenges.len() {
                1 => launch_pairwise_round0(
                    descriptors,
                    kernel.batch_challenges[0],
                    contributions,
                    acc_size,
                    context,
                )?,
                2 => launch_lookup_round0(
                    descriptors,
                    &kernel.batch_challenges,
                    contributions,
                    acc_size,
                    context,
                )?,
                n => unreachable!("unsupported dimension-reducing challenge count {n}"),
            }
        }

        Ok(())
    }

    fn launch_round1_kernels(
        &mut self,
        scheduled: &[GpuSumcheckRound1ScheduledLaunchDescriptors<B, E>],
        acc_size: usize,
        explicit_form: bool,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let contributions_base = self.round_scratch.contributions.as_mut_ptr();
        for (idx, (kernel, descriptors)) in
            self.kernel_plans.iter().zip(scheduled.iter()).enumerate()
        {
            let contributions = unsafe { contributions_base.add(idx * acc_size * 2) };
            let input_descriptors = descriptors.device.extension_field_inputs.as_ptr();
            match kernel.batch_challenges.len() {
                1 => launch_pairwise_continuation(
                    input_descriptors,
                    kernel.batch_challenges[0],
                    explicit_form,
                    contributions,
                    acc_size,
                    context,
                )?,
                2 => launch_lookup_continuation(
                    input_descriptors,
                    &kernel.batch_challenges,
                    explicit_form,
                    contributions,
                    acc_size,
                    context,
                )?,
                n => unreachable!("unsupported dimension-reducing challenge count {n}"),
            }
        }

        Ok(())
    }

    fn launch_round2_kernels(
        &mut self,
        scheduled: &[GpuSumcheckRound2ScheduledLaunchDescriptors<B, E>],
        acc_size: usize,
        explicit_form: bool,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let contributions_base = self.round_scratch.contributions.as_mut_ptr();
        for (idx, (kernel, descriptors)) in
            self.kernel_plans.iter().zip(scheduled.iter()).enumerate()
        {
            let contributions = unsafe { contributions_base.add(idx * acc_size * 2) };
            let input_descriptors = descriptors.device.extension_field_inputs.as_ptr();
            match kernel.batch_challenges.len() {
                1 => launch_pairwise_continuation(
                    input_descriptors,
                    kernel.batch_challenges[0],
                    explicit_form,
                    contributions,
                    acc_size,
                    context,
                )?,
                2 => launch_lookup_continuation(
                    input_descriptors,
                    &kernel.batch_challenges,
                    explicit_form,
                    contributions,
                    acc_size,
                    context,
                )?,
                n => unreachable!("unsupported dimension-reducing challenge count {n}"),
            }
        }

        Ok(())
    }

    fn launch_round3_kernels(
        &mut self,
        scheduled: &[GpuSumcheckRound3AndBeyondScheduledLaunchDescriptors<E>],
        acc_size: usize,
        explicit_form: bool,
        context: &ProverContext,
    ) -> CudaResult<()> {
        let contributions_base = self.round_scratch.contributions.as_mut_ptr();
        for (idx, (kernel, descriptors)) in
            self.kernel_plans.iter().zip(scheduled.iter()).enumerate()
        {
            let contributions = unsafe { contributions_base.add(idx * acc_size * 2) };
            let input_descriptors = descriptors.device.extension_field_inputs.as_ptr();
            match kernel.batch_challenges.len() {
                1 => launch_pairwise_continuation(
                    input_descriptors,
                    kernel.batch_challenges[0],
                    explicit_form,
                    contributions,
                    acc_size,
                    context,
                )?,
                2 => launch_lookup_continuation(
                    input_descriptors,
                    &kernel.batch_challenges,
                    explicit_form,
                    contributions,
                    acc_size,
                    context,
                )?,
                n => unreachable!("unsupported dimension-reducing challenge count {n}"),
            }
        }

        Ok(())
    }

    fn schedule_round_coefficients_reduction(
        &mut self,
        step: usize,
        acc_size: usize,
        context: &ProverContext,
    ) -> CudaResult<HostAllocation<[E]>> {
        let challenge_offset = step + 1;
        let challenge_count = self.folding_steps - step - 1;
        assert_eq!(acc_size, 1usize << challenge_count);
        launch_build_eq_values(
            self.round_scratch.claim_point.as_ptr(),
            challenge_offset,
            challenge_count,
            self.round_scratch.eq_values.as_mut_ptr(),
            acc_size,
            context,
        )?;

        launch_weight_contributions(
            self.round_scratch.contributions.as_ptr(),
            self.kernel_plans.len(),
            self.round_scratch.eq_values.as_ptr(),
            self.round_scratch.weighted_rows.as_mut_ptr(),
            acc_size,
            context,
        )?;

        let weighted_rows = unsafe {
            DeviceSlice::from_raw_parts_mut(
                self.round_scratch.weighted_rows.as_mut_ptr(),
                acc_size * 2,
            )
        };
        let weighted_matrix = DeviceMatrix::new(weighted_rows, acc_size);
        let reduction_output = unsafe {
            DeviceSlice::from_raw_parts_mut(self.round_scratch.reduction_output.as_mut_ptr(), 2)
        };
        let reduction_temp = unsafe {
            DeviceSlice::from_raw_parts_mut(
                self.round_scratch.reduction_temp_storage.as_mut_ptr(),
                self.round_scratch.reduction_temp_storage.len(),
            )
        };
        batch_reduce(
            ReduceOperation::Sum,
            reduction_temp,
            &weighted_matrix,
            reduction_output,
            context.get_exec_stream(),
        )?;

        let mut reduction_host = unsafe { context.alloc_host_uninit_slice(2) };
        memory_copy_async(
            &mut reduction_host,
            &self.round_scratch.reduction_output,
            context.get_exec_stream(),
        )?;
        Ok(reduction_host)
    }

    fn schedule_device_values_readback_from_raw_ptr(
        &self,
        ptr: *const E,
        len: usize,
        context: &ProverContext,
    ) -> CudaResult<HostAllocation<[E]>> {
        let device = unsafe { DeviceSlice::from_raw_parts(ptr, len) };
        let mut host = unsafe { context.alloc_host_uninit_slice(len) };
        memory_copy_async(&mut host, device, context.get_exec_stream())?;
        Ok(host)
    }

    fn evaluate_with_two_variable_eq_ext(values: &[E; 4], r_before_last: E, r_last: E) -> E {
        let mut result = E::ZERO;

        let mut w00 = E::ONE;
        w00.sub_assign(&r_before_last);
        let mut tmp = E::ONE;
        tmp.sub_assign(&r_last);
        w00.mul_assign(&tmp);
        let mut term = values[0];
        term.mul_assign(&w00);
        result.add_assign(&term);

        let mut w01 = E::ONE;
        w01.sub_assign(&r_before_last);
        w01.mul_assign(&r_last);
        let mut term = values[1];
        term.mul_assign(&w01);
        result.add_assign(&term);

        let mut w10 = r_before_last;
        let mut tmp = E::ONE;
        tmp.sub_assign(&r_last);
        w10.mul_assign(&tmp);
        let mut term = values[2];
        term.mul_assign(&w10);
        result.add_assign(&term);

        let mut w11 = r_before_last;
        w11.mul_assign(&r_last);
        let mut term = values[3];
        term.mul_assign(&w11);
        result.add_assign(&term);

        result
    }

    fn final_evaluation_sources_for_last_step(
        &self,
        last_step: usize,
    ) -> BTreeMap<GKRAddress, *const E> {
        let mut result = BTreeMap::new();
        for kernel in self.kernel_plans.iter() {
            let sources = match last_step {
                1 => &kernel.round1_prepared.extension_field_inputs,
                2 => {
                    &kernel
                        .round2_prepared
                        .as_ref()
                        .expect("round 2 storage must be prepared")
                        .extension_field_inputs
                }
                step => {
                    &kernel
                        .round3_and_beyond_prepared
                        .iter()
                        .find(|prepared| prepared.step == step)
                        .unwrap_or_else(|| {
                            panic!("missing prepared round 3+ storage for step {step}")
                        })
                        .prepared
                        .extension_field_inputs
                }
            };
            for (address, source) in kernel.inputs.inputs_in_extension.iter().zip(sources.iter()) {
                if *address == GKRAddress::placeholder() || result.contains_key(address) {
                    continue;
                }
                result.insert(*address, source.this_layer_start.cast_const());
            }
        }

        result
    }

    fn schedule_last_evaluations_readback(
        &self,
        last_step: usize,
        context: &ProverContext,
    ) -> CudaResult<BTreeMap<GKRAddress, HostAllocation<[E]>>> {
        let mut result = BTreeMap::new();
        for (address, ptr) in self.final_evaluation_sources_for_last_step(last_step) {
            result.insert(
                address,
                self.schedule_device_values_readback_from_raw_ptr(ptr, 4, context)?,
            );
        }
        Ok(result)
    }

    pub(crate) fn schedule_execute_dimension_reducing_layer(
        &mut self,
        output_layer_claims: &BTreeMap<GKRAddress, E>,
        previous_claim_point: &[E],
        seed: Seed,
        _batch_challenge_base: E,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRDimensionReducingScheduledLayerExecution<B, E>> {
        assert_eq!(
            previous_claim_point.len(),
            self.folding_steps,
            "dimension-reducing claim point must match folding steps"
        );

        let last_step = self.folding_steps - 1;
        let mut round_challenge_buffers = Vec::with_capacity(last_step);
        for len in 1..=last_step {
            round_challenge_buffers.push(unsafe { context.alloc_host_uninit_slice(len) });
        }
        let claim_point_host = alloc_host_and_copy(context, previous_claim_point);
        memory_copy_async(
            &mut self.round_scratch.claim_point,
            &claim_point_host,
            context.get_exec_stream(),
        )?;

        let shared_state = Arc::new(Mutex::new(ScheduledDimensionReducingLayerExecutionState {
            seed,
            claim: self.compute_combined_claim(output_layer_claims),
            eq_prefactor: E::ONE,
            folding_challenges: Vec::with_capacity(self.folding_steps + 1),
            internal_round_coefficients: Vec::with_capacity(self.folding_steps - 1),
            result: None,
        }));
        let mut round_states = Vec::with_capacity(last_step.saturating_sub(1) + 1);
        let mut reduction_states = Vec::with_capacity(last_step);

        for step in 0..last_step {
            let acc_size = 1usize << (self.folding_steps - step - 1);
            if step == 0 {
                self.launch_round0_kernels(acc_size, context)?;
            } else {
                let mut callbacks = Callbacks::new();
                match step {
                    1 => {
                        let scheduled = self.schedule_round_1(
                            round_challenge_buffers[step - 1].get_accessor(),
                            &mut callbacks,
                            context,
                        )?;
                        self.launch_round1_kernels(&scheduled, acc_size, false, context)?;
                        round_states.push(ScheduledDimensionReducingRoundState::Round1 {
                            callbacks,
                            scheduled,
                        });
                    }
                    2 => {
                        let scheduled = self.schedule_round_2(
                            round_challenge_buffers[step - 1].get_accessor(),
                            &mut callbacks,
                            context,
                        )?;
                        self.launch_round2_kernels(&scheduled, acc_size, false, context)?;
                        round_states.push(ScheduledDimensionReducingRoundState::Round2 {
                            callbacks,
                            scheduled,
                        });
                    }
                    _ => {
                        let scheduled = self.schedule_round_3_and_beyond(
                            step,
                            round_challenge_buffers[step - 1].get_accessor(),
                            &mut callbacks,
                            context,
                        )?;
                        self.launch_round3_kernels(&scheduled, acc_size, false, context)?;
                        round_states.push(ScheduledDimensionReducingRoundState::Round3AndBeyond {
                            callbacks,
                            scheduled,
                        });
                    }
                }
            }

            let reduction_output =
                self.schedule_round_coefficients_reduction(step, acc_size, context)?;
            let reduction_accessor = reduction_output.get_accessor();
            let next_round_challenges = if step < last_step {
                Some(round_challenge_buffers[step].get_mut_accessor())
            } else {
                None
            };
            let shared_state_for_callback = Arc::clone(&shared_state);
            let previous_claim_coord = previous_claim_point[step];
            let mut callbacks = Callbacks::new();
            callbacks.schedule(
                move || unsafe {
                    let reduction = reduction_accessor.get();
                    let c0 = reduction[0];
                    let c2 = reduction[1];
                    let mut state = shared_state_for_callback.lock().unwrap();
                    let mut normalized_claim = state.claim;
                    normalized_claim.mul_assign(
                        &state
                            .eq_prefactor
                            .inverse()
                            .expect("eq prefactor must be non-zero"),
                    );
                    let coeffs = output_univariate_monomial_form_max_quadratic::<BF, E>(
                        previous_claim_coord,
                        normalized_claim,
                        c0,
                        c2,
                    );
                    commit_field_els(&mut state.seed, &coeffs);
                    state.internal_round_coefficients.push(coeffs);

                    let folding_challenge = draw_random_field_els::<BF, E>(&mut state.seed, 1)[0];
                    state.claim =
                        evaluate_small_univariate_poly::<BF, E, _>(&coeffs, &folding_challenge);
                    state.eq_prefactor =
                        evaluate_eq_poly::<BF, E>(&folding_challenge, &previous_claim_coord);
                    state.folding_challenges.push(folding_challenge);
                    if let Some(next_round_challenges) = next_round_challenges {
                        next_round_challenges.get_mut()[..state.folding_challenges.len()]
                            .copy_from_slice(&state.folding_challenges);
                    }
                },
                context.get_exec_stream(),
            )?;
            reduction_states.push(ScheduledDimensionReducingReductionState {
                callbacks,
                reduction_output,
            });
        }

        let mut final_round_callbacks = Callbacks::new();
        let final_round_state = match last_step {
            1 => {
                let scheduled = self.schedule_round_1(
                    round_challenge_buffers[last_step - 1].get_accessor(),
                    &mut final_round_callbacks,
                    context,
                )?;
                self.launch_round1_kernels(&scheduled, 1, true, context)?;
                ScheduledDimensionReducingRoundState::Round1 {
                    callbacks: final_round_callbacks,
                    scheduled,
                }
            }
            2 => {
                let scheduled = self.schedule_round_2(
                    round_challenge_buffers[last_step - 1].get_accessor(),
                    &mut final_round_callbacks,
                    context,
                )?;
                self.launch_round2_kernels(&scheduled, 1, true, context)?;
                ScheduledDimensionReducingRoundState::Round2 {
                    callbacks: final_round_callbacks,
                    scheduled,
                }
            }
            step => {
                let scheduled = self.schedule_round_3_and_beyond(
                    step,
                    round_challenge_buffers[last_step - 1].get_accessor(),
                    &mut final_round_callbacks,
                    context,
                )?;
                self.launch_round3_kernels(&scheduled, 1, true, context)?;
                ScheduledDimensionReducingRoundState::Round3AndBeyond {
                    callbacks: final_round_callbacks,
                    scheduled,
                }
            }
        };
        let final_evaluations = self.schedule_last_evaluations_readback(last_step, context)?;
        let final_evaluation_accessors: Vec<_> = final_evaluations
            .iter()
            .map(|(addr, values)| (*addr, values.get_accessor()))
            .collect();
        let shared_state_for_callback = Arc::clone(&shared_state);
        let folding_steps = self.folding_steps;
        let mut final_readback_callbacks = Callbacks::new();
        final_readback_callbacks.schedule(
            move || unsafe {
                let mut last_evaluations = BTreeMap::new();
                for (address, accessor) in final_evaluation_accessors.iter() {
                    let values: [E; 4] = accessor.get().try_into().unwrap();
                    last_evaluations.insert(*address, values);
                }

                let transcript_inputs: Vec<E> = last_evaluations
                    .values()
                    .flat_map(|values| values.iter().copied())
                    .collect();
                let mut state = shared_state_for_callback.lock().unwrap();
                commit_field_els(&mut state.seed, &transcript_inputs);

                let challenges = draw_random_field_els::<BF, E>(&mut state.seed, 3);
                let [r_before_last, r_last, next_batching_challenge]: [E; 3] =
                    challenges.try_into().unwrap();
                let mut new_claim_point = state.folding_challenges.clone();
                new_claim_point.push(r_before_last);
                new_claim_point.push(r_last);

                let new_claims = last_evaluations
                    .iter()
                    .map(|(addr, values)| {
                        (
                            *addr,
                            Self::evaluate_with_two_variable_eq_ext(values, r_before_last, r_last),
                        )
                    })
                    .collect();

                let proof = SumcheckIntermediateProofValues::<BF, E> {
                    sumcheck_num_rounds: folding_steps,
                    internal_round_coefficients: state.internal_round_coefficients.clone(),
                    final_step_evaluations: last_evaluations
                        .iter()
                        .map(|(addr, values)| (*addr, values.to_vec()))
                        .collect(),
                    _marker: core::marker::PhantomData,
                };

                state.result = Some(GpuGKRDimensionReducingLayerExecution {
                    proof,
                    new_claims,
                    new_claim_point,
                    next_batching_challenge,
                    updated_seed: state.seed,
                });
            },
            context.get_exec_stream(),
        )?;

        Ok(GpuGKRDimensionReducingScheduledLayerExecution {
            claim_point_host,
            round_challenge_buffers,
            round_states: {
                let mut states = round_states;
                states.push(final_round_state);
                states
            },
            reduction_states,
            final_readback: ScheduledDimensionReducingFinalReadback {
                callbacks: final_readback_callbacks,
                evaluations: final_evaluations,
            },
            shared_state,
        })
    }
}

impl<B, E: FieldExtension<BF> + Field> GpuGKRDimensionReducingScheduledLayerExecution<B, E> {
    pub(crate) fn into_execution(self) -> GpuGKRDimensionReducingLayerExecution<E> {
        self.shared_state
            .lock()
            .unwrap()
            .result
            .take()
            .expect("dimension-reducing layer execution is not ready yet")
    }
}

#[cfg(test)]
mod tests {
    use super::{
        build_dimension_reducing_kernel_blueprints, launch_build_eq_values,
        launch_lookup_continuation, launch_lookup_round0, launch_pairwise_continuation,
        launch_pairwise_round0, launch_weight_contributions,
    };
    use crate::allocator::tracker::AllocationPlacement;
    use crate::ops::cub::device_reduce::{
        batch_reduce, get_batch_reduce_temp_storage_bytes, ReduceOperation,
    };
    use crate::primitives::context::{DeviceAllocation, ProverContext};
    use crate::primitives::device_structures::DeviceMatrix;
    use crate::primitives::field::{BF, E4};
    use crate::prover::gkr::{
        GpuBaseFieldPolySource, GpuExtensionFieldPolyContinuingLaunchDescriptor,
        GpuExtensionFieldPolyInitialSource, GpuSumcheckRound0DeviceLaunchDescriptors,
        GpuSumcheckRound0HostLaunchDescriptors, GpuSumcheckRound0ScheduledLaunchDescriptors,
    };
    use crate::prover::test_utils::make_test_context;
    use cs::gkr_compiler::OutputType;
    use era_cudart::memory::{memory_copy, memory_copy_async};
    use era_cudart::slice::{CudaSlice, CudaSliceMut, DeviceSlice};
    use field::Field;
    use prover::gkr::prover::dimension_reduction::forward::DimensionReducingInputOutput;
    use serial_test::serial;
    use std::collections::BTreeMap;

    fn sample_ext(seed: u32) -> E4 {
        E4::from_array_of_base([
            BF::new(seed),
            BF::new(seed + 1),
            BF::new(seed + 2),
            BF::new(seed + 3),
        ])
    }

    fn successive_powers<E: Field>(base: E, count: usize) -> Vec<E> {
        let mut current = E::ONE;
        (0..count)
            .map(|_| {
                let result = current;
                current.mul_assign(&base);
                result
            })
            .collect()
    }

    fn alloc_and_copy<T: Copy>(context: &ProverContext, values: &[T]) -> DeviceAllocation<T> {
        let mut allocation = context
            .alloc(values.len(), AllocationPlacement::BestFit)
            .unwrap();
        memory_copy(&mut allocation, values).unwrap();
        allocation
    }

    #[test]
    fn dimension_reducing_kernel_blueprints_match_cpu_order_and_challenges() {
        let layer = BTreeMap::from([
            (
                OutputType::PermutationProduct,
                DimensionReducingInputOutput {
                    inputs: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 0,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 1,
                        },
                    ],
                    output: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 0,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 1,
                        },
                    ],
                },
            ),
            (
                OutputType::Lookup16Bits,
                DimensionReducingInputOutput {
                    inputs: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 2,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 3,
                        },
                    ],
                    output: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 2,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 3,
                        },
                    ],
                },
            ),
            (
                OutputType::LookupTimestamps,
                DimensionReducingInputOutput {
                    inputs: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 4,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 5,
                        },
                    ],
                    output: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 4,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 5,
                        },
                    ],
                },
            ),
            (
                OutputType::GenericLookup,
                DimensionReducingInputOutput {
                    inputs: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 6,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 10,
                            offset: 7,
                        },
                    ],
                    output: vec![
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 6,
                        },
                        cs::definitions::GKRAddress::InnerLayer {
                            layer: 11,
                            offset: 7,
                        },
                    ],
                },
            ),
        ]);

        let batch_challenge_base = sample_ext(10);
        let blueprints = build_dimension_reducing_kernel_blueprints(&layer, batch_challenge_base);
        let powers = successive_powers(batch_challenge_base, 8);

        assert_eq!(blueprints.len(), 5);
        assert_eq!(
            blueprints[0].inputs.inputs_in_extension,
            vec![layer[&OutputType::PermutationProduct].inputs[0]]
        );
        assert_eq!(
            blueprints[0].inputs.outputs_in_extension,
            vec![layer[&OutputType::PermutationProduct].output[0]]
        );
        assert_eq!(blueprints[0].batch_challenges, vec![powers[0]]);

        assert_eq!(
            blueprints[1].inputs.inputs_in_extension,
            vec![layer[&OutputType::PermutationProduct].inputs[1]]
        );
        assert_eq!(
            blueprints[1].inputs.outputs_in_extension,
            vec![layer[&OutputType::PermutationProduct].output[1]]
        );
        assert_eq!(blueprints[1].batch_challenges, vec![powers[1]]);

        assert_eq!(
            blueprints[2].inputs.inputs_in_extension,
            layer[&OutputType::Lookup16Bits].inputs
        );
        assert_eq!(
            blueprints[2].inputs.outputs_in_extension,
            layer[&OutputType::Lookup16Bits].output
        );
        assert_eq!(blueprints[2].batch_challenges, vec![powers[2], powers[3]]);

        assert_eq!(
            blueprints[3].inputs.inputs_in_extension,
            layer[&OutputType::LookupTimestamps].inputs
        );
        assert_eq!(
            blueprints[3].inputs.outputs_in_extension,
            layer[&OutputType::LookupTimestamps].output
        );
        assert_eq!(blueprints[3].batch_challenges, vec![powers[4], powers[5]]);

        assert_eq!(
            blueprints[4].inputs.inputs_in_extension,
            layer[&OutputType::GenericLookup].inputs
        );
        assert_eq!(
            blueprints[4].inputs.outputs_in_extension,
            layer[&OutputType::GenericLookup].output
        );
        assert_eq!(blueprints[4].batch_challenges, vec![powers[6], powers[7]]);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn pairwise_round0_kernel_matches_cpu() {
        let context = make_test_context(64, 8);
        let input_values = (0..8).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let output_values = (0..4).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
        let batch_challenge = sample_ext(200);
        let input = alloc_and_copy(&context, &input_values);
        let output = alloc_and_copy(&context, &output_values);
        let mut contributions = alloc_and_copy(&context, &[E4::ZERO; 4]);

        let mut round0 = GpuSumcheckRound0ScheduledLaunchDescriptors {
            host: GpuSumcheckRound0HostLaunchDescriptors {
                base_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(0)
                },
                extension_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(1)
                },
                base_field_outputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(0)
                },
                extension_field_outputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(1)
                },
            },
            device: GpuSumcheckRound0DeviceLaunchDescriptors {
                base_field_inputs: context
                    .alloc::<GpuBaseFieldPolySource<BF>>(0, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_inputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(1, AllocationPlacement::Top)
                    .unwrap(),
                base_field_outputs: context
                    .alloc::<GpuBaseFieldPolySource<BF>>(0, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_outputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(1, AllocationPlacement::Top)
                    .unwrap(),
            },
        };
        unsafe {
            round0
                .host
                .extension_field_inputs
                .get_mut_accessor()
                .get_mut()[0] = GpuExtensionFieldPolyInitialSource {
                start: input.as_ptr(),
                next_layer_size: 4,
            };
            round0
                .host
                .extension_field_outputs
                .get_mut_accessor()
                .get_mut()[0] = GpuExtensionFieldPolyInitialSource {
                start: output.as_ptr(),
                next_layer_size: 2,
            };
        }
        memory_copy_async(
            &mut round0.device.extension_field_inputs,
            &round0.host.extension_field_inputs,
            context.get_exec_stream(),
        )
        .unwrap();
        memory_copy_async(
            &mut round0.device.extension_field_outputs,
            &round0.host.extension_field_outputs,
            context.get_exec_stream(),
        )
        .unwrap();

        launch_pairwise_round0::<E4>(
            &round0,
            batch_challenge,
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();

        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy(&mut host, &contributions).unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let mut expected = Vec::new();
        for output_index in 0..2 {
            let index = output_index * 2;
            let mut c0 = batch_challenge;
            c0.mul_assign(&output_values[output_index]);
            let mut a = input_values[4 + index];
            a.sub_assign(&input_values[index]);
            let mut b = input_values[4 + index + 1];
            b.sub_assign(&input_values[index + 1]);
            let mut c1 = a;
            c1.mul_assign(&b);
            c1.mul_assign(&batch_challenge);
            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn lookup_round0_kernel_matches_cpu() {
        let context = make_test_context(64, 8);
        let input0_values = (0..8).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let input1_values = (0..8).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
        let output_num_values = (0..4).map(|i| sample_ext(200 + i)).collect::<Vec<_>>();
        let output_den_values = (0..4).map(|i| sample_ext(300 + i)).collect::<Vec<_>>();
        let input0 = alloc_and_copy(&context, &input0_values);
        let input1 = alloc_and_copy(&context, &input1_values);
        let output_num = alloc_and_copy(&context, &output_num_values);
        let output_den = alloc_and_copy(&context, &output_den_values);
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();
        let batch0 = sample_ext(400);
        let batch1 = sample_ext(500);

        let mut round0 = GpuSumcheckRound0ScheduledLaunchDescriptors {
            host: GpuSumcheckRound0HostLaunchDescriptors {
                base_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(0)
                },
                extension_field_inputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(2)
                },
                base_field_outputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuBaseFieldPolySource<BF>>(0)
                },
                extension_field_outputs: unsafe {
                    context.alloc_host_uninit_slice::<GpuExtensionFieldPolyInitialSource<E4>>(2)
                },
            },
            device: GpuSumcheckRound0DeviceLaunchDescriptors {
                base_field_inputs: context
                    .alloc::<GpuBaseFieldPolySource<BF>>(0, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_inputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(2, AllocationPlacement::Top)
                    .unwrap(),
                base_field_outputs: context
                    .alloc::<GpuBaseFieldPolySource<BF>>(0, AllocationPlacement::Top)
                    .unwrap(),
                extension_field_outputs: context
                    .alloc::<GpuExtensionFieldPolyInitialSource<E4>>(2, AllocationPlacement::Top)
                    .unwrap(),
            },
        };
        unsafe {
            round0
                .host
                .extension_field_inputs
                .get_mut_accessor()
                .get_mut()[0] = GpuExtensionFieldPolyInitialSource {
                start: input0.as_ptr(),
                next_layer_size: 4,
            };
            round0
                .host
                .extension_field_inputs
                .get_mut_accessor()
                .get_mut()[1] = GpuExtensionFieldPolyInitialSource {
                start: input1.as_ptr(),
                next_layer_size: 4,
            };
            round0
                .host
                .extension_field_outputs
                .get_mut_accessor()
                .get_mut()[0] = GpuExtensionFieldPolyInitialSource {
                start: output_num.as_ptr(),
                next_layer_size: 2,
            };
            round0
                .host
                .extension_field_outputs
                .get_mut_accessor()
                .get_mut()[1] = GpuExtensionFieldPolyInitialSource {
                start: output_den.as_ptr(),
                next_layer_size: 2,
            };
        }
        memory_copy_async(
            &mut round0.device.extension_field_inputs,
            &round0.host.extension_field_inputs,
            context.get_exec_stream(),
        )
        .unwrap();
        memory_copy_async(
            &mut round0.device.extension_field_outputs,
            &round0.host.extension_field_outputs,
            context.get_exec_stream(),
        )
        .unwrap();

        launch_lookup_round0::<E4>(
            &round0,
            &[batch0, batch1],
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();

        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy(&mut host, &contributions).unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let mut expected = Vec::new();
        for output_index in 0..2 {
            let index = output_index * 2;
            let pair_index = index + 1;

            let mut a = input0_values[4 + index];
            a.sub_assign(&input0_values[index]);
            let mut b = input1_values[4 + index];
            b.sub_assign(&input1_values[index]);
            let mut c = input0_values[4 + pair_index];
            c.sub_assign(&input0_values[pair_index]);
            let mut d = input1_values[4 + pair_index];
            d.sub_assign(&input1_values[pair_index]);

            let mut num = a;
            num.mul_assign(&d);
            let mut t = c;
            t.mul_assign(&b);
            num.add_assign(&t);

            let mut den = b;
            den.mul_assign(&d);

            let mut c0 = batch0;
            c0.mul_assign(&output_num_values[output_index]);
            let mut output_den_term = batch1;
            output_den_term.mul_assign(&output_den_values[output_index]);
            c0.add_assign(&output_den_term);

            let mut c1 = batch0;
            c1.mul_assign(&num);
            let mut den_term = batch1;
            den_term.mul_assign(&den);
            c1.add_assign(&den_term);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn lookup_continuation_kernel_matches_cpu() {
        let context = make_test_context(64, 8);
        let prev0 = (0..16).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let prev1 = (0..16).map(|i| sample_ext(100 + i)).collect::<Vec<_>>();
        let challenge = sample_ext(300);
        let batch0 = sample_ext(400);
        let batch1 = sample_ext(500);
        let prev0_dev = alloc_and_copy(&context, &prev0);
        let prev1_dev = alloc_and_copy(&context, &prev1);
        let cache0: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();
        let cache1: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();
        let descriptors = [
            GpuExtensionFieldPolyContinuingLaunchDescriptor {
                previous_layer_start: prev0_dev.as_ptr(),
                this_layer_start: cache0.as_ptr().cast_mut(),
                this_layer_size: 8,
                next_layer_size: 4,
                folding_challenge: challenge,
                first_access: true,
            },
            GpuExtensionFieldPolyContinuingLaunchDescriptor {
                previous_layer_start: prev1_dev.as_ptr(),
                this_layer_start: cache1.as_ptr().cast_mut(),
                this_layer_size: 8,
                next_layer_size: 4,
                folding_challenge: challenge,
                first_access: true,
            },
        ];
        let descriptors_dev = alloc_and_copy(&context, &descriptors);
        let contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        launch_lookup_continuation::<E4>(
            descriptors_dev.as_ptr(),
            &[batch0, batch1],
            false,
            contributions.as_ptr().cast_mut(),
            2,
            &context,
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();

        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy(&mut host, &contributions).unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let fold = |values: &[E4], idx: usize| {
            let mut delta = values[8 + idx];
            delta.sub_assign(&values[idx]);
            let mut result = challenge;
            result.mul_assign(&delta);
            result.add_assign(&values[idx]);
            result
        };
        let mut expected = Vec::new();
        for output_index in 0..2 {
            let idx = output_index * 2;
            let a0 = fold(&prev0, idx);
            let a1 = fold(&prev0, idx + 4);
            let mut da = a1;
            da.sub_assign(&a0);
            let b0 = fold(&prev1, idx);
            let b1 = fold(&prev1, idx + 4);
            let mut db = b1;
            db.sub_assign(&b0);

            let c0 = fold(&prev0, idx + 1);
            let c1 = fold(&prev0, idx + 5);
            let mut dc = c1;
            dc.sub_assign(&c0);
            let d0 = fold(&prev1, idx + 1);
            let d1 = fold(&prev1, idx + 5);
            let mut dd = d1;
            dd.sub_assign(&d0);

            let mut num = da;
            num.mul_assign(&dd);
            let mut t = dc;
            t.mul_assign(&db);
            num.add_assign(&t);

            let mut den = db;
            den.mul_assign(&dd);

            let mut e0 = batch0;
            e0.mul_assign(&num);
            let mut e1 = batch1;
            e1.mul_assign(&den);
            e0.add_assign(&e1);

            expected.push(E4::ZERO);
            expected.push(e0);
        }

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn pairwise_continuation_kernel_matches_cpu() {
        let context = make_test_context(64, 8);
        let prev = (0..16).map(|i| sample_ext(10 + i)).collect::<Vec<_>>();
        let challenge = sample_ext(300);
        let batch = sample_ext(400);
        let prev_dev = alloc_and_copy(&context, &prev);
        let cache: DeviceAllocation<E4> = context.alloc(8, AllocationPlacement::Top).unwrap();
        let descriptors = [GpuExtensionFieldPolyContinuingLaunchDescriptor {
            previous_layer_start: prev_dev.as_ptr(),
            this_layer_start: cache.as_ptr().cast_mut(),
            this_layer_size: 8,
            next_layer_size: 4,
            folding_challenge: challenge,
            first_access: true,
        }];
        let descriptors_dev = alloc_and_copy(&context, &descriptors);
        let mut contributions: DeviceAllocation<E4> =
            context.alloc(4, AllocationPlacement::Top).unwrap();

        launch_pairwise_continuation::<E4>(
            descriptors_dev.as_ptr(),
            batch,
            false,
            contributions.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();

        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy(&mut host, &contributions).unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let fold = |values: &[E4], idx: usize| {
            let mut delta = values[8 + idx];
            delta.sub_assign(&values[idx]);
            let mut result = challenge;
            result.mul_assign(&delta);
            result.add_assign(&values[idx]);
            result
        };

        let mut expected = Vec::new();
        for output_index in 0..2 {
            let idx = output_index * 2;
            let even0 = fold(&prev, idx);
            let even1 = fold(&prev, idx + 4);
            let mut even_delta = even1;
            even_delta.sub_assign(&even0);

            let odd0 = fold(&prev, idx + 1);
            let odd1 = fold(&prev, idx + 5);
            let mut odd_delta = odd1;
            odd_delta.sub_assign(&odd0);

            let mut c0 = even0;
            c0.mul_assign(&odd0);
            c0.mul_assign(&batch);

            let mut c1 = even_delta;
            c1.mul_assign(&odd_delta);
            c1.mul_assign(&batch);

            expected.push(c0);
            expected.push(c1);
        }

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn weight_contributions_and_reduce_match_cpu() {
        let context = make_test_context(64, 8);
        let contributions = vec![
            sample_ext(10),
            sample_ext(11),
            sample_ext(12),
            sample_ext(13),
            sample_ext(20),
            sample_ext(21),
            sample_ext(22),
            sample_ext(23),
        ];
        let eq = vec![sample_ext(30), sample_ext(31)];
        let contributions_dev = alloc_and_copy(&context, &contributions);
        let eq_dev = alloc_and_copy(&context, &eq);
        let mut weighted_rows = context.alloc(4, AllocationPlacement::Top).unwrap();

        launch_weight_contributions::<E4>(
            contributions_dev.as_ptr(),
            2,
            eq_dev.as_ptr(),
            weighted_rows.as_mut_ptr(),
            2,
            &context,
        )
        .unwrap();

        let temp_bytes =
            get_batch_reduce_temp_storage_bytes::<E4>(ReduceOperation::Sum, 2, 2).unwrap();
        let mut temp = context.alloc(temp_bytes, AllocationPlacement::Top).unwrap();
        let mut reduced = context.alloc(2, AllocationPlacement::Top).unwrap();
        let weighted_rows_slice =
            unsafe { DeviceSlice::from_raw_parts(weighted_rows.as_ptr(), weighted_rows.len()) };
        let weighted_matrix = DeviceMatrix::new(weighted_rows_slice, 2);
        let temp_slice = unsafe { DeviceSlice::from_raw_parts_mut(temp.as_mut_ptr(), temp.len()) };
        let reduced_slice =
            unsafe { DeviceSlice::from_raw_parts_mut(reduced.as_mut_ptr(), reduced.len()) };
        batch_reduce(
            ReduceOperation::Sum,
            temp_slice,
            &weighted_matrix,
            reduced_slice,
            context.get_exec_stream(),
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();

        let mut host = unsafe { context.alloc_host_uninit_slice(2) };
        memory_copy(&mut host, &reduced).unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let mut expected = [E4::ZERO; 2];
        for row in 0..2 {
            let mut row0 = contributions[row * 2];
            row0.add_assign(&contributions[4 + row * 2]);
            row0.mul_assign(&eq[row]);
            expected[0].add_assign(&row0);

            let mut row1 = contributions[row * 2 + 1];
            row1.add_assign(&contributions[4 + row * 2 + 1]);
            row1.mul_assign(&eq[row]);
            expected[1].add_assign(&row1);
        }

        assert_eq!(actual, expected);
    }

    #[test]
    #[cfg(not(no_cuda))]
    #[serial]
    fn build_eq_values_matches_cpu() {
        let context = make_test_context(64, 8);
        let claim_point = vec![
            sample_ext(40),
            sample_ext(50),
            sample_ext(60),
            sample_ext(70),
        ];
        let claim_point_dev = alloc_and_copy(&context, &claim_point);
        let mut eq_values = context.alloc(4, AllocationPlacement::Top).unwrap();

        launch_build_eq_values::<E4>(
            claim_point_dev.as_ptr(),
            1,
            2,
            eq_values.as_mut_ptr(),
            4,
            &context,
        )
        .unwrap();
        context.get_exec_stream().synchronize().unwrap();

        let mut host = unsafe { context.alloc_host_uninit_slice(4) };
        memory_copy(&mut host, &eq_values).unwrap();
        let actual = unsafe { host.get_accessor().get().to_vec() };

        let r0 = claim_point[1];
        let r1 = claim_point[2];
        let mut one_minus_r0 = E4::ONE;
        one_minus_r0.sub_assign(&r0);
        let mut one_minus_r1 = E4::ONE;
        one_minus_r1.sub_assign(&r1);

        let mut expected_00 = one_minus_r0;
        expected_00.mul_assign(&one_minus_r1);
        let mut expected_01 = one_minus_r0;
        expected_01.mul_assign(&r1);
        let mut expected_10 = r0;
        expected_10.mul_assign(&one_minus_r1);
        let mut expected_11 = r0;
        expected_11.mul_assign(&r1);

        let expected = vec![expected_00, expected_01, expected_10, expected_11];

        assert_eq!(actual, expected);
    }
}
