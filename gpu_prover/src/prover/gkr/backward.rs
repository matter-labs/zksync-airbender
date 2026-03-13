use std::collections::{BTreeMap, VecDeque};

use cs::definitions::GKRAddress;
use cs::gkr_compiler::OutputType;
use era_cudart::result::CudaResult;
use field::Field;
use prover::gkr::prover::dimension_reduction::forward::DimensionReducingInputOutput;
use prover::gkr::sumcheck::evaluation_kernels::GKRInputs;

use super::forward::GpuGKRForwardScratch;
use super::{
    GpuGKRStorage, GpuSumcheckRound0ScheduledLaunchDescriptors, GpuSumcheckRound1PreparedStorage,
    GpuSumcheckRound1ScheduledLaunchDescriptors, GpuSumcheckRound2PreparedStorage,
    GpuSumcheckRound2ScheduledLaunchDescriptors, GpuSumcheckRound3AndBeyondPreparedStorage,
    GpuSumcheckRound3AndBeyondScheduledLaunchDescriptors,
};
use crate::primitives::callbacks::Callbacks;
use crate::primitives::context::{ProverContext, UnsafeAccessor};
use crate::primitives::device_tracing::Range;

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

impl<B, E: Field> GpuGKRDimensionReducingBackwardState<B, E> {
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

        self.next_trace_len_after_reduction *= 2;

        Ok(Some(GpuGKRDimensionReducingSumcheckLayerPlan {
            layer_idx,
            trace_len_after_reduction,
            folding_steps,
            kernel_plans,
            round0_descriptors,
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

#[cfg(test)]
mod tests {
    use super::build_dimension_reducing_kernel_blueprints;
    use crate::primitives::field::{BF, E4};
    use cs::gkr_compiler::OutputType;
    use field::Field;
    use prover::gkr::prover::dimension_reduction::forward::DimensionReducingInputOutput;
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
}
