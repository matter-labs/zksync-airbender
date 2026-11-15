use std::{collections::BTreeMap, sync::Arc};

use era_cudart::{result::CudaResult, slice::DeviceSlice};
use gpu_core::primitives::{context::DeviceAllocation, device_tracing::Range};
use gpu_prover_context::ProverContext;

pub(crate) use crate::forward::dimension_reducing::{
    prepare_dimension_reduction_forward, schedule_prepared_dimension_reduction_forward,
    PreparedDimensionReductionForward,
};
pub(super) use crate::forward::kernels::*;
use crate::{
    upstream::{DimensionReducingInputOutput, Field, GKRAddress, OutputType},
    GpuExtensionFieldPoly, GpuGKRLayerSource, GpuGKRStorage,
};

pub struct GpuGKRForwardOutput<B, E> {
    pub(crate) tracing_ranges: Vec<Range>,
    pub(crate) storage: GpuGKRStorage<B, E>,
    pub initial_layer_for_sumcheck: usize,
    pub dimension_reducing_inputs:
        BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>>,
}

pub struct GpuGKRTranscriptHandoff<E> {
    flat_evaluations_backing: Arc<DeviceAllocation<E>>,
    flat_total_len: usize,
}

pub struct ForwardOutputSlabTarget<E> {
    pub backing: Arc<DeviceAllocation<E>>,
    pub len: usize,
}

impl<B, E> GpuGKRForwardOutput<B, E> {
    pub(crate) fn new(
        tracing_ranges: Vec<Range>,
        storage: GpuGKRStorage<B, E>,
        initial_layer_for_sumcheck: usize,
        dimension_reducing_inputs: BTreeMap<
            usize,
            BTreeMap<OutputType, DimensionReducingInputOutput>,
        >,
    ) -> Self {
        Self {
            tracing_ranges,
            storage,
            initial_layer_for_sumcheck,
            dimension_reducing_inputs,
        }
    }
    pub(crate) fn into_parts(
        self,
    ) -> (
        Vec<Range>,
        GpuGKRStorage<B, E>,
        usize,
        BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>>,
    ) {
        (
            self.tracing_ranges,
            self.storage,
            self.initial_layer_for_sumcheck,
            self.dimension_reducing_inputs,
        )
    }
}

impl<E> GpuGKRTranscriptHandoff<E> {
    pub fn device_flat_evaluations(&self) -> &DeviceSlice<E> {
        &self.flat_evaluations_backing[..self.flat_total_len]
    }
}

impl<B, E: Copy> GpuGKRForwardOutput<B, E> {
    pub fn transcript_handoff(&self) -> GpuGKRTranscriptHandoff<E> {
        let reduced_outputs = self
            .dimension_reducing_inputs
            .get(&self.initial_layer_for_sumcheck)
            .expect("reduced outputs for initial sumcheck layer must exist");

        let output_layer = self.initial_layer_for_sumcheck + 1;
        let class = super::gkr_address_audit::AddressClass::ThisLayerInnerLayerWrite;
        let flat_evaluations_backing: Arc<DeviceAllocation<E>> = Arc::clone(
            self.storage
                .layers
                .get(output_layer)
                .and_then(|layer| layer.ext_class_backings.get(&class))
                .expect(
                    "consolidated backing Arc for reduced-output polys must exist after the \
                     forward dim-reduction pass",
                ),
        );

        let mut flat_total_len = 0usize;
        for reduced_io in reduced_outputs.values() {
            let [first_addr, second_addr]: [GKRAddress; 2] = reduced_io
                .output
                .clone()
                .try_into()
                .expect("transcript handoff expects exactly two reduced outputs per type");
            for addr in [first_addr, second_addr] {
                let poly = self
                    .storage
                    .try_get_ext_poly(addr)
                    .unwrap_or_else(|| panic!("missing reduced extension poly for {:?}", addr));
                flat_total_len += poly.len();
            }
        }
        assert!(
            flat_total_len <= flat_evaluations_backing.len(),
            "consolidated backing must contain the reduced-output poly prefix"
        );

        GpuGKRTranscriptHandoff {
            flat_evaluations_backing,
            flat_total_len,
        }
    }
}
pub(crate) mod dimension_reducing;

pub(crate) mod kernels;

pub(crate) mod vm;
