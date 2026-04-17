use std::collections::BTreeMap;
use std::mem::ManuallyDrop;
use std::ops::DerefMut;
use std::ptr::null;

use cs::definitions::{
    gkr::{RamWordRepresentation, DECODER_LOOKUP_FORMAL_SET_INDEX},
    GKRAddress, MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_HIGH_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_ADDRESS_LOW_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_HIGH_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_TIMESTAMP_LOW_IDX, MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_HIGH_IDX,
    MEM_ARGUMENT_CHALLENGE_POWERS_VALUE_LOW_IDX,
};
use cs::gkr_compiler::{
    CompiledAddressSpaceRelationStrict, CompiledAddressStrict, GKRCircuitArtifact,
    GKRLayerDescription, NoFieldGKRCacheRelation, NoFieldGKRRelation, OutputType,
};
use era_cudart::execution::{CudaLaunchConfig, KernelFunction};
use era_cudart::memory::memory_copy_async;
use era_cudart::paste::paste;
use era_cudart::result::CudaResult;
use era_cudart::{cuda_kernel_declaration, cuda_kernel_signature_arguments_and_function};
use field::{Field, FieldExtension, PrimeField};
use prover::gkr::prover::dimension_reduction::forward::DimensionReducingInputOutput;
use prover::gkr::prover::GKRExternalChallenges;

use super::backward::GpuGKRDimensionReducingBackwardState;
use super::forward::schedule_ext_poly_readback;
use super::setup::{GpuGKRForwardSetup, GpuGKRSetupTransfer};
use super::stage1::GpuGKRStage1Output;
use super::{GpuBaseFieldPoly, GpuBaseFieldSourceKind, GpuExtensionFieldPoly, GpuGKRStorage};
use crate::allocator::tracker::AllocationPlacement;
use crate::ops::simple::{
    add_into_y, mul_into_y, set_by_ref, set_by_val, sub_into_x, Add, BinaryOp, Mul, SetByRef,
    SetByVal, Sub,
};
use crate::primitives::context::{DeviceAllocation, HostAllocation, ProverContext, UnsafeAccessor};
use crate::primitives::device_structures::DeviceVectorChunk;
use crate::primitives::device_tracing::Range;
use crate::primitives::field::{BF, E4};
use crate::primitives::utils::{get_grid_block_dims_for_threads_count, WARP_SIZE};

pub(crate) struct GpuGKRForwardOutput<B, E> {
    pub(super) tracing_ranges: Vec<Range>,
    pub(crate) storage: GpuGKRStorage<B, E>,
    pub(crate) initial_layer_for_sumcheck: usize,
    pub(crate) dimension_reducing_inputs:
        BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>>,
}

pub(crate) struct GpuGKRTranscriptHandoff<E> {
    pub(super) _tracing_ranges: Vec<Range>,
    pub(super) explicit_evaluations: BTreeMap<OutputType, [HostAllocation<[E]>; 2]>,
}

impl<E: Copy> GpuGKRTranscriptHandoff<E> {
    pub(crate) fn explicit_evaluation_accessors(
        &self,
    ) -> BTreeMap<OutputType, [UnsafeAccessor<[E]>; 2]> {
        self.explicit_evaluations
            .iter()
            .map(|(output_type, evals)| {
                (
                    *output_type,
                    [evals[0].get_accessor(), evals[1].get_accessor()],
                )
            })
            .collect()
    }

    pub(crate) fn final_explicit_evaluations(&self) -> BTreeMap<OutputType, [Vec<E>; 2]> {
        self.explicit_evaluations
            .iter()
            .map(|(output_type, evals)| {
                let copied =
                    std::array::from_fn(|idx| unsafe { evals[idx].get_accessor().get() }.to_vec());
                (*output_type, copied)
            })
            .collect()
    }

    pub(crate) fn flattened_transcript_evaluations(&self) -> Vec<E> {
        let capacity = self
            .explicit_evaluations
            .values()
            .map(|evals| {
                evals
                    .iter()
                    .map(|poly| unsafe { poly.get_accessor().get() }.len())
                    .sum::<usize>()
            })
            .sum();
        let mut flattened = Vec::with_capacity(capacity);
        for evals in self.explicit_evaluations.values() {
            for poly in evals.iter() {
                flattened.extend_from_slice(unsafe { poly.get_accessor().get() });
            }
        }

        flattened
    }
}

impl<B, E: Copy> GpuGKRForwardOutput<B, E> {
    pub(crate) fn schedule_transcript_handoff(
        &self,
        context: &ProverContext,
    ) -> CudaResult<GpuGKRTranscriptHandoff<E>> {
        let mut tracing_ranges = Vec::new();
        let reduced_outputs = self
            .dimension_reducing_inputs
            .get(&self.initial_layer_for_sumcheck)
            .expect("reduced outputs for initial sumcheck layer must exist");
        let mut explicit_evaluations = BTreeMap::new();
        for (output_type, reduced_io) in reduced_outputs.iter() {
            let [first_addr, second_addr]: [GKRAddress; 2] = reduced_io
                .output
                .clone()
                .try_into()
                .expect("transcript handoff expects exactly two reduced outputs per type");
            let first = schedule_ext_poly_readback(&self.storage, first_addr, context)?;
            let second = schedule_ext_poly_readback(&self.storage, second_addr, context)?;
            explicit_evaluations.insert(*output_type, [first, second]);
        }

        Ok(GpuGKRTranscriptHandoff {
            _tracing_ranges: tracing_ranges,
            explicit_evaluations,
        })
    }
}

impl<B, E> GpuGKRForwardOutput<B, E> {
    pub(crate) fn into_dimension_reducing_backward_state(
        self,
    ) -> GpuGKRDimensionReducingBackwardState<B, E> {
        GpuGKRDimensionReducingBackwardState::new(
            self.tracing_ranges,
            self.storage,
            self.initial_layer_for_sumcheck,
            self.dimension_reducing_inputs,
        )
    }
}

#[derive(Clone, Copy, Default)]
pub(super) struct ForwardLookupUsage {
    pub(super) last_generic_mapping_layer: Option<usize>,
    pub(super) last_range_mapping_layer: Option<usize>,
    pub(super) last_timestamp_mapping_layer: Option<usize>,
    pub(super) last_generic_lookup_layer: Option<usize>,
}

pub(super) const GKR_FORWARD_MAX_GATES_PER_LAYER: usize = 63;
pub(super) const GKR_FORWARD_THREADS_PER_BLOCK: u32 = WARP_SIZE * 4;
pub(super) const GKR_DIM_REDUCING_FORWARD_MAX_INPUTS: usize = 5;
pub(super) const MAX_CACHE_RELATIONS_PER_LAYER: usize = 20;
pub(super) const MEMORY_TUPLE_LINEAR_TERMS: usize = 8;
pub(super) const MEMORY_TUPLE_ADDRESS_LOW_TERM: usize = 0;
pub(super) const MEMORY_TUPLE_ADDRESS_HIGH_TERM: usize = 1;
pub(super) const MEMORY_TUPLE_TIMESTAMP_LOW_TERM: usize = 2;
pub(super) const MEMORY_TUPLE_TIMESTAMP_HIGH_TERM: usize = 3;
pub(super) const MEMORY_TUPLE_VALUE_LOW_TERM: usize = 4;
pub(super) const MEMORY_TUPLE_VALUE_LOW_EXTRA_TERM: usize = 5;
pub(super) const MEMORY_TUPLE_VALUE_HIGH_TERM: usize = 6;
pub(super) const MEMORY_TUPLE_VALUE_HIGH_EXTRA_TERM: usize = 7;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub(super) enum GpuGKRForwardGateKind {
    NoOp = 0,
    Product = 1,
    MaskIdentity = 2,
    LookupPair = 3,
    LookupWithCachedDensAndSetup = 4,
    LookupBasePair = 5,
    LookupBaseMinusMultiplicityByBase = 6,
    LookupExtMinusMultiplicityByExt = 7,
    LookupUnbalancedBase = 8,
    LookupUnbalancedExtension = 9,
    LookupExtPair = 10,
    InitialGrandProductWithoutCaches = 11,
    MaterializeGrandProductTermExpression = 12,
    LookupPairFromBaseInputs = 13,
    LookupWithDensAndSetupExpressions = 14,
    LookupPairFromVectorInputs = 15,
    LookupFromVectorInputWithSetup = 16,
    LookupUnbalancedPairWithVectorInputs = 17,
}

impl GpuGKRForwardGateKind {
    pub(super) const fn as_u32(self) -> u32 {
        self as u32
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub(super) struct GpuGKRForwardNoOpDescriptor {
    pub(super) reserved: usize,
}

#[repr(C)]
#[derive(Debug, Default)]
pub(super) struct GpuGKRForwardProductDescriptor<E> {
    pub(super) lhs: *const E,
    pub(super) rhs: *const E,
    pub(super) dst: *mut E,
}

impl<E> Copy for GpuGKRForwardProductDescriptor<E> {}

impl<E> Clone for GpuGKRForwardProductDescriptor<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(super) struct GpuGKRForwardMaskIdentityDescriptor<E> {
    pub(super) input: *const E,
    pub(super) mask: *const BF,
    pub(super) dst: *mut E,
}

impl<E> Copy for GpuGKRForwardMaskIdentityDescriptor<E> {}

impl<E> Clone for GpuGKRForwardMaskIdentityDescriptor<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(super) struct GpuGKRForwardLookupPairDescriptor<E> {
    pub(super) a: *const E,
    pub(super) b: *const E,
    pub(super) c: *const E,
    pub(super) d: *const E,
    pub(super) num: *mut E,
    pub(super) den: *mut E,
}

impl<E> Copy for GpuGKRForwardLookupPairDescriptor<E> {}

impl<E> Clone for GpuGKRForwardLookupPairDescriptor<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(super) struct GpuGKRForwardLookupWithCachedDensAndSetupDescriptor<E> {
    pub(super) a: *const BF,
    pub(super) b: *const E,
    pub(super) c: *const BF,
    pub(super) d: *const E,
    pub(super) num: *mut E,
    pub(super) den: *mut E,
}

impl<E> Copy for GpuGKRForwardLookupWithCachedDensAndSetupDescriptor<E> {}

impl<E> Clone for GpuGKRForwardLookupWithCachedDensAndSetupDescriptor<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(super) struct GpuGKRForwardLookupBasePairDescriptor<E> {
    pub(super) lhs: *const BF,
    pub(super) rhs: *const BF,
    pub(super) num: *mut E,
    pub(super) den: *mut E,
}

impl<E> Copy for GpuGKRForwardLookupBasePairDescriptor<E> {}

impl<E> Clone for GpuGKRForwardLookupBasePairDescriptor<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(super) struct GpuGKRForwardLookupExtPairDescriptor<E> {
    pub(super) lhs: *const E,
    pub(super) rhs: *const E,
    pub(super) num: *mut E,
    pub(super) den: *mut E,
}

impl<E> Copy for GpuGKRForwardLookupExtPairDescriptor<E> {}

impl<E> Clone for GpuGKRForwardLookupExtPairDescriptor<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(super) struct GpuGKRForwardLookupBaseMinusMultiplicityByBaseDescriptor<E> {
    pub(super) b: *const BF,
    pub(super) c: *const BF,
    pub(super) d: *const BF,
    pub(super) d_source_kind: GpuBaseFieldSourceKind,
    pub(super) num: *mut E,
    pub(super) den: *mut E,
}

impl<E> Copy for GpuGKRForwardLookupBaseMinusMultiplicityByBaseDescriptor<E> {}

impl<E> Clone for GpuGKRForwardLookupBaseMinusMultiplicityByBaseDescriptor<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(super) struct GpuGKRForwardLookupExtMinusMultiplicityByExtDescriptor<E> {
    pub(super) b: *const E,
    pub(super) c: *const BF,
    pub(super) d: *const E,
    pub(super) num: *mut E,
    pub(super) den: *mut E,
}

impl<E> Copy for GpuGKRForwardLookupExtMinusMultiplicityByExtDescriptor<E> {}

impl<E> Clone for GpuGKRForwardLookupExtMinusMultiplicityByExtDescriptor<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(super) struct GpuGKRForwardLookupUnbalancedBaseDescriptor<E> {
    pub(super) a: *const E,
    pub(super) b: *const E,
    pub(super) remainder: *const BF,
    pub(super) num: *mut E,
    pub(super) den: *mut E,
}

impl<E> Copy for GpuGKRForwardLookupUnbalancedBaseDescriptor<E> {}

impl<E> Clone for GpuGKRForwardLookupUnbalancedBaseDescriptor<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(super) struct GpuGKRForwardLookupUnbalancedExtensionDescriptor<E> {
    pub(super) a: *const E,
    pub(super) b: *const E,
    pub(super) remainder: *const E,
    pub(super) num: *mut E,
    pub(super) den: *mut E,
}

impl<E> Copy for GpuGKRForwardLookupUnbalancedExtensionDescriptor<E> {}

impl<E> Clone for GpuGKRForwardLookupUnbalancedExtensionDescriptor<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(super) struct GpuGKRForwardMemoryTupleExpressionDescriptor<E> {
    pub(super) address_space_kind: GpuGKRForwardCacheAddressSpaceKind,
    pub(super) address_space_ptr: *const BF,
    pub(super) address_space_constant: BF,
    pub(super) constant_term: E,
    pub(super) linear_inputs: [*const BF; MEMORY_TUPLE_LINEAR_TERMS],
    pub(super) linear_challenges: [E; MEMORY_TUPLE_LINEAR_TERMS],
}

impl<E: Copy> Copy for GpuGKRForwardMemoryTupleExpressionDescriptor<E> {}

impl<E: Copy> Clone for GpuGKRForwardMemoryTupleExpressionDescriptor<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(super) struct GpuGKRForwardInitialGrandProductWithoutCachesDescriptor<E> {
    pub(super) lhs: GpuGKRForwardMemoryTupleExpressionDescriptor<E>,
    pub(super) rhs: GpuGKRForwardMemoryTupleExpressionDescriptor<E>,
    pub(super) dst: *mut E,
}

impl<E: Copy> Copy for GpuGKRForwardInitialGrandProductWithoutCachesDescriptor<E> {}

impl<E: Copy> Clone for GpuGKRForwardInitialGrandProductWithoutCachesDescriptor<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(super) struct GpuGKRForwardMaterializeGrandProductTermExpressionDescriptor<E> {
    pub(super) input: GpuGKRForwardMemoryTupleExpressionDescriptor<E>,
    pub(super) dst: *mut E,
}

impl<E: Copy> Copy for GpuGKRForwardMaterializeGrandProductTermExpressionDescriptor<E> {}

impl<E: Copy> Clone for GpuGKRForwardMaterializeGrandProductTermExpressionDescriptor<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(super) struct GpuGKRForwardLookupPairFromBaseInputsDescriptor<E> {
    pub(super) lhs_mapping: *const u32,
    pub(super) rhs_mapping: *const u32,
    pub(super) num: *mut E,
    pub(super) den: *mut E,
}

impl<E: Copy> Copy for GpuGKRForwardLookupPairFromBaseInputsDescriptor<E> {}

impl<E: Copy> Clone for GpuGKRForwardLookupPairFromBaseInputsDescriptor<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(super) struct GpuGKRForwardLookupWithDensAndSetupExpressionsDescriptor<E> {
    pub(super) decoder_predicate: *const BF,
    pub(super) input_mapping: *const u32,
    pub(super) multiplicity: *const BF,
    pub(super) generic_lookup: *const E,
    pub(super) decoder_fill_value: *const E,
    pub(super) generic_lookup_len: u32,
    pub(super) num: *mut E,
    pub(super) den: *mut E,
}

impl<E> Copy for GpuGKRForwardLookupWithDensAndSetupExpressionsDescriptor<E> {}

impl<E> Clone for GpuGKRForwardLookupWithDensAndSetupExpressionsDescriptor<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(super) struct GpuGKRForwardLookupPairFromVectorInputsDescriptor<E> {
    pub(super) lhs_mapping: *const u32,
    pub(super) rhs_mapping: *const u32,
    pub(super) generic_lookup: *const E,
    pub(super) num: *mut E,
    pub(super) den: *mut E,
}

impl<E> Copy for GpuGKRForwardLookupPairFromVectorInputsDescriptor<E> {}

impl<E> Clone for GpuGKRForwardLookupPairFromVectorInputsDescriptor<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(super) struct GpuGKRForwardLookupFromVectorInputWithSetupDescriptor<E> {
    pub(super) input_mapping: *const u32,
    pub(super) multiplicity: *const BF,
    pub(super) generic_lookup: *const E,
    pub(super) generic_lookup_len: u32,
    pub(super) num: *mut E,
    pub(super) den: *mut E,
}

impl<E> Copy for GpuGKRForwardLookupFromVectorInputWithSetupDescriptor<E> {}

impl<E> Clone for GpuGKRForwardLookupFromVectorInputWithSetupDescriptor<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(super) struct GpuGKRForwardLookupUnbalancedPairWithVectorInputsDescriptor<E> {
    pub(super) a: *const E,
    pub(super) b: *const E,
    pub(super) remainder_mapping: *const u32,
    pub(super) generic_lookup: *const E,
    pub(super) num: *mut E,
    pub(super) den: *mut E,
}

impl<E> Copy for GpuGKRForwardLookupUnbalancedPairWithVectorInputsDescriptor<E> {}

impl<E> Clone for GpuGKRForwardLookupUnbalancedPairWithVectorInputsDescriptor<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
union GpuGKRForwardGatePayload<E> {
    no_op: ManuallyDrop<GpuGKRForwardNoOpDescriptor>,
    product: ManuallyDrop<GpuGKRForwardProductDescriptor<E>>,
    mask_identity: ManuallyDrop<GpuGKRForwardMaskIdentityDescriptor<E>>,
    lookup_pair: ManuallyDrop<GpuGKRForwardLookupPairDescriptor<E>>,
    lookup_with_cached_dens_and_setup:
        ManuallyDrop<GpuGKRForwardLookupWithCachedDensAndSetupDescriptor<E>>,
    lookup_base_pair: ManuallyDrop<GpuGKRForwardLookupBasePairDescriptor<E>>,
    lookup_ext_pair: ManuallyDrop<GpuGKRForwardLookupExtPairDescriptor<E>>,
    lookup_base_minus_multiplicity_by_base:
        ManuallyDrop<GpuGKRForwardLookupBaseMinusMultiplicityByBaseDescriptor<E>>,
    lookup_ext_minus_multiplicity_by_ext:
        ManuallyDrop<GpuGKRForwardLookupExtMinusMultiplicityByExtDescriptor<E>>,
    lookup_unbalanced_base: ManuallyDrop<GpuGKRForwardLookupUnbalancedBaseDescriptor<E>>,
    lookup_unbalanced_extension: ManuallyDrop<GpuGKRForwardLookupUnbalancedExtensionDescriptor<E>>,
    initial_grand_product_without_caches:
        ManuallyDrop<GpuGKRForwardInitialGrandProductWithoutCachesDescriptor<E>>,
    materialize_grand_product_term_expression:
        ManuallyDrop<GpuGKRForwardMaterializeGrandProductTermExpressionDescriptor<E>>,
    lookup_pair_from_base_inputs: ManuallyDrop<GpuGKRForwardLookupPairFromBaseInputsDescriptor<E>>,
    lookup_with_dens_and_setup_expressions:
        ManuallyDrop<GpuGKRForwardLookupWithDensAndSetupExpressionsDescriptor<E>>,
    lookup_pair_from_vector_inputs:
        ManuallyDrop<GpuGKRForwardLookupPairFromVectorInputsDescriptor<E>>,
    lookup_from_vector_input_with_setup:
        ManuallyDrop<GpuGKRForwardLookupFromVectorInputWithSetupDescriptor<E>>,
    lookup_unbalanced_pair_with_vector_inputs:
        ManuallyDrop<GpuGKRForwardLookupUnbalancedPairWithVectorInputsDescriptor<E>>,
}

impl<E: Copy> Copy for GpuGKRForwardGatePayload<E> {}

impl<E: Copy> Clone for GpuGKRForwardGatePayload<E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<E> Default for GpuGKRForwardGatePayload<E> {
    fn default() -> Self {
        Self {
            no_op: ManuallyDrop::new(GpuGKRForwardNoOpDescriptor::default()),
        }
    }
}

#[repr(C)]
#[derive(Default)]
pub(super) struct GpuGKRForwardGateDescriptor<E> {
    pub(super) kind: u32,
    pub(super) _reserved: u32,
    pub(super) payload: GpuGKRForwardGatePayload<E>,
}

impl<E: Copy> Copy for GpuGKRForwardGateDescriptor<E> {}

impl<E: Copy> Clone for GpuGKRForwardGateDescriptor<E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<E> GpuGKRForwardGateDescriptor<E> {
    pub(super) fn no_op() -> Self {
        Self {
            kind: GpuGKRForwardGateKind::NoOp.as_u32(),
            _reserved: 0,
            payload: GpuGKRForwardGatePayload::default(),
        }
    }

    pub(super) fn with_product(lhs: *const E, rhs: *const E, dst: *mut E) -> Self {
        Self {
            kind: GpuGKRForwardGateKind::Product.as_u32(),
            _reserved: 0,
            payload: GpuGKRForwardGatePayload {
                product: ManuallyDrop::new(GpuGKRForwardProductDescriptor { lhs, rhs, dst }),
            },
        }
    }

    pub(super) fn with_mask_identity(input: *const E, mask: *const BF, dst: *mut E) -> Self {
        Self {
            kind: GpuGKRForwardGateKind::MaskIdentity.as_u32(),
            _reserved: 0,
            payload: GpuGKRForwardGatePayload {
                mask_identity: ManuallyDrop::new(GpuGKRForwardMaskIdentityDescriptor {
                    input,
                    mask,
                    dst,
                }),
            },
        }
    }

    pub(super) fn with_lookup_pair(
        a: *const E,
        b: *const E,
        c: *const E,
        d: *const E,
        num: *mut E,
        den: *mut E,
    ) -> Self {
        Self {
            kind: GpuGKRForwardGateKind::LookupPair.as_u32(),
            _reserved: 0,
            payload: GpuGKRForwardGatePayload {
                lookup_pair: ManuallyDrop::new(GpuGKRForwardLookupPairDescriptor {
                    a,
                    b,
                    c,
                    d,
                    num,
                    den,
                }),
            },
        }
    }

    pub(super) fn with_lookup_cached_dens_and_setup(
        a: *const BF,
        b: *const E,
        c: *const BF,
        d: *const E,
        num: *mut E,
        den: *mut E,
    ) -> Self {
        Self {
            kind: GpuGKRForwardGateKind::LookupWithCachedDensAndSetup.as_u32(),
            _reserved: 0,
            payload: GpuGKRForwardGatePayload {
                lookup_with_cached_dens_and_setup: ManuallyDrop::new(
                    GpuGKRForwardLookupWithCachedDensAndSetupDescriptor {
                        a,
                        b,
                        c,
                        d,
                        num,
                        den,
                    },
                ),
            },
        }
    }

    pub(super) fn with_lookup_base_pair(
        lhs: *const BF,
        rhs: *const BF,
        num: *mut E,
        den: *mut E,
    ) -> Self {
        Self {
            kind: GpuGKRForwardGateKind::LookupBasePair.as_u32(),
            _reserved: 0,
            payload: GpuGKRForwardGatePayload {
                lookup_base_pair: ManuallyDrop::new(GpuGKRForwardLookupBasePairDescriptor {
                    lhs,
                    rhs,
                    num,
                    den,
                }),
            },
        }
    }

    pub(super) fn with_lookup_ext_pair(
        lhs: *const E,
        rhs: *const E,
        num: *mut E,
        den: *mut E,
    ) -> Self {
        Self {
            kind: GpuGKRForwardGateKind::LookupExtPair.as_u32(),
            _reserved: 0,
            payload: GpuGKRForwardGatePayload {
                lookup_ext_pair: ManuallyDrop::new(GpuGKRForwardLookupExtPairDescriptor {
                    lhs,
                    rhs,
                    num,
                    den,
                }),
            },
        }
    }

    pub(super) fn with_lookup_base_minus_multiplicity_by_base(
        b: *const BF,
        c: *const BF,
        d: *const BF,
        d_source_kind: GpuBaseFieldSourceKind,
        num: *mut E,
        den: *mut E,
    ) -> Self {
        Self {
            kind: GpuGKRForwardGateKind::LookupBaseMinusMultiplicityByBase.as_u32(),
            _reserved: 0,
            payload: GpuGKRForwardGatePayload {
                lookup_base_minus_multiplicity_by_base: ManuallyDrop::new(
                    GpuGKRForwardLookupBaseMinusMultiplicityByBaseDescriptor {
                        b,
                        c,
                        d,
                        d_source_kind,
                        num,
                        den,
                    },
                ),
            },
        }
    }

    pub(super) fn with_lookup_ext_minus_multiplicity_by_ext(
        b: *const E,
        c: *const BF,
        d: *const E,
        num: *mut E,
        den: *mut E,
    ) -> Self {
        Self {
            kind: GpuGKRForwardGateKind::LookupExtMinusMultiplicityByExt.as_u32(),
            _reserved: 0,
            payload: GpuGKRForwardGatePayload {
                lookup_ext_minus_multiplicity_by_ext: ManuallyDrop::new(
                    GpuGKRForwardLookupExtMinusMultiplicityByExtDescriptor { b, c, d, num, den },
                ),
            },
        }
    }

    pub(super) fn with_lookup_unbalanced_base(
        a: *const E,
        b: *const E,
        remainder: *const BF,
        num: *mut E,
        den: *mut E,
    ) -> Self {
        Self {
            kind: GpuGKRForwardGateKind::LookupUnbalancedBase.as_u32(),
            _reserved: 0,
            payload: GpuGKRForwardGatePayload {
                lookup_unbalanced_base: ManuallyDrop::new(
                    GpuGKRForwardLookupUnbalancedBaseDescriptor {
                        a,
                        b,
                        remainder,
                        num,
                        den,
                    },
                ),
            },
        }
    }

    pub(super) fn with_lookup_unbalanced_extension(
        a: *const E,
        b: *const E,
        remainder: *const E,
        num: *mut E,
        den: *mut E,
    ) -> Self {
        Self {
            kind: GpuGKRForwardGateKind::LookupUnbalancedExtension.as_u32(),
            _reserved: 0,
            payload: GpuGKRForwardGatePayload {
                lookup_unbalanced_extension: ManuallyDrop::new(
                    GpuGKRForwardLookupUnbalancedExtensionDescriptor {
                        a,
                        b,
                        remainder,
                        num,
                        den,
                    },
                ),
            },
        }
    }

    pub(super) fn with_initial_grand_product_without_caches(
        lhs: GpuGKRForwardMemoryTupleExpressionDescriptor<E>,
        rhs: GpuGKRForwardMemoryTupleExpressionDescriptor<E>,
        dst: *mut E,
    ) -> Self {
        Self {
            kind: GpuGKRForwardGateKind::InitialGrandProductWithoutCaches.as_u32(),
            _reserved: 0,
            payload: GpuGKRForwardGatePayload {
                initial_grand_product_without_caches: ManuallyDrop::new(
                    GpuGKRForwardInitialGrandProductWithoutCachesDescriptor { lhs, rhs, dst },
                ),
            },
        }
    }

    pub(super) fn with_materialize_grand_product_term_expression(
        input: GpuGKRForwardMemoryTupleExpressionDescriptor<E>,
        dst: *mut E,
    ) -> Self {
        Self {
            kind: GpuGKRForwardGateKind::MaterializeGrandProductTermExpression.as_u32(),
            _reserved: 0,
            payload: GpuGKRForwardGatePayload {
                materialize_grand_product_term_expression: ManuallyDrop::new(
                    GpuGKRForwardMaterializeGrandProductTermExpressionDescriptor { input, dst },
                ),
            },
        }
    }

    pub(super) fn with_lookup_pair_from_base_inputs(
        lhs_mapping: *const u32,
        rhs_mapping: *const u32,
        num: *mut E,
        den: *mut E,
    ) -> Self {
        Self {
            kind: GpuGKRForwardGateKind::LookupPairFromBaseInputs.as_u32(),
            _reserved: 0,
            payload: GpuGKRForwardGatePayload {
                lookup_pair_from_base_inputs: ManuallyDrop::new(
                    GpuGKRForwardLookupPairFromBaseInputsDescriptor {
                        lhs_mapping,
                        rhs_mapping,
                        num,
                        den,
                    },
                ),
            },
        }
    }

    pub(super) fn with_lookup_with_dens_and_setup_expressions(
        decoder_predicate: *const BF,
        input_mapping: *const u32,
        multiplicity: *const BF,
        generic_lookup: *const E,
        decoder_fill_value: *const E,
        generic_lookup_len: u32,
        num: *mut E,
        den: *mut E,
    ) -> Self {
        Self {
            kind: GpuGKRForwardGateKind::LookupWithDensAndSetupExpressions.as_u32(),
            _reserved: 0,
            payload: GpuGKRForwardGatePayload {
                lookup_with_dens_and_setup_expressions: ManuallyDrop::new(
                    GpuGKRForwardLookupWithDensAndSetupExpressionsDescriptor {
                        decoder_predicate,
                        input_mapping,
                        multiplicity,
                        generic_lookup,
                        decoder_fill_value,
                        generic_lookup_len,
                        num,
                        den,
                    },
                ),
            },
        }
    }

    pub(super) fn with_lookup_pair_from_vector_inputs(
        lhs_mapping: *const u32,
        rhs_mapping: *const u32,
        generic_lookup: *const E,
        num: *mut E,
        den: *mut E,
    ) -> Self {
        Self {
            kind: GpuGKRForwardGateKind::LookupPairFromVectorInputs.as_u32(),
            _reserved: 0,
            payload: GpuGKRForwardGatePayload {
                lookup_pair_from_vector_inputs: ManuallyDrop::new(
                    GpuGKRForwardLookupPairFromVectorInputsDescriptor {
                        lhs_mapping,
                        rhs_mapping,
                        generic_lookup,
                        num,
                        den,
                    },
                ),
            },
        }
    }

    pub(super) fn with_lookup_from_vector_input_with_setup(
        input_mapping: *const u32,
        multiplicity: *const BF,
        generic_lookup: *const E,
        generic_lookup_len: u32,
        num: *mut E,
        den: *mut E,
    ) -> Self {
        Self {
            kind: GpuGKRForwardGateKind::LookupFromVectorInputWithSetup.as_u32(),
            _reserved: 0,
            payload: GpuGKRForwardGatePayload {
                lookup_from_vector_input_with_setup: ManuallyDrop::new(
                    GpuGKRForwardLookupFromVectorInputWithSetupDescriptor {
                        input_mapping,
                        multiplicity,
                        generic_lookup,
                        generic_lookup_len,
                        num,
                        den,
                    },
                ),
            },
        }
    }

    pub(super) fn with_lookup_unbalanced_pair_with_vector_inputs(
        a: *const E,
        b: *const E,
        remainder_mapping: *const u32,
        generic_lookup: *const E,
        num: *mut E,
        den: *mut E,
    ) -> Self {
        Self {
            kind: GpuGKRForwardGateKind::LookupUnbalancedPairWithVectorInputs.as_u32(),
            _reserved: 0,
            payload: GpuGKRForwardGatePayload {
                lookup_unbalanced_pair_with_vector_inputs: ManuallyDrop::new(
                    GpuGKRForwardLookupUnbalancedPairWithVectorInputsDescriptor {
                        a,
                        b,
                        remainder_mapping,
                        generic_lookup,
                        num,
                        den,
                    },
                ),
            },
        }
    }
}

#[repr(C)]
pub(super) struct GpuGKRForwardLayerBatch<
    E,
    const MAX_GATES: usize = GKR_FORWARD_MAX_GATES_PER_LAYER,
> {
    pub(super) gate_count: u32,
    pub(super) _reserved: u32,
    pub(super) lookup_additive_challenge: *const E,
    pub(super) descriptors: [GpuGKRForwardGateDescriptor<E>; MAX_GATES],
}

impl<E: Copy, const MAX_GATES: usize> Copy for GpuGKRForwardLayerBatch<E, MAX_GATES> {}

impl<E: Copy, const MAX_GATES: usize> Clone for GpuGKRForwardLayerBatch<E, MAX_GATES> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<E, const MAX_GATES: usize> Default for GpuGKRForwardLayerBatch<E, MAX_GATES> {
    fn default() -> Self {
        Self {
            gate_count: 0,
            _reserved: 0,
            lookup_additive_challenge: null(),
            descriptors: std::array::from_fn(|_| GpuGKRForwardGateDescriptor::no_op()),
        }
    }
}

impl<E, const MAX_GATES: usize> GpuGKRForwardLayerBatch<E, MAX_GATES> {
    pub(super) fn new(lookup_additive_challenge: *const E) -> Self {
        Self {
            lookup_additive_challenge,
            ..Self::default()
        }
    }
}

pub(super) struct LoweredGpuGKRForwardLayer<E> {
    pub(super) batches: Vec<GpuGKRForwardLayerBatch<E>>,
    pub(super) computed_extension_outputs: Vec<(GKRAddress, GpuExtensionFieldPoly<E>)>,
    pub(super) aliased_base_outputs: Vec<(GKRAddress, GpuBaseFieldPoly<BF>)>,
    pub(super) aliased_extension_outputs: Vec<(GKRAddress, GpuExtensionFieldPoly<E>)>,
}

cuda_kernel_signature_arguments_and_function!(
    GpuGKRForwardLayer<T>,
    batch: GpuGKRForwardLayerBatch<T>,
    count: u32,
);

pub(crate) trait GpuGKRForwardKernelSet: Copy + Sized {
    const FORWARD_LAYER: GpuGKRForwardLayerSignature<Self>;
}

macro_rules! gkr_forward_layer_kernels {
    ($type:ty) => {
        paste! {
            cuda_kernel_declaration!(
                [<ab_gkr_forward_layer_ $type:lower _kernel>](
                    batch: GpuGKRForwardLayerBatch<$type>,
                    count: u32,
                )
            );

            impl GpuGKRForwardKernelSet for $type {
                const FORWARD_LAYER: GpuGKRForwardLayerSignature<Self> =
                    [<ab_gkr_forward_layer_ $type:lower _kernel>];
            }
        }
    };
}

gkr_forward_layer_kernels!(E4);

#[repr(u32)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(super) enum GpuGKRForwardCacheKind {
    #[default]
    Empty = 0,
    SingleColumnLookup = 1,
    VectorizedLookup = 2,
    VectorizedLookupSetup = 3,
    MemoryTuple = 4,
}

#[repr(u32)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(super) enum GpuGKRForwardCacheAddressSpaceKind {
    #[default]
    Empty = 0,
    Constant = 1,
    Is = 2,
    Not = 3,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub(super) struct GpuGKRForwardCacheDescriptor<E> {
    pub(super) kind: GpuGKRForwardCacheKind,
    pub(super) address_space_kind: GpuGKRForwardCacheAddressSpaceKind,
    pub(super) mapping: *const u32,
    pub(super) setup_values: *const BF,
    pub(super) setup_source_kind: GpuBaseFieldSourceKind,
    pub(super) generic_lookup: *const E,
    pub(super) decoder_mask: *const BF,
    pub(super) decoder_fill_value: *const E,
    pub(super) base_output: *mut BF,
    pub(super) ext_output: *mut E,
    pub(super) generic_lookup_len: u32,
    pub(super) address_space_ptr: *const BF,
    pub(super) address_space_constant: BF,
    pub(super) constant_term: E,
    pub(super) linear_inputs: [*const BF; MEMORY_TUPLE_LINEAR_TERMS],
    pub(super) linear_challenges: [E; MEMORY_TUPLE_LINEAR_TERMS],
}

impl<E: Field> Default for GpuGKRForwardCacheDescriptor<E> {
    fn default() -> Self {
        Self {
            kind: GpuGKRForwardCacheKind::Empty,
            address_space_kind: GpuGKRForwardCacheAddressSpaceKind::Empty,
            mapping: null(),
            setup_values: null(),
            setup_source_kind: GpuBaseFieldSourceKind::Empty,
            generic_lookup: null(),
            decoder_mask: null(),
            decoder_fill_value: null(),
            base_output: null::<BF>().cast_mut(),
            ext_output: null::<E>().cast_mut(),
            generic_lookup_len: 0,
            address_space_ptr: null(),
            address_space_constant: BF::ZERO,
            constant_term: E::ZERO,
            linear_inputs: [null(); MEMORY_TUPLE_LINEAR_TERMS],
            linear_challenges: [E::ZERO; MEMORY_TUPLE_LINEAR_TERMS],
        }
    }
}

#[repr(C)]
#[derive(Clone, Copy)]
pub(super) struct GpuGKRForwardCacheBatch<E> {
    pub(super) count: u32,
    pub(super) descriptors: [GpuGKRForwardCacheDescriptor<E>; MAX_CACHE_RELATIONS_PER_LAYER],
}

impl<E: Field> Default for GpuGKRForwardCacheBatch<E> {
    fn default() -> Self {
        Self {
            count: 0,
            descriptors: [GpuGKRForwardCacheDescriptor::default(); MAX_CACHE_RELATIONS_PER_LAYER],
        }
    }
}

cuda_kernel_signature_arguments_and_function!(
    GpuGKRForwardCache<T>,
    batch: GpuGKRForwardCacheBatch<T>,
    trace_len: u32,
);

pub(crate) trait GpuGKRForwardCacheKernelSet: Copy + Sized {
    const FORWARD_CACHE: GpuGKRForwardCacheSignature<Self>;
}

macro_rules! gkr_forward_cache_kernels {
    ($type:ty) => {
        paste! {
            cuda_kernel_declaration!(
                [<ab_gkr_forward_cache_ $type:lower _kernel>](
                    batch: GpuGKRForwardCacheBatch<$type>,
                    trace_len: u32,
                )
            );

            impl GpuGKRForwardCacheKernelSet for $type {
                const FORWARD_CACHE: GpuGKRForwardCacheSignature<Self> =
                    [<ab_gkr_forward_cache_ $type:lower _kernel>];
            }
        }
    };
}

gkr_forward_cache_kernels!(E4);

cuda_kernel_signature_arguments_and_function!(
    GpuGKRVirtualBaseAccum<T>,
    source_kind: GpuBaseFieldSourceKind,
    scalar: T,
    dst: *mut T,
    count: u32,
);

pub(crate) trait GpuGKRVirtualBaseAccumKernelSet: Copy + Sized {
    const VIRTUAL_BASE_ACCUM: GpuGKRVirtualBaseAccumSignature<Self>;
}

macro_rules! gkr_virtual_base_accum_kernels {
    ($type:ty) => {
        paste! {
            cuda_kernel_declaration!(
                [<ab_gkr_virtual_base_accum_ $type:lower _kernel>](
                    source_kind: GpuBaseFieldSourceKind,
                    scalar: $type,
                    dst: *mut $type,
                    count: u32,
                )
            );

            impl GpuGKRVirtualBaseAccumKernelSet for $type {
                const VIRTUAL_BASE_ACCUM: GpuGKRVirtualBaseAccumSignature<Self> =
                    [<ab_gkr_virtual_base_accum_ $type:lower _kernel>];
            }
        }
    };
}

gkr_virtual_base_accum_kernels!(E4);

#[repr(u32)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(super) enum GpuGKRDimensionReducingForwardInputKind {
    #[default]
    NoOp = 0,
    PairwiseProduct = 1,
    LookupPair = 2,
}

impl GpuGKRDimensionReducingForwardInputKind {
    pub(super) const fn as_u32(self) -> u32 {
        self as u32
    }
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub(super) struct GpuGKRDimensionReducingForwardNoOpDescriptor {
    pub(super) reserved: usize,
}

#[repr(C)]
#[derive(Debug, Default)]
pub(super) struct GpuGKRDimensionReducingForwardPairwiseProductDescriptor<E> {
    pub(super) input: *const E,
    pub(super) output: *mut E,
}

impl<E> Copy for GpuGKRDimensionReducingForwardPairwiseProductDescriptor<E> {}

impl<E> Clone for GpuGKRDimensionReducingForwardPairwiseProductDescriptor<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
#[derive(Debug, Default)]
pub(super) struct GpuGKRDimensionReducingForwardLookupPairDescriptor<E> {
    pub(super) num: *const E,
    pub(super) den: *const E,
    pub(super) output_num: *mut E,
    pub(super) output_den: *mut E,
}

impl<E> Copy for GpuGKRDimensionReducingForwardLookupPairDescriptor<E> {}

impl<E> Clone for GpuGKRDimensionReducingForwardLookupPairDescriptor<E> {
    fn clone(&self) -> Self {
        *self
    }
}

#[repr(C)]
union GpuGKRDimensionReducingForwardInputPayload<E> {
    no_op: ManuallyDrop<GpuGKRDimensionReducingForwardNoOpDescriptor>,
    pairwise_product: ManuallyDrop<GpuGKRDimensionReducingForwardPairwiseProductDescriptor<E>>,
    lookup_pair: ManuallyDrop<GpuGKRDimensionReducingForwardLookupPairDescriptor<E>>,
}

impl<E> Copy for GpuGKRDimensionReducingForwardInputPayload<E> {}

impl<E> Clone for GpuGKRDimensionReducingForwardInputPayload<E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<E> Default for GpuGKRDimensionReducingForwardInputPayload<E> {
    fn default() -> Self {
        Self {
            no_op: ManuallyDrop::new(GpuGKRDimensionReducingForwardNoOpDescriptor::default()),
        }
    }
}

#[repr(C)]
#[derive(Default)]
pub(super) struct GpuGKRDimensionReducingForwardInputDescriptor<E> {
    pub(super) kind: u32,
    pub(super) _reserved: u32,
    pub(super) payload: GpuGKRDimensionReducingForwardInputPayload<E>,
}

impl<E> Copy for GpuGKRDimensionReducingForwardInputDescriptor<E> {}

impl<E> Clone for GpuGKRDimensionReducingForwardInputDescriptor<E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<E> GpuGKRDimensionReducingForwardInputDescriptor<E> {
    pub(super) fn no_op() -> Self {
        Self {
            kind: GpuGKRDimensionReducingForwardInputKind::NoOp.as_u32(),
            _reserved: 0,
            payload: GpuGKRDimensionReducingForwardInputPayload::default(),
        }
    }

    pub(super) fn with_pairwise_product(input: *const E, output: *mut E) -> Self {
        Self {
            kind: GpuGKRDimensionReducingForwardInputKind::PairwiseProduct.as_u32(),
            _reserved: 0,
            payload: GpuGKRDimensionReducingForwardInputPayload {
                pairwise_product: ManuallyDrop::new(
                    GpuGKRDimensionReducingForwardPairwiseProductDescriptor { input, output },
                ),
            },
        }
    }

    pub(super) fn with_lookup_pair(
        num: *const E,
        den: *const E,
        output_num: *mut E,
        output_den: *mut E,
    ) -> Self {
        Self {
            kind: GpuGKRDimensionReducingForwardInputKind::LookupPair.as_u32(),
            _reserved: 0,
            payload: GpuGKRDimensionReducingForwardInputPayload {
                lookup_pair: ManuallyDrop::new(
                    GpuGKRDimensionReducingForwardLookupPairDescriptor {
                        num,
                        den,
                        output_num,
                        output_den,
                    },
                ),
            },
        }
    }
}

#[derive(Clone, Copy)]
pub(super) enum LoweredGpuGKRDimensionReducingForwardInput<E> {
    PairwiseProduct {
        input: *const E,
        output: *mut E,
    },
    LookupPair {
        num: *const E,
        den: *const E,
        output_num: *mut E,
        output_den: *mut E,
    },
}

#[repr(C)]
pub(super) struct GpuGKRDimensionReducingForwardBatch<
    E,
    const MAX_INPUTS: usize = GKR_DIM_REDUCING_FORWARD_MAX_INPUTS,
> {
    pub(super) input_count: u32,
    pub(super) _reserved: u32,
    pub(super) descriptors: [GpuGKRDimensionReducingForwardInputDescriptor<E>; MAX_INPUTS],
}

impl<E, const MAX_INPUTS: usize> Copy for GpuGKRDimensionReducingForwardBatch<E, MAX_INPUTS> {}

impl<E, const MAX_INPUTS: usize> Clone for GpuGKRDimensionReducingForwardBatch<E, MAX_INPUTS> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<E, const MAX_INPUTS: usize> Default for GpuGKRDimensionReducingForwardBatch<E, MAX_INPUTS> {
    fn default() -> Self {
        Self {
            input_count: 0,
            _reserved: 0,
            descriptors: [GpuGKRDimensionReducingForwardInputDescriptor::no_op(); MAX_INPUTS],
        }
    }
}

pub(super) struct LoweredGpuGKRDimensionReducingForwardRound<E> {
    pub(super) batch: GpuGKRDimensionReducingForwardBatch<E>,
    pub(super) layer_description: BTreeMap<OutputType, DimensionReducingInputOutput>,
    pub(super) computed_extension_outputs: Vec<(GKRAddress, GpuExtensionFieldPoly<E>)>,
}

cuda_kernel_signature_arguments_and_function!(
    GpuGKRDimensionReducingForward<T>,
    batch: GpuGKRDimensionReducingForwardBatch<T>,
    row_count: u32,
);

pub(crate) trait GpuGKRDimensionReducingForwardKernelSet: Copy + Sized {
    const DIMENSION_REDUCING_FORWARD: GpuGKRDimensionReducingForwardSignature<Self>;
}

macro_rules! gkr_dim_reducing_forward_kernels {
    ($type:ty) => {
        paste! {
            cuda_kernel_declaration!(
                [<ab_gkr_dim_reducing_forward_ $type:lower _kernel>](
                    batch: GpuGKRDimensionReducingForwardBatch<$type>,
                    row_count: u32,
                )
            );

            impl GpuGKRDimensionReducingForwardKernelSet for $type {
                const DIMENSION_REDUCING_FORWARD: GpuGKRDimensionReducingForwardSignature<Self> =
                    [<ab_gkr_dim_reducing_forward_ $type:lower _kernel>];
            }
        }
    };
}

gkr_dim_reducing_forward_kernels!(E4);

pub(super) fn gkr_forward_cache_launch_config(
    count: u32,
    context: &ProverContext,
) -> CudaLaunchConfig<'_> {
    let (grid_dim, block_dim) = get_grid_block_dims_for_threads_count(WARP_SIZE * 4, count.max(1));
    CudaLaunchConfig::basic(grid_dim, block_dim, context.get_exec_stream())
}

pub(super) fn launch_forward_cache<E: GpuGKRForwardCacheKernelSet>(
    batch: GpuGKRForwardCacheBatch<E>,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(trace_len <= u32::MAX as usize);
    let config = gkr_forward_cache_launch_config(trace_len as u32, context);
    let args = GpuGKRForwardCacheArguments::new(batch, trace_len as u32);
    GpuGKRForwardCacheFunction(E::FORWARD_CACHE).launch(&config, &args)
}

pub(super) fn launch_virtual_base_accum<E: GpuGKRVirtualBaseAccumKernelSet>(
    source_kind: GpuBaseFieldSourceKind,
    scalar: E,
    dst: *mut E,
    count: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(count <= u32::MAX as usize);
    let config = gkr_forward_cache_launch_config(count as u32, context);
    let args = GpuGKRVirtualBaseAccumArguments::new(source_kind, scalar, dst, count as u32);
    GpuGKRVirtualBaseAccumFunction(E::VIRTUAL_BASE_ACCUM).launch(&config, &args)
}

pub(super) fn pack_dimension_reducing_forward_batch<E>(
    lowered_inputs: &[LoweredGpuGKRDimensionReducingForwardInput<E>],
) -> GpuGKRDimensionReducingForwardBatch<E> {
    assert!(
        lowered_inputs.len() <= GKR_DIM_REDUCING_FORWARD_MAX_INPUTS,
        "dimension reduction layer has {} lowered inputs, exceeding the fused forward cap of {}",
        lowered_inputs.len(),
        GKR_DIM_REDUCING_FORWARD_MAX_INPUTS
    );

    let mut batch = GpuGKRDimensionReducingForwardBatch::default();
    batch.input_count = lowered_inputs.len() as u32;
    for (lowered_input, descriptor) in lowered_inputs.iter().zip(batch.descriptors.iter_mut()) {
        *descriptor = match *lowered_input {
            LoweredGpuGKRDimensionReducingForwardInput::PairwiseProduct { input, output } => {
                GpuGKRDimensionReducingForwardInputDescriptor::with_pairwise_product(input, output)
            }
            LoweredGpuGKRDimensionReducingForwardInput::LookupPair {
                num,
                den,
                output_num,
                output_den,
            } => GpuGKRDimensionReducingForwardInputDescriptor::with_lookup_pair(
                num, den, output_num, output_den,
            ),
        };
    }

    batch
}

pub(super) fn gkr_dimension_reducing_forward_launch_config(
    row_count: u32,
    context: &ProverContext,
) -> CudaLaunchConfig<'_> {
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(GKR_FORWARD_THREADS_PER_BLOCK, row_count.max(1));
    CudaLaunchConfig::basic(grid_dim, block_dim, context.get_exec_stream())
}

pub(super) fn launch_dimension_reducing_forward<E: GpuGKRDimensionReducingForwardKernelSet>(
    batch: &GpuGKRDimensionReducingForwardBatch<E>,
    row_count: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(row_count <= u32::MAX as usize);
    let config = gkr_dimension_reducing_forward_launch_config(row_count as u32, context);
    let args = GpuGKRDimensionReducingForwardArguments::new(*batch, row_count as u32);
    GpuGKRDimensionReducingForwardFunction(E::DIMENSION_REDUCING_FORWARD).launch(&config, &args)
}

pub(super) fn gkr_forward_launch_config(
    count: u32,
    context: &ProverContext,
) -> CudaLaunchConfig<'_> {
    let (grid_dim, block_dim) =
        get_grid_block_dims_for_threads_count(GKR_FORWARD_THREADS_PER_BLOCK, count.max(1));
    CudaLaunchConfig::basic(grid_dim, block_dim, context.get_exec_stream())
}

pub(super) fn launch_forward_layer<E: GpuGKRForwardKernelSet>(
    batch: &GpuGKRForwardLayerBatch<E>,
    trace_len: usize,
    context: &ProverContext,
) -> CudaResult<()> {
    assert!(trace_len <= u32::MAX as usize);
    let count = trace_len as u32;
    let config = gkr_forward_launch_config(count, context);
    let args = GpuGKRForwardLayerArguments::new(*batch, count);
    GpuGKRForwardLayerFunction(E::FORWARD_LAYER).launch(&config, &args)
}
