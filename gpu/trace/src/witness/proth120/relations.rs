use crate::upstream::{
    GKRAddress, GKRCircuitArtifact, PRLinearRelation, PRSingleColumnLookupRelation,
};
use crate::witness::{Address, MAX_LINEAR_TERMS_COUNT};
use era_cudart::memory::memory_copy_async;
use era_cudart::result::CudaResult;
use gpu_core::allocator::tracker::AllocationPlacement;
use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::PR;
use gpu_core::primitives::static_host::{alloc_static_pinned_box_from_slice, StaticPinnedBox};
use gpu_prover_context::ProverContext;
use std::mem::{align_of, offset_of, size_of};

#[repr(C, align(16))]
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct Proth120LinearTerm {
    coefficient: PR,
    address: Address,
    padding: u32,
}

#[repr(C, align(16))]
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct Proth120LinearRelation {
    constant: PR,
    terms: [Proth120LinearTerm; MAX_LINEAR_TERMS_COUNT],
    terms_count: u32,
    padding: [u32; 3],
}

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub(crate) struct Proth120LookupExpressions {
    relations: *const Proth120LinearRelation,
    count: u32,
    padding: u32,
}

const _: () = {
    assert!(size_of::<Address>() == 12);
    assert!(align_of::<Address>() == 4);
    assert!(offset_of!(Proth120LinearTerm, coefficient) == 0);
    assert!(offset_of!(Proth120LinearTerm, address) == 16);
    assert!(offset_of!(Proth120LinearTerm, padding) == 28);
    assert!(size_of::<Proth120LinearTerm>() == 32);
    assert!(align_of::<Proth120LinearTerm>() == 16);
    assert!(offset_of!(Proth120LinearRelation, constant) == 0);
    assert!(offset_of!(Proth120LinearRelation, terms) == 16);
    assert!(offset_of!(Proth120LinearRelation, terms_count) == 144);
    assert!(offset_of!(Proth120LinearRelation, padding) == 148);
    assert!(size_of::<Proth120LinearRelation>() == 160);
    assert!(align_of::<Proth120LinearRelation>() == 16);
    assert!(offset_of!(Proth120LookupExpressions, relations) == 0);
    assert!(offset_of!(Proth120LookupExpressions, count) == 8);
    assert!(offset_of!(Proth120LookupExpressions, padding) == 12);
    assert!(size_of::<Proth120LookupExpressions>() == 16);
    assert!(align_of::<Proth120LookupExpressions>() == 8);
};

impl From<&PRLinearRelation> for Proth120LinearRelation {
    fn from(value: &PRLinearRelation) -> Self {
        let len = value.linear_terms.len();
        assert!(
            len <= MAX_LINEAR_TERMS_COUNT,
            "Proth120 lookup relation has {len} terms, at most {MAX_LINEAR_TERMS_COUNT} are supported"
        );
        let mut terms = [Proth120LinearTerm::default(); MAX_LINEAR_TERMS_COUNT];
        for (&(coefficient, address), dst) in value.linear_terms.iter().zip(terms.iter_mut()) {
            let address = match address {
                GKRAddress::BaseLayerMemory(_)
                | GKRAddress::BaseLayerWitness(_)
                | GKRAddress::ScratchSpace(_) => Address::from(address),
                address => {
                    panic!("Proth120 lookup relation term reads unsupported address {address:?}")
                }
            };
            *dst = Proth120LinearTerm {
                coefficient,
                address,
                padding: 0,
            };
        }
        Self {
            constant: value.constant,
            terms,
            terms_count: len as u32,
            padding: [0; 3],
        }
    }
}

struct Proth120RelationSet {
    _host: Option<StaticPinnedBox<Proth120LinearRelation>>,
    device: Option<DeviceAllocation<Proth120LinearRelation>>,
    count: u32,
}

impl Proth120RelationSet {
    fn new(
        relations: &[PRSingleColumnLookupRelation],
        context: &ProverContext,
    ) -> CudaResult<Self> {
        if relations.is_empty() {
            return Ok(Self {
                _host: None,
                device: None,
                count: 0,
            });
        }
        let converted: Vec<Proth120LinearRelation> = relations
            .iter()
            .map(|relation| (&relation.input).into())
            .collect();
        assert!(converted.len() <= u32::MAX as usize);
        let count = converted.len() as u32;
        let host = alloc_static_pinned_box_from_slice(&converted)?;
        let mut device = context.alloc(converted.len(), AllocationPlacement::BestFit)?;
        memory_copy_async(&mut device, &*host, context.get_exec_stream())?;
        Ok(Self {
            _host: Some(host),
            device: Some(device),
            count,
        })
    }

    fn expressions(&self) -> Proth120LookupExpressions {
        Proth120LookupExpressions {
            relations: self
                .device
                .as_ref()
                .map_or(std::ptr::null(), |device| device.as_ptr()),
            count: self.count,
            padding: 0,
        }
    }
}

/// Owns pinned H2D sources, so it must be kept until the completion event of the last launch that reads it.
pub struct Proth120LookupRelations {
    range_check_16: Proth120RelationSet,
    timestamp: Proth120RelationSet,
}

impl Proth120LookupRelations {
    pub(crate) fn expressions(&self) -> (Proth120LookupExpressions, Proth120LookupExpressions) {
        (
            self.range_check_16.expressions(),
            self.timestamp.expressions(),
        )
    }

    pub(crate) fn counts(&self) -> (usize, usize) {
        (
            self.range_check_16.count as usize,
            self.timestamp.count as usize,
        )
    }
}

pub fn prepare_lookup_relations(
    circuit: &GKRCircuitArtifact<PR>,
    context: &ProverContext,
) -> CudaResult<Proth120LookupRelations> {
    Ok(Proth120LookupRelations {
        range_check_16: Proth120RelationSet::new(
            &circuit.range_check_16_lookup_expressions,
            context,
        )?,
        timestamp: Proth120RelationSet::new(
            &circuit.timestamp_range_check_lookup_expressions,
            context,
        )?,
    })
}
