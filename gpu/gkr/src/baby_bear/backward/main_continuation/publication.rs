use std::collections::BTreeMap;

use gpu_core::primitives::{context::DeviceAllocation, field::E4};

use crate::{backward::main_continuation::publication::*, upstream::GKRAddress};

/// Owns the dense source-ID columns written by a continuation producer.
pub(crate) struct ContinuationPublishedLevel {
    shape: ContinuationPublishedShape,
    allocation: DeviceAllocation<E4>,
}

impl ContinuationPublishedLevel {
    pub(crate) fn try_new(
        shape: ContinuationPublishedShape,
        allocation: DeviceAllocation<E4>,
    ) -> Result<Self, ContinuationPublicationError> {
        let expected = shape_elems(shape)?;
        let actual = allocation.len();
        if actual != expected {
            return Err(ContinuationPublicationError::AllocationLength { expected, actual });
        }
        Ok(Self { shape, allocation })
    }

    pub(crate) fn shape(&self) -> ContinuationPublishedShape {
        self.shape
    }

    pub(crate) fn allocation(&self) -> &DeviceAllocation<E4> {
        &self.allocation
    }

    pub(crate) fn as_ptr(&self) -> *const E4 {
        self.allocation.as_ptr()
    }
}

pub(crate) fn repoint_final_evaluations_from_raw<E>(
    base: *const E4,
    allocation_bytes: usize,
    elements_per_address: usize,
    byte_offsets: &BTreeMap<GKRAddress, usize>,
    destinations: &mut BTreeMap<GKRAddress, *const E>,
) -> Result<(), FinalEvaluationRepointError> {
    if elements_per_address == 0 {
        return Err(FinalEvaluationRepointError::ZeroElementSpan);
    }
    let element_bytes = size_of::<E>();
    let span_bytes = elements_per_address.checked_mul(element_bytes).ok_or(
        FinalEvaluationRepointError::ElementSpanOverflow {
            element_count: elements_per_address,
            element_bytes,
        },
    )?;
    // Validate the complete map before mutating a pointer so a bad address or
    // offset cannot leave a partially repointed final-evaluation set.
    for address in destinations.keys() {
        let offset = *byte_offsets
            .get(address)
            .ok_or(FinalEvaluationRepointError::MissingAddress { address: *address })?;
        let end = offset.checked_add(span_bytes).ok_or(
            FinalEvaluationRepointError::OffsetOutOfBounds {
                offset,
                element_count: elements_per_address,
                element_bytes,
                allocation_bytes,
            },
        )?;
        if end > allocation_bytes {
            return Err(FinalEvaluationRepointError::OffsetOutOfBounds {
                offset,
                element_count: elements_per_address,
                element_bytes,
                allocation_bytes,
            });
        }
    }
    for (address, pointer) in destinations.iter_mut() {
        let offset = byte_offsets[address];
        *pointer = base.cast::<u8>().wrapping_add(offset).cast::<E>();
    }
    Ok(())
}

#[cfg(test)]
mod cpu_continuation_published_level {
    use std::collections::BTreeMap;

    use super::FinalEvaluationRepointError;
    use crate::upstream::GKRAddress;

    fn address(offset: usize) -> GKRAddress {
        GKRAddress::ScratchSpace(offset)
    }

    #[test]
    fn cpu_continuation_published_level_repoints_without_a_round_vector() {
        let offsets = BTreeMap::from([(address(3), 0usize), (address(8), 64usize)]);
        let destinations = crate::baby_bear::backward::final_evaluation_repoint_probe(
            128,
            2,
            &offsets,
            [address(3), address(8)],
        )
        .unwrap();
        assert_eq!(destinations[&address(3)], 0);
        assert_eq!(destinations[&address(8)], 64);
        assert!(crate::baby_bear::backward::final_evaluation_repoint_probe(
            80,
            2,
            &offsets,
            [address(8)],
        )
        .is_err());
        assert!(crate::baby_bear::backward::final_evaluation_repoint_probe(
            128,
            2,
            &offsets,
            [address(99)],
        )
        .is_err());
        assert!(crate::baby_bear::backward::final_evaluation_repoint_probe(
            128,
            usize::MAX,
            &offsets,
            [address(3)],
        )
        .is_err());

        let mut span_destination = BTreeMap::from([(
            address(3),
            std::ptr::null::<gpu_core::primitives::field::E4>(),
        )]);
        assert!(matches!(
            crate::baby_bear::backward::main_continuation::publication::repoint_final_evaluations_from_raw(
                0x10_000usize as *const gpu_core::primitives::field::E4,
                128,
                0,
                &offsets,
                &mut span_destination,
            ),
            Err(FinalEvaluationRepointError::ZeroElementSpan)
        ));
        assert!(matches!(
            crate::baby_bear::backward::main_continuation::publication::repoint_final_evaluations_from_raw(
                0x10_000usize as *const gpu_core::primitives::field::E4,
                128,
                usize::MAX,
                &offsets,
                &mut span_destination,
            ),
            Err(FinalEvaluationRepointError::ElementSpanOverflow { .. })
        ));
        let overflow_offsets = BTreeMap::from([(address(3), usize::MAX - 8)]);
        assert!(matches!(
            crate::baby_bear::backward::main_continuation::publication::repoint_final_evaluations_from_raw(
                0x10_000usize as *const gpu_core::primitives::field::E4,
                usize::MAX,
                2,
                &overflow_offsets,
                &mut span_destination,
            ),
            Err(FinalEvaluationRepointError::OffsetOutOfBounds { .. })
        ));

        let mut partial_guard = BTreeMap::from([
            (address(3), std::ptr::null::<u32>()),
            (address(99), std::ptr::null::<u32>()),
        ]);
        assert!(crate::baby_bear::backward::main_continuation::publication::repoint_final_evaluations_from_raw(
            0x10_000usize as *const gpu_core::primitives::field::E4,
            128,
            2,
            &offsets,
            &mut partial_guard,
        )
        .is_err());
        assert!(partial_guard.values().all(|pointer| pointer.is_null()));
    }
}
