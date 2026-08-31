use std::collections::BTreeMap;

use gpu_core::primitives::context::DeviceAllocation;
use gpu_core::primitives::field::E4;
use gpu_gkr_compiler::SourceId;

use crate::upstream::GKRAddress;

/// Geometry of one canonical, dense `SourceId` publication arena.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ContinuationPublishedShape {
    pub(crate) depth: u8,
    pub(crate) columns: usize,
    pub(crate) column_elems: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ContinuationPublicationError {
    EmptyShape,
    ShapeElementCountOverflow,
    AllocationLength {
        expected: usize,
        actual: usize,
    },
    SourceOutOfBounds {
        source: SourceId,
        columns: usize,
    },
    DuplicateSemanticSource {
        source: SourceId,
    },
    MissingSemanticSource {
        source: SourceId,
    },
    NonCanonicalSourceColumn {
        source: SourceId,
        expected: usize,
        actual: usize,
    },
}

impl core::fmt::Display for ContinuationPublicationError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for ContinuationPublicationError {}

fn shape_elems(shape: ContinuationPublishedShape) -> Result<usize, ContinuationPublicationError> {
    if shape.columns == 0 || shape.column_elems == 0 {
        return Err(ContinuationPublicationError::EmptyShape);
    }
    shape
        .columns
        .checked_mul(shape.column_elems)
        .ok_or(ContinuationPublicationError::ShapeElementCountOverflow)
}

pub(crate) fn validate_canonical_publication(
    shape: ContinuationPublishedShape,
    publication: impl IntoIterator<Item = (SourceId, usize)>,
) -> Result<(), ContinuationPublicationError> {
    shape_elems(shape)?;
    let mut seen = vec![false; shape.columns];
    for (source, column) in publication {
        let source_index = usize::try_from(source.0).map_err(|_| {
            ContinuationPublicationError::SourceOutOfBounds {
                source,
                columns: shape.columns,
            }
        })?;
        if source_index >= shape.columns {
            return Err(ContinuationPublicationError::SourceOutOfBounds {
                source,
                columns: shape.columns,
            });
        }
        if seen[source_index] {
            return Err(ContinuationPublicationError::DuplicateSemanticSource { source });
        }
        seen[source_index] = true;
        if column != source_index {
            return Err(ContinuationPublicationError::NonCanonicalSourceColumn {
                source,
                expected: source_index,
                actual: column,
            });
        }
    }
    if let Some(missing) = seen.iter().position(|present| !present) {
        return Err(ContinuationPublicationError::MissingSemanticSource {
            source: SourceId(missing as u32),
        });
    }
    Ok(())
}

/// Sole owner of a canonical continuation publication arena.
///
/// Construction validates the producer's independently supplied semantic
/// source-to-column map. Because fields are private and the type is not
/// cloneable, canonical dense `SourceId` order is thereafter a type invariant;
/// adoption needs to revalidate only consumer geometry.
pub(crate) struct ContinuationPublishedLevel {
    shape: ContinuationPublishedShape,
    allocation: DeviceAllocation<E4>,
}

impl ContinuationPublishedLevel {
    pub(crate) fn try_new(
        shape: ContinuationPublishedShape,
        allocation: DeviceAllocation<E4>,
        publication: impl IntoIterator<Item = (SourceId, usize)>,
    ) -> Result<Self, ContinuationPublicationError> {
        let publication: Vec<_> = publication.into_iter().collect();
        validate_canonical_publication(shape, publication.iter().copied())?;
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum FinalEvaluationRepointError {
    MissingAddress {
        address: GKRAddress,
    },
    ZeroElementSpan,
    ElementSpanOverflow {
        element_count: usize,
        element_bytes: usize,
    },
    OffsetOutOfBounds {
        offset: usize,
        element_count: usize,
        element_bytes: usize,
        allocation_bytes: usize,
    },
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

    use gpu_gkr_compiler::SourceId;

    use crate::upstream::GKRAddress;

    use super::{
        validate_canonical_publication, ContinuationPublicationError, FinalEvaluationRepointError,
    };
    use crate::backward::ContinuationPublishedShape;

    fn address(offset: usize) -> GKRAddress {
        GKRAddress::ScratchSpace(offset)
    }

    #[test]
    fn cpu_continuation_published_level_rejects_noncanonical_source_columns() {
        let shape = ContinuationPublishedShape {
            depth: 12,
            columns: 3,
            column_elems: 16,
        };
        assert_eq!(
            validate_canonical_publication(
                shape,
                [(SourceId(0), 0), (SourceId(1), 1), (SourceId(2), 2)],
            ),
            Ok(())
        );
        assert!(matches!(
            validate_canonical_publication(
                shape,
                [(SourceId(0), 0), (SourceId(1), 2), (SourceId(2), 1)],
            ),
            Err(ContinuationPublicationError::NonCanonicalSourceColumn { .. })
        ));
        assert!(matches!(
            validate_canonical_publication(shape, [(SourceId(0), 0), (SourceId(0), 1)]),
            Err(ContinuationPublicationError::DuplicateSemanticSource { .. })
        ));
        assert!(matches!(
            validate_canonical_publication(shape, [(SourceId(0), 0), (SourceId(1), 1)]),
            Err(ContinuationPublicationError::MissingSemanticSource { .. })
        ));
    }

    #[test]
    fn cpu_continuation_published_level_repoints_without_a_round_vector() {
        let offsets = BTreeMap::from([(address(3), 0usize), (address(8), 64usize)]);
        let destinations = crate::backward::final_evaluation_repoint_probe(
            128,
            2,
            &offsets,
            [address(3), address(8)],
        )
        .unwrap();
        assert_eq!(destinations[&address(3)], 0);
        assert_eq!(destinations[&address(8)], 64);
        assert!(
            crate::backward::final_evaluation_repoint_probe(80, 2, &offsets, [address(8)],)
                .is_err()
        );
        assert!(
            crate::backward::final_evaluation_repoint_probe(128, 2, &offsets, [address(99)],)
                .is_err()
        );
        assert!(crate::backward::final_evaluation_repoint_probe(
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
            super::repoint_final_evaluations_from_raw(
                0x10_000usize as *const gpu_core::primitives::field::E4,
                128,
                0,
                &offsets,
                &mut span_destination,
            ),
            Err(FinalEvaluationRepointError::ZeroElementSpan)
        ));
        assert!(matches!(
            super::repoint_final_evaluations_from_raw(
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
            super::repoint_final_evaluations_from_raw(
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
        assert!(super::repoint_final_evaluations_from_raw(
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
