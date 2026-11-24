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
    AllocationLength { expected: usize, actual: usize },
}

impl core::fmt::Display for ContinuationPublicationError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for ContinuationPublicationError {}

pub(crate) fn shape_elems(
    shape: ContinuationPublishedShape,
) -> Result<usize, ContinuationPublicationError> {
    if shape.columns == 0 || shape.column_elems == 0 {
        return Err(ContinuationPublicationError::EmptyShape);
    }
    shape
        .columns
        .checked_mul(shape.column_elems)
        .ok_or(ContinuationPublicationError::ShapeElementCountOverflow)
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
