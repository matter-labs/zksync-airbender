pub(crate) use crate::backward::main_continuation::{
    binding::pointer_ranges_overlap,
    publication::{ContinuationPublicationError, ContinuationPublishedShape},
};

pub(crate) mod binding;
pub(crate) mod publication;
