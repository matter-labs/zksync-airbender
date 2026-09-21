//! Shared host traces -> what the CPU primitives take.
//!
//! Nothing here owns a producer's block: an adapter borrows the trace for the
//! life of the request, so the completion can hand every block back.

pub(crate) mod inits_and_teardowns;
pub(crate) mod rows;
