//! Backward-eval VM (spec §2). CPU compiler + interpreter for the GKR
//! backward-sumcheck instrument. Sibling of `fwd`; owns its own descriptor
//! namespace (`BwdSpecialTable`) — never shares fwd's `SpecialTable`.
pub mod source;
pub mod distill;
pub mod compile;
pub mod construct;
pub mod cost;
pub mod fif;
pub mod interp;
pub mod plan;
pub mod search;
pub mod trace;
mod structure;
