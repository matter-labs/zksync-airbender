//! Backward-eval VM (spec §2). CPU compiler + interpreter for the GKR
//! backward-sumcheck instrument. Sibling of `fwd`; owns its own descriptor
//! namespace (`BwdSpecialTable`) — never shares fwd's `SpecialTable`.
pub mod batch;
pub mod source;
pub mod distill;
pub mod compile;
pub mod fragment;
pub mod construct;
pub mod cost;
pub mod engine;
pub mod fif;
pub mod interp;
pub mod plan;
pub mod price;
pub mod search;
pub mod trace;
mod structure;
