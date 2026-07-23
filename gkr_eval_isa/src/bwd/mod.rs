//! Backward-eval VM (spec §2). CPU compiler + interpreter for the GKR
//! backward-sumcheck instrument. Sibling of `fwd`; owns its own descriptor
//! namespace (`BwdSpecialTable`) — never shares fwd's `SpecialTable`.
pub mod batch;
pub mod compile;
pub mod construct;
pub mod cost;
pub mod disasm;
pub mod distill;
pub mod engine;
pub mod fif;
pub mod fragment;
pub mod interp;
pub mod plan;
pub mod price;
pub mod search;
pub mod source;
mod structure;
pub mod trace;
