//! Backward-eval VM (spec §2). CPU compiler + interpreter for the GKR
//! backward-sumcheck instrument. Sibling of `fwd`; owns its own descriptor
//! namespace (`BwdSpecialTable`) — never shares fwd's `SpecialTable`.
pub mod source;
// pub mod distill; // Task 4
// pub mod compile; // Task 5
// pub mod interp; // Task 6
