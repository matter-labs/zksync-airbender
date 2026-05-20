//! GKR-pipeline program proving orchestration.
//!
//! Two modes:
//!
//! * [`per_family`]: prove a program with the per-opcode-family decomposition —
//!   6 family circuits + one inits-and-teardowns circuit + per-CSR delegations.
//! * [`unified`]: prove a program with the single unified reduced-machine
//!   circuit (subsumes the 6 families + inline i/t) + per-CSR delegations.
//!
//! Both modes share the program execution capture (see [`common`]) and the
//! delegation prove logic (see [`delegations`]). Each mode wires up a
//! Fiat–Shamir derived `pow_challenge` + `external_challenges` (necessary for
//! FSV verification, where the verifier re-derives them via
//! `draw_from_transcript_seed` and asserts match).

pub mod common;
pub mod delegations;
pub mod per_family;
pub mod unified;
