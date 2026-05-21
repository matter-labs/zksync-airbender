//! GKR-pipeline program proving orchestration.
//!
//! Two modes:
//!
//! * [`per_family`]: prove a program with the per-opcode-family decomposition —
//!   5 per-opcode family circuits + one inits-and-teardowns circuit + per-CSR
//!   delegations.
//! * [`unified`]: prove a program with the single unified reduced-machine
//!   circuit (subsumes 4 of the per-opcode families — add_sub_lui_auipc_mop,
//!   jump_branch_slt, binary_shifts, mem_word_only — plus inline i/t) +
//!   per-CSR delegations. mem_subword_only is NOT subsumed and runs as a
//!   separate circuit alongside.
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
