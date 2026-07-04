//! Schedule search (Stage 2b): DagLayer-native genome structure, the DAG-intrinsic
//! traffic floor the search compares against, and the compile-in-loop metaheuristic
//! that produces a `CircuitSchedule` (Task 6). This is the production home the
//! test-only `gkr_eval_isa/tests/s3_gap`/`s3_planner` prototypes were promoted into
//! (Tasks 5-6, see each submodule's docs for the provenance of what moved) — the
//! `s3_planner` event-replay simulation (`Replay`/`forkset`/`StepPlanRaw`) is deleted:
//! the scorer compiles candidates for real instead of simulating them.

pub mod decode;
pub mod floor;
pub mod genome;
pub mod producer;
pub mod scorer;
pub mod search;
pub mod structure;
