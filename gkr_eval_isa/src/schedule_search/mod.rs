//! Schedule search (Stage 2b): DagLayer-native genome structure + the DAG-intrinsic
//! traffic floor the search compares against. This is the production home the
//! test-only `gkr_eval_isa/tests/s3_gap`/`s3_planner` prototypes are being promoted
//! into (Task 5); see each submodule's docs for the provenance of what moved.

pub mod floor;
pub mod structure;
