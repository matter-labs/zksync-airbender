//! gkr_eval_isa: the GKR forward-eval VM compiler (`fwd`) — lowers a DAG-IR
//! layer to the single-accumulator forward-VM ISA — plus the schedule-search
//! optimizer (`schedule_search`) that drives its cache/residency decisions.

pub mod bwd;
pub mod fwd;
pub mod schedule_search;
