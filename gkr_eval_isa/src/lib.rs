//! gkr_eval_isa: the GKR forward-eval VM compiler (`fwd`) — lowers a DAG-IR
//! layer to the single-accumulator forward-VM ISA — plus the schedule-search
//! optimizer (`schedule_search`) that drives its cache/residency decisions.

pub mod bwd;
pub mod eval_plan;
pub mod fwd;
/// Crate-internal shared primitive: the offline interval packer both the forward
/// Stage-3 allocator and the backward coefficient placer run. Not part of the
/// crate's public surface.
pub(crate) mod interval_pack;
pub mod schedule;
pub mod schedule_search;
/// Crate-internal shared primitive: the final source-window binder both the
/// forward `Program` adapter and the backward coefficient schedule run. Not part
/// of the crate's public surface.
pub(crate) mod source_bind;

pub use bwd::domain::{
    BwdRegime, CacheFence, bwd_cache_fences, bwd_traffic_floor, enumerate_bwd_site_domain,
};
pub use schedule::*;
