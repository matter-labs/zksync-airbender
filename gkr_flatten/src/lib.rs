//! Deterministic oracle-driven DAG flattener: `elaborate(dag, oracle) →
//! LinearIR`. M0 (sizing DP) and M1 (walker + interpreter + value parity)
//! are delivered; M2 (residency/accounting/search) and M3 (derived-order A/B)
//! are out of scope for this crate as it stands.
//!
//! Module map:
//! - [`dag`]: read-only `DagLayer` view (leaf classification, widths).
//! - [`su`]: the streaming-unit peak model (`cone_peak`/`streamable`).
//! - [`analysis`]: the all-recompute sizing DP (`sites`/`peak`/`ceiling`).
//! - [`ir`]: `LinearIR` `Program` representation + its interpreter.
//! - [`oracle`] / [`walk`]: the flattener itself (`flatten`) driven by an
//!   `Oracle`'s root order and cache decisions.
//! - [`resolvers`]: the value-parity test harness (shared hash resolvers).
//!
//! See `.agents/specs/2026-07-15-gkr-flattener-design.md` for the full design.

pub mod analysis;
pub mod dag;
pub mod fixtures;
pub mod ir;
pub mod oracle;
pub mod resolvers;
pub mod residency;
pub mod su;
pub mod walk;
