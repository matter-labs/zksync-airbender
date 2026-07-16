//! Deterministic oracle-driven DAG flattener: `elaborate(dag, oracle) →
//! LinearIR`. M0 (sizing DP), M1 (walker + interpreter + value parity), and
//! M2 (simulated cache residency, site-domain enumeration, genome encoding,
//! and greedy/GA search) are delivered; M3 (derived order keys, after-set
//! prediction, order-bias genes, feasibility clamping) is out of scope for
//! this crate as it stands.
//!
//! Module map:
//! - [`dag`]: read-only `DagLayer` view (leaf classification, widths).
//! - [`su`]: the streaming-unit peak model (`cone_peak`/`streamable`).
//! - [`analysis`]: the all-recompute sizing DP (`sites`/`peak`/`ceiling`).
//! - [`ir`]: `LinearIR` `Program` representation + its interpreter.
//! - [`oracle`] / [`walk`]: the flattener itself (`flatten`/
//!   `flatten_budgeted`) driven by an `Oracle`'s root order and
//!   cache-admission decisions; `oracle` also owns the M2 site-domain
//!   enumeration (`SiteTable`).
//! - [`residency`]: the M2 simulated cache/stash lane pool (`Residency`) the
//!   walker consults for hit/admission/eviction decisions under a budget.
//! - [`genome`]: the M2 keep-gene encoding (`Genome`/`decode`) a search
//!   mutates/recombines, decoded into a `GenomeOracle` the walker consumes.
//! - [`search`]: the M2 objective (`Score`), zero-search baselines, CELF
//!   priced greedy, and the memetic GA over `genome::Genome`.
//! - [`resolvers`]: the shared production resolver (`HashResolvers`) used by
//!   this crate's value-parity tests and the M1/M2 parity gates.
//! - [`fixtures`]: on-disk loading of the real compiled-circuit layers this
//!   crate's tests and sweeps exercise.
//!
//! See `.agents/specs/2026-07-15-gkr-flattener-design.md` for the full design.

pub mod analysis;
pub mod dag;
pub mod fixtures;
pub mod genome;
pub mod ir;
pub mod oracle;
pub mod residency;
pub mod resolvers;
pub mod search;
pub mod su;
pub mod walk;
