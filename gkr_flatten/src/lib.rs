//! Deterministic oracle-driven DAG flattener: `elaborate(dag, oracle) →
//! LinearIR`. M0 (sizing DP), M1 (walker + interpreter + value parity), M2
//! (simulated cache residency, site-domain enumeration, genome encoding, and
//! greedy/GA search), and M3 (dead-aware eviction, the derived/biased/
//! searched fold-order policies, per-fold feasibility clamping, and the
//! `order_bias` genome extension) are delivered.
//!
//! Module map:
//! - [`dag`]: read-only `DagLayer` view (leaf classification, widths).
//! - [`su`]: the streaming-unit peak model (`cone_peak`/`streamable`).
//! - [`analysis`]: the all-recompute sizing DP (`sites`/`peak`/`ceiling`).
//! - [`ir`]: `LinearIR` `Program` representation + its interpreter.
//! - [`oracle`] / [`walk`]: the flattener itself (`flatten`/
//!   `flatten_budgeted`) driven by an `Oracle`'s root order and
//!   cache-admission decisions; `oracle` also owns the M2 site-domain
//!   enumeration (`SiteTable`); `walk` also threads the M3 `OrderPolicy`/
//!   `OrderCtx` order channel and per-value use countdown
//!   (`flatten_with`/`flatten_counted`).
//! - [`order`]: the M3 order channel (`OrderCtx`) — per-value dies-in/fills
//!   queries, static-peak feasibility (`order_feasible`), and the
//!   `OrderPolicy` selector the walker's derived/biased/searched fold
//!   ordering consults. Read-only: it decides nothing about caching.
//! - [`residency`]: the simulated cache/stash lane pool (`Residency`,
//!   M2 strictly-lower eviction, M3 dead-first: exhausted residents are
//!   reclaimable by any admission regardless of priority) the walker
//!   consults for hit/admission/eviction decisions under a budget.
//! - [`genome`]: the keep-gene encoding (`Genome`/`decode`) a search
//!   mutates/recombines, decoded into a `GenomeOracle` the walker consumes;
//!   M3 adds a locus-aligned `order_bias` gene consulted only by the
//!   `DerivedBiased`/`Searched` order policies.
//! - [`search`]: the objective (`Score`), zero-search baselines, CELF priced
//!   greedy, and the memetic GA over `genome::Genome`.
//! - [`resolvers`]: the shared production resolver (`HashResolvers`) used by
//!   this crate's value-parity tests and the M1/M2 parity gates.
//! - [`fixtures`]: on-disk loading of the real compiled-circuit layers this
//!   crate's tests and sweeps exercise.
//!
//! See `.agents/specs/2026-07-15-gkr-flattener-design.md` for the M0-M2
//! design and `.agents/specs/2026-07-16-gkr-flattener-m3-order-design.md`
//! for M3.

pub mod analysis;
pub mod dag;
pub mod fixtures;
pub mod genome;
pub mod ir;
pub mod oracle;
pub mod order;
pub mod residency;
pub mod resolvers;
pub mod search;
pub mod su;
pub mod walk;
