//! Purpose: let soundness-regression tests inject a single, controlled
//! divergence into an otherwise-honest proof (e.g. perturb a grand-product
//! cache eval while leaving the committed base columns intact) so a verifier
//! test can assert the proof is REJECTED. Used to guard:
//!   - the MemoryTuple grand-product cache must be bound
//!     to the base (address/timestamp/value) columns. A perturbed cache eval
//!     on an active row must be rejected (`ForgeSite::MemTupleCache`).
//!   - Negative control: a bound single-column lookup / range-check cache is
//!     already bound, so the same perturbation must be rejected even without
//!     the memtuple fix (`ForgeSite::SingleColumnLookupCache`).

use std::sync::RwLock;

use field::Field;

/// A point in the prover pipeline at which a test may inject a perturbation.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ForgeSite {
    MemTupleCache,
    SingleColumnLookupCache,
}

/// A single forge directive: perturb `site` at trace row `row`.
#[derive(Clone, Copy, Debug)]
pub struct Forge {
    pub site: ForgeSite,
    pub row: usize,
}

// Process-global (NOT thread-local): the prover materializes on a worker thread
// pool, so the forge set must be visible to every worker. Written only by tests
// (which run generation serially, calling `clear` between fixtures); read
// uncontended during a prove, so the per-row `read()` is cheap.
static ACTIVE: RwLock<Vec<Forge>> = RwLock::new(Vec::new());

/// Register a forge directive. Test-only.
pub fn register(forge: Forge) {
    ACTIVE.write().unwrap().push(forge);
}

/// Remove all registered forge directives. Test-only. Call between fixtures.
pub fn clear() {
    ACTIVE.write().unwrap().clear();
}

/// If a forge is registered for `(site, row)`, perturb `value` by adding one
pub fn perturb<T: Field>(site: ForgeSite, row: usize, value: &mut T) -> bool {
    let hit = ACTIVE
        .read()
        .unwrap()
        .iter()
        .any(|f| f.site == site && f.row == row);
    if hit {
        value.add_assign(&T::ONE);
    }
    hit
}
