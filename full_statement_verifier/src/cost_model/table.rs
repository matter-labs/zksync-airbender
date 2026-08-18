//! Calibrated coefficients for `estimate_verifier_cycles`: `c0` is one fsv guest
//! run's composition-independent cost, `v` prices one additional proof of each
//! compiled circuit. Both are guest cycle counts, measured by tracing the
//! transpiler VM over real recursion proofs.
//!
//! Regenerate from the four calibration fixtures (how to produce them: the module
//! docs of `full_statement_verifier/tests/cost_model_trace.rs`):
//!
//! ```text
//! COST_MODEL_FIXTURE_DIR=<dir> RUST_MIN_STACK=1073741824 RUSTFLAGS="-Awarnings" \
//!   cargo test -p full_statement_verifier --features host_utils,verifiers \
//!   --test cost_model_trace -- --ignored --nocapture
//! ```
//!
//! `emit_cost_tables` prints the replacement for `TABLES` below; paste it and drop
//! the trailing `// unpriced:` line. `estimate_matches_measurement_on_every_fixture`
//! is the acceptance gate.
//!
//! Invalidated by anything that moves the guest's instruction stream: a rebuilt fsv
//! guest under `tools/gkr_verifier`, a regenerated circuit under
//! `cs/compiled_circuits`, a change to the verifier's circuit lists or their order,
//! a different security level or `BlakeMode`.
//!
//! The blake2 g-function delegation is deliberately unpriced: no workload in scope
//! uses it, so no fixture exercises it. A proof carrying it is rejected with
//! `EstimateError::UnpricedCircuit` rather than estimated. Bringing it into scope
//! means adding a fixture with at least two of its proofs -- it sits in the
//! epilogue-tail region, where a singleton cannot be priced.

use super::{CircuitId, CostTable};
use verifier_common::fsv_binaries::{BlakeMode, FsvProgram};

pub static TABLES: &[(FsvProgram, BlakeMode, CostTable)] = &[
    (
        FsvProgram::UnrolledBaseLayer,
        BlakeMode::Compression,
        CostTable {
            c0: 829388,
            v: &[
                (CircuitId::Riscv(1), 836806),
                (CircuitId::Riscv(2), 860392),
                (CircuitId::Riscv(3), 871878),
                (CircuitId::Riscv(4), 859852),
                (CircuitId::Riscv(16), 828582),
                (CircuitId::Riscv(17), 844210),
                (CircuitId::Delegation(1991), 2328581),
                (CircuitId::Delegation(1994), 1263472),
                (CircuitId::Delegation(1995), 1240848),
            ],
        },
    ),
    (
        FsvProgram::UnrolledRecursionLayer,
        BlakeMode::Compression,
        CostTable {
            c0: 817362,
            v: &[
                (CircuitId::Riscv(1), 836806),
                (CircuitId::Riscv(2), 860392),
                (CircuitId::Riscv(3), 871878),
                (CircuitId::Riscv(16), 828582),
                (CircuitId::Delegation(1991), 2328581),
                (CircuitId::Delegation(1994), 1263472),
                (CircuitId::Delegation(1995), 1240848),
            ],
        },
    ),
];
