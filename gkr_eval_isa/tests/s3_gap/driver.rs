//! Rust subprocess driver for the CP-SAT scheduling oracle (`oracle/solve.py`).
//!
//! `run_oracle` spawns `python3 {CARGO_MANIFEST_DIR}/oracle/solve.py`, pipes the
//! `OracleInstance` (+ `mode`/`mip_gap`/`max_secs`) as JSON to stdin, and parses
//! the `OracleResult` JSON from stdout. Tool absence (no `python3`, or
//! `ModuleNotFoundError: ortools`) maps to `io::ErrorKind::NotFound` so callers
//! can SKIP rather than fail.
//!
//! ## Solver self-test + within-stage capacity LOCK guards (audit HIGH-1)
//!
//! The within-stage capacity uses a STREAMING charge — a fold's transient peak
//! is `width(result) + max-single-operand` (accumulator + the single largest
//! operand being merged), a TRUE LOWER BOUND. Verify directly:
//!
//! ```text
//! # Self-test (recompute cost = 2 base reads) + both LOCK guards in one shot:
//! python3 gkr_eval_isa/oracle/solve.py --selftest
//!   → "recompute": {"status":"optimal","traffic":2}
//!   → "guard_4base": cliff 5  (Add(4 base)→ext infeasible@4, feasible@5 == 4+1)
//!   → "guard_4ext":  cliff 8  (Add(4 ext)→ext  infeasible@7, feasible@8/@16 == 4+4)
//!   → "guard_8ext":  cliff 8  (wider ext reduction; peak stays 8, feasible@16)
//!   → "all_pass": true ; exit 0
//!
//! # Guard 1 (sub-peak rejects) by hand — Add(4 base)→ext, budget below peak 5:
//! echo '{"budget":4,"mode":"J","roots":[4],"nodes":[
//!   {"id":0,"kind":"Read","width":1,"real_dram":true,"children":[]},
//!   {"id":1,"kind":"Read","width":1,"real_dram":true,"children":[]},
//!   {"id":2,"kind":"Read","width":1,"real_dram":true,"children":[]},
//!   {"id":3,"kind":"Read","width":1,"real_dram":true,"children":[]},
//!   {"id":4,"kind":"Add","width":4,"real_dram":false,"children":[0,1,2,3]}]}' \
//!   | python3 gkr_eval_isa/oracle/solve.py     # → "status":"infeasible"
//! # (same instance, budget 5)                  # → "status":"optimal"
//!
//! # Guard 2 (NOT over-rejected) by hand — Add(4 ext)→ext, budget 16:
//! echo '{"budget":16,"mode":"J","roots":[4],"nodes":[
//!   {"id":0,"kind":"Read","width":4,"real_dram":true,"children":[]},
//!   {"id":1,"kind":"Read","width":4,"real_dram":true,"children":[]},
//!   {"id":2,"kind":"Read","width":4,"real_dram":true,"children":[]},
//!   {"id":3,"kind":"Read","width":4,"real_dram":true,"children":[]},
//!   {"id":4,"kind":"Add","width":4,"real_dram":false,"children":[0,1,2,3]}]}' \
//!   | python3 gkr_eval_isa/oracle/solve.py     # → "status":"optimal" (un-relaxed: 20>16 infeasible)
//! ```
//!
//! The `#[ignore]`d driver test below is the Rust round-trip of the recompute
//! self-test. Run it with:
//! ```text
//! cargo test -p gkr_eval_isa --test s3_gap_experiment driver:: -- --ignored --nocapture
//! ```

use super::instance::OracleInstance;
use std::io::Write;
use std::process::{Command, Stdio};

#[derive(Clone, Copy)]
pub enum Mode {
    J,
    E,
}

#[derive(serde::Serialize, serde::Deserialize)]
pub struct OracleStage {
    pub stage: u32,
    pub root: u32,
    pub resident_after: Vec<u32>,
}

#[derive(serde::Serialize, serde::Deserialize)]
pub struct OracleResult {
    pub status: String,
    pub traffic: u64,
    pub instrs: u64,
    pub bound: u64,
    pub wall_ms: u64,
    pub schedule: Vec<OracleStage>,
}

/// Spawn the CP-SAT oracle, pipe `inst` (+ mode/mip_gap/max_secs) as JSON to
/// stdin, parse the `OracleResult` from stdout.
///
/// Maps solver-tool absence to [`std::io::ErrorKind::NotFound`]: a spawn ENOENT
/// (no `python3`) and a non-zero exit (e.g. `ModuleNotFoundError: ortools`) both
/// surface as `NotFound` so callers can skip rather than fail. A malformed
/// stdout maps to `InvalidData`.
pub fn run_oracle(
    inst: &OracleInstance,
    mode: Mode,
    mip_gap: f64,
    max_secs: u64,
) -> std::io::Result<OracleResult> {
    let script = format!("{}/oracle/solve.py", env!("CARGO_MANIFEST_DIR"));
    let mut payload = serde_json::to_value(inst).unwrap();
    payload["mode"] = serde_json::json!(match mode {
        Mode::J => "J",
        Mode::E => "E",
    });
    payload["mip_gap"] = serde_json::json!(mip_gap);
    payload["max_secs"] = serde_json::json!(max_secs);
    // spawn ENOENT (no python3) → NotFound; surfaces distinctly from a parse error.
    let mut child = Command::new("python3")
        .arg(&script)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    child
        .stdin
        .take()
        .unwrap()
        .write_all(payload.to_string().as_bytes())?;
    let out = child.wait_with_output()?;
    if !out.status.success() {
        // non-zero exit (e.g. `ModuleNotFoundError: ortools`) — tool absent/broken,
        // NOT a modeling bug. Map to NotFound so callers can skip rather than fail.
        return Err(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!(
                "oracle solver unavailable (python exit {:?}): {}",
                out.status.code(),
                String::from_utf8_lossy(&out.stderr)
            ),
        ));
    }
    let r: OracleResult = serde_json::from_slice(&out.stdout).map_err(|e| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            format!(
                "oracle parse: {e}; stdout={}",
                String::from_utf8_lossy(&out.stdout)
            ),
        )
    })?;
    Ok(r)
}

/// True iff python3 + ortools are importable — gate `#[ignore]`d tests / harness on this.
pub fn oracle_available() -> bool {
    std::process::Command::new("python3")
        .args(["-c", "from ortools.sat.python import cp_model"])
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .map(|s| s.success())
        .unwrap_or(false)
}

// ── Hand-built OracleInstance helpers for J-vs-E differential ───────────────

/// Order-sensitive instance: two ext Priors P1 (id=0) and P2 (id=1), three
/// fold roots R1=Add([P1]) (id=2), R2=Add([P2]) (id=3), R3=Add([P1,P2]) (id=4).
/// Budget = 12 (= 3×ext = enough to hold one ext resident while computing one ext fold).
///
/// ## Why the identity order pays one extra ext reload (traffic gap = +4)
///
/// Both P1 and P2 are needed by R3 (the last root in identity order).
/// Budget = 12 allows keeping at most ONE ext Prior resident while computing
/// another ext fold (resident 4 + fold-acc 4 + transient 4 = 12 = budget).
///
/// **J-optimal order: [R1, R3, R2] (root indices 0→2, 2→4, 1→3)**
///   t=0  compute R1=Add([P1])     load P1 (traffic 4); keep P1 resident
///         base = 4(P1) + 4(R1-acc) = 8; trans = 4(P1-operand); total = 12 ✓
///   t=1  compute R3=Add([P1,P2])  P1 available (no reload); load P2 (traffic 4)
///         base = 4(R3-acc) = 4; trans = 4(max-operand P2) = 4; total = 8 ✓
///         keep P2 resident (res[1,P2]=1 → live[1,P2]=1):
///         base = 4(P2) + 4(R3-acc) = 8; trans = 4; total = 12 ✓
///   t=2  compute R2=Add([P2])     P2 available (no reload); traffic = 0
///         base = 4(R2-acc) = 4; trans = 4(P2-operand); total = 8 ✓
///   **J traffic = 4 (P1) + 4 (P2) = 8**
///
/// **E (identity) order: [R1, R2, R3]**
///   t=0  compute R1=Add([P1])     load P1 (traffic 4); must keep P1 for t=2
///         keep P1 resident: base=4(P1)+4(R1)=8; trans=4; total=12 ✓
///   t=1  compute R2=Add([P2])     load P2 (traffic 4); keep P1 for t=2
///         must carry P1 (res[1,P1]=1 → live[1,P1]=1)
///         base = 4(P1) + 4(R2-acc) = 8; trans = 4(P2-operand); total = 12 ✓
///         but if also keeping P2 (res[1,P2]=1 → live[1,P2]=1):
///         base = 4(P1) + 4(P2) + 4(R2-acc) = 12; trans = 4; total = 16 > 12 ✗
///         → CANNOT keep both; at most one Prior can be carried across this stage
///   t=2  compute R3=Add([P1,P2])  P1 available; must reload P2 (traffic 4)
///         base = 4(R3-acc) = 4; trans = 4; total = 8 ✓
///   **E traffic = 4 (P1) + 4 (P2) + 4 (P2 reload) = 12**
///
/// Gap = E − J = 12 − 8 = +4 = one ext Prior reload.
pub fn order_sensitive_two_prior_instance() -> OracleInstance {
    use crate::s3_gap::instance::{NodeKind, OracleNode};
    OracleInstance {
        // budget 12: 3×ext-width; allows one ext Prior resident while computing one ext fold
        budget: 12,
        // root 0 → R1 (id=2), root 1 → R2 (id=3), root 2 → R3 (id=4)
        roots: vec![2, 3, 4],
        nodes: vec![
            OracleNode { id: 0, kind: NodeKind::Prior, width: 4, real_dram: true,  children: vec![] }, // P1
            OracleNode { id: 1, kind: NodeKind::Prior, width: 4, real_dram: true,  children: vec![] }, // P2
            OracleNode { id: 2, kind: NodeKind::Add,   width: 4, real_dram: false, children: vec![0] }, // R1=Add([P1])
            OracleNode { id: 3, kind: NodeKind::Add,   width: 4, real_dram: false, children: vec![1] }, // R2=Add([P2])
            OracleNode { id: 4, kind: NodeKind::Add,   width: 4, real_dram: false, children: vec![0, 1] }, // R3=Add([P1,P2])
        ],
    }
}

/// Order-insensitive instance: two independent single-Prior roots.
/// P1 is only used by R1; P2 is only used by R2.  No matter the order, each
/// Prior is loaded exactly once → J traffic == E traffic = 8.
pub fn order_insensitive_instance() -> OracleInstance {
    use crate::s3_gap::instance::{NodeKind, OracleNode};
    OracleInstance {
        budget: 8, // ext-fold streaming peak = 4+4 = 8; each root fits independently
        // root 0 → R1 (id=1), root 1 → R2 (id=3)
        roots: vec![1, 3],
        nodes: vec![
            OracleNode { id: 0, kind: NodeKind::Prior, width: 4, real_dram: true,  children: vec![] }, // P1
            OracleNode { id: 1, kind: NodeKind::Add,   width: 4, real_dram: false, children: vec![0] }, // R1=Add([P1])
            OracleNode { id: 2, kind: NodeKind::Prior, width: 4, real_dram: true,  children: vec![] }, // P2
            OracleNode { id: 3, kind: NodeKind::Add,   width: 4, real_dram: false, children: vec![2] }, // R2=Add([P2])
        ],
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::s3_gap::instance::{NodeKind, OracleNode};

    // #[ignore]: live-solver test, needs python3 + ortools (crate convention:
    // fwd_parity.rs:320/426, disasm_dump.rs:57 gate heavy/tool tests). Run with
    // `--ignored`. A plain `cargo test -p gkr_eval_isa` must NOT invoke the solver.
    #[test]
    #[ignore = "needs python3 + ortools; run with --ignored"]
    fn driver_solves_recompute_cost_two() {
        // ext = Add(base, base), budget 16. node 2 has no reload edge → this pins
        // recompute cost = 2 base reads (NOT a reload-vs-recompute choice; see model comment).
        let inst = OracleInstance {
            budget: 16,
            roots: vec![2],
            nodes: vec![
                OracleNode {
                    id: 0,
                    kind: NodeKind::Read,
                    width: 1,
                    real_dram: true,
                    children: vec![],
                },
                OracleNode {
                    id: 1,
                    kind: NodeKind::Read,
                    width: 1,
                    real_dram: true,
                    children: vec![],
                },
                OracleNode {
                    id: 2,
                    kind: NodeKind::Add,
                    width: 4,
                    real_dram: false,
                    children: vec![0, 1],
                },
            ],
        };
        let r = run_oracle(&inst, Mode::J, 0.0, 60).expect("python3+ortools available");
        assert_eq!(r.status, "optimal");
        assert_eq!(r.traffic, 2, "recompute cost = 2 base reads");
    }

    #[test]
    #[ignore = "needs python3 + ortools; run with --ignored"]
    fn fixed_order_costs_more_than_free_order_when_order_matters() {
        // See order_sensitive_two_prior_instance() for the hand-derived derivation.
        // Briefly: budget=12 lets J pick order [R1,R3,R2] (P1 used consecutively,
        // then P2 kept resident for R2) → traffic=8.  E (identity order [R1,R2,R3])
        // cannot keep both P1 and P2 resident at stage 1 → must reload one at
        // stage 2 → traffic=12.  Gap = +4 = one ext Prior reload.
        let inst = order_sensitive_two_prior_instance();
        let j = run_oracle(&inst, Mode::J, 0.0, 120).unwrap();
        let e = run_oracle(&inst, Mode::E, 0.0, 120).unwrap();
        println!("J: status={} traffic={} schedule={:?}", j.status, j.traffic,
            j.schedule.iter().map(|s| (s.stage, s.root)).collect::<Vec<_>>());
        println!("E: status={} traffic={} schedule={:?}", e.status, e.traffic,
            e.schedule.iter().map(|s| (s.stage, s.root)).collect::<Vec<_>>());
        assert_eq!(j.status, "optimal");
        assert_eq!(e.status, "optimal");
        assert!(j.traffic <= e.traffic, "J is the joint optimum, never worse than fixed-order E");
        assert!(j.traffic < e.traffic, "this instance is order-sensitive → J strictly cheaper");
    }

    #[test]
    #[ignore = "needs python3 + ortools; run with --ignored"]
    fn fixed_order_equals_free_order_when_order_irrelevant() {
        // independent single-read roots: order cannot change traffic
        let inst = order_insensitive_instance();
        let j = run_oracle(&inst, Mode::J, 0.0, 60).unwrap();
        let e = run_oracle(&inst, Mode::E, 0.0, 60).unwrap();
        println!("J: status={} traffic={}", j.status, j.traffic);
        println!("E: status={} traffic={}", e.status, e.traffic);
        assert_eq!(j.traffic, e.traffic, "no order sensitivity → J == E");
    }
}
