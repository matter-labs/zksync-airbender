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
//! The within-stage capacity charges the SEQUENTIAL (Sethi-Ullman) peak of each
//! root's cone — `peak(fold) = max(peak(c1), width + peak(c2))` over children
//! sorted by descending peak — a TRUE LOWER BOUND that, for a lone n-ary fold,
//! collapses to `width(result) + max-operand` (the single-fold guards are
//! therefore unchanged from the earlier streaming charge). Verify directly:
//!
//! ```text
//! # Self-test (recompute cost = 2 base reads) + all LOCK guards in one shot:
//! python3 gkr_eval_isa/oracle/solve.py --selftest
//!   → "recompute": {"status":"optimal","traffic":2}
//!   → "guard_4base": cliff 5  (Add(4 base)→ext infeasible@4, feasible@5 == 4+1)
//!   → "guard_4ext":  cliff 8  (Add(4 ext)→ext  infeasible@7, feasible@8/@16 == 4+4)
//!   → "guard_8ext":  cliff 8  (wider ext reduction; peak stays 8, feasible@16)
//!   → "guard_sop":   cliff 12 (sum-of-3-ext-products; OLD SUM model rejected @16,
//!                              sequential peak = max(8, 4+8) = 12, feasible@12/@16)
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

/// Order-sensitive instance: one ext Prior P1 (id=0) shared by two roots
/// R_a=Add([P1]) (id=3) and R_c=Add([P1]) (id=5), with an EXPENSIVE intervening
/// root R_b=Add([read,read]) (id=4) whose cone peak is 8.
///
/// ## Why the identity order pays one extra ext reload (traffic gap = +4)
///
/// Budget = 8. The sequential cone peaks are P[R_a]=P[R_c]=4 and P[R_b]=8 (an
/// ext fold of two ext reads: `max(4, 4+4) = 8`). Carrying P1 (4 cells) resident
/// *across* R_b's stage costs `4 + P[R_b] = 4 + 8 = 12 > 8` — impossible. So P1
/// can only stay resident across stages whose cone leaves room for it.
///
/// **E (identity) order: [R_a, R_b, R_c]** — R_b sits *between* the two P1 uses.
///   t=0  R_a=Add([P1])      load P1 (traffic 4)
///   t=1  R_b=Add([a,b])     load a,b (traffic 8); cannot also carry P1
///         (carry P1 4 + P[R_b] 8 = 12 > 8) → P1 evicted
///   t=2  R_c=Add([P1])      P1 gone → reload P1 (traffic 4)
///   **E traffic = 4 (P1) + 8 (R_b) + 4 (P1 reload) = 16**
///
/// **J-optimal order: [R_b, R_a, R_c]** — R_b moved out from between the P1 uses.
///   t=0  R_b=Add([a,b])     load a,b (traffic 8)
///   t=1  R_a=Add([P1])      load P1 (traffic 4); keep P1 resident (boundary 4 ≤ 8)
///   t=2  R_c=Add([P1])      P1 resident (no reload); traffic 0
///   **J traffic = 8 (R_b) + 4 (P1) = 12**
///
/// Gap = E − J = 16 − 12 = +4 = one ext Prior reload. (Under the earlier
/// over-strict `base+transient` charge the simpler two-Prior instance also read
/// as order-sensitive, but that sensitivity was a modeling artifact — the
/// corrected sequential peak lets a fixed order keep both Priors resident there,
/// so genuine order-sensitivity now requires an expensive *intervening* cone.)
pub fn order_sensitive_shared_prior_instance() -> OracleInstance {
    use crate::s3_gap::instance::{NodeKind, OracleNode};
    OracleInstance {
        // budget 8: P1(4) cannot be carried across R_b's cone peak (8) → 4+8 > 8
        budget: 8,
        // root 0 → R_a (id=3), root 1 → R_b (id=4), root 2 → R_c (id=5)
        roots: vec![3, 4, 5],
        nodes: vec![
            OracleNode { id: 0, kind: NodeKind::Prior, width: 4, real_dram: true,  children: vec![] },     // P1 (shared)
            OracleNode { id: 1, kind: NodeKind::Read,  width: 4, real_dram: true,  children: vec![] },     // R_b leaf a
            OracleNode { id: 2, kind: NodeKind::Read,  width: 4, real_dram: true,  children: vec![] },     // R_b leaf b
            OracleNode { id: 3, kind: NodeKind::Add,   width: 4, real_dram: false, children: vec![0] },    // R_a = Add([P1])
            OracleNode { id: 4, kind: NodeKind::Add,   width: 4, real_dram: false, children: vec![1, 2] }, // R_b = Add([a,b]) peak 8
            OracleNode { id: 5, kind: NodeKind::Add,   width: 4, real_dram: false, children: vec![0] },    // R_c = Add([P1])
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
        // See order_sensitive_shared_prior_instance() for the hand-derived
        // derivation. Briefly: budget=8, P1 is shared by R_a and R_c with an
        // expensive R_b (cone peak 8) between them in emission order. J reorders
        // R_b out from between the P1 uses (traffic 12); E (identity [R_a,R_b,R_c])
        // cannot carry P1 across R_b → reloads it (traffic 16). Gap = +4.
        let inst = order_sensitive_shared_prior_instance();
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
