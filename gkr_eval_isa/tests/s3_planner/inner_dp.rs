//! Inner planner: stage-indexed simulation + Belady stage-boundary leaf caching
//! (Task 3) + fork residency DP (Task 4). Objective matches the oracle: (traffic, instrs),
//! counted ONCE PER NODE PER STAGE (deduped cone set), residency at stage boundaries.

use super::forkset;
use crate::s3_gap::instance::{NodeKind, OracleInstance};

pub struct PlanResult {
    pub traffic: u64,
    pub instrs: u64,
    pub feasible: bool,
    pub order: Vec<u32>,
}
impl PlanResult {
    pub fn objective(&self) -> (u64, u64) {
        (self.traffic, self.instrs)
    }
}

pub fn plan_naive(inst: &OracleInstance) -> PlanResult {
    let (mut traffic, mut instrs) = (0u64, 0u64);
    for &root in &inst.roots {
        for v in forkset::cone(inst, root) {
            // deduped: each cone node once per stage
            let node = &inst.nodes[v as usize];
            if node.real_dram {
                traffic += node.width as u64;
            }
            if matches!(node.kind, NodeKind::Add | NodeKind::Mul | NodeKind::Special) {
                instrs += 1;
            }
        }
    }
    PlanResult {
        traffic,
        instrs,
        feasible: true,
        order: inst.roots.clone(),
    }
}

pub fn plan_belady_leaves(inst: &OracleInstance) -> PlanResult {
    let fi = forkset::analyze(inst);
    let t = inst.roots.len();
    // Per-stage distinct DRAM leaves + deduped recompute count.
    let mut stage_leaves: Vec<Vec<u32>> = Vec::with_capacity(t);
    let mut instrs = 0u64;
    for &root in &inst.roots {
        let c = forkset::cone(inst, root); // deduped node set
        let mut leaves = Vec::new();
        for &v in &c {
            let node = &inst.nodes[v as usize];
            if node.real_dram {
                leaves.push(v);
            }
            if matches!(node.kind, NodeKind::Add | NodeKind::Mul | NodeKind::Special) {
                instrs += 1;
            }
        }
        stage_leaves.push(leaves);
    }

    let budget = inst.budget;
    let width = |v: u32| inst.nodes[v as usize].width as usize;
    let mut resident: Vec<u32> = Vec::new();
    let mut used = 0usize;
    let mut traffic = 0u64;

    for ti in 0..t {
        for &v in &stage_leaves[ti] {
            if resident.contains(&v) {
                continue;
            } // hit (resident from a prior stage)
            traffic += width(v) as u64; // miss -> load
            while used + width(v) > budget && !resident.is_empty() {
                let victim_idx = (0..resident.len())
                    .max_by(|&a, &b| {
                        let na = next_demand_stage(&stage_leaves, ti, resident[a]);
                        let nb = next_demand_stage(&stage_leaves, ti, resident[b]);
                        na.cmp(&nb).then(resident[b].cmp(&resident[a])) // furthest; tie -> smallest id
                    })
                    .unwrap();
                let victim = resident.swap_remove(victim_idx);
                used -= width(victim);
            }
            if used + width(v) <= budget {
                resident.push(v);
                used += width(v);
            }
            // else: v alone exceeds budget — reloaded on each future demand.
        }
        // boundary cleanup: drop residents with no future demand.
        let mut i = 0;
        while i < resident.len() {
            if next_demand_stage(&stage_leaves, ti, resident[i]) == usize::MAX {
                let v = resident.swap_remove(i);
                used -= width(v);
            } else {
                i += 1;
            }
        }
    }

    let feasible = fi.root_peak.iter().all(|&p| (p as usize) <= budget); // (B)-only baseline
    PlanResult {
        traffic,
        instrs,
        feasible,
        order: inst.roots.clone(),
    }
}

/// Smallest stage index strictly greater than `ti` whose cone demands leaf `v`
/// (usize::MAX if none). Stage granularity matches the oracle's per-stage compute.
fn next_demand_stage(stage_leaves: &[Vec<u32>], ti: usize, v: u32) -> usize {
    for s in (ti + 1)..stage_leaves.len() {
        if stage_leaves[s].contains(&v) {
            return s;
        }
    }
    usize::MAX
}

// ── Fork-residency planner: enumerate fork trajectories, then Belady each ──────
//
// CORRECTNESS (systematic-debugging, seed-12): Belady must NOT be interleaved with
// the fork-keep decisions. Belady's next-use lookahead depends on which leaves are
// *shielded* by resident forks at FUTURE stages — decisions a forward DP has not
// made yet. Running Belady stage-by-stage with a shielding-blind (static-cone)
// demand string keeps leaves a later resident fork would shield, overflowing the
// budget and forcing a needless fork recompute (the (2,6)-vs-(2,5) bug). The fix is
// two-phase:
//   Phase A — enumerate every feasible fork-residency trajectory to the end (fork
//             choices fully locked in; per-stage recompute/instrs determined here).
//   Phase B — per complete trajectory the fork schedule is fixed, so each stage's
//             *shielded* DRAM-leaf demand is exact; run Belady over it for traffic.
//   Phase C — pick the min-objective trajectory.

pub struct PlanRun {
    pub result: PlanResult,
    pub max_frontier: usize,
}

/// Walk `cone(root)` but stop descending at any node in `resident` (those nodes
/// are free this stage and their sub-cones are NOT re-walked). Returns the set of
/// nodes actually *demanded* (computed) this stage, in sorted node-id order.
fn demanded_with_resident(inst: &OracleInstance, root: u32, resident: &[u32]) -> Vec<u32> {
    let mut is_res = vec![false; inst.nodes.len()];
    for &v in resident {
        is_res[v as usize] = true;
    }
    let mut seen = vec![false; inst.nodes.len()];
    let mut stack = vec![root];
    while let Some(v) = stack.pop() {
        if seen[v as usize] {
            continue;
        }
        seen[v as usize] = true;
        // A resident node is free: counted neither as traffic nor instr, and its
        // children are not re-walked.
        if is_res[v as usize] {
            continue;
        }
        for &c in &inst.nodes[v as usize].children {
            if !seen[c as usize] {
                stack.push(c);
            }
        }
    }
    // Demanded = reachable AND not resident (resident nodes were marked seen but
    // are free; exclude them from the computed set).
    (0..inst.nodes.len() as u32)
        .filter(|&v| seen[v as usize] && !is_res[v as usize])
        .collect()
}

/// Plan a fixed root order: enumerate all feasible fork-residency trajectories
/// (Phase A), Belady each one with its now-fixed shielded leaf demand (Phase B),
/// and return the min-objective `(traffic, instrs)` (Phase C). `max_frontier` is
/// the number of complete fork trajectories enumerated.
pub fn plan_fixed_order(inst: &OracleInstance) -> PlanRun {
    let fi = forkset::analyze(inst);
    let t = inst.roots.len();
    let budget = inst.budget;
    let width = |v: u32| inst.nodes[v as usize].width as usize;

    // Short-circuit (C): if any root's Sethi-Ullman cone peak alone exceeds the
    // budget, no schedule can materialize it — the instance is infeasible.
    if fi.root_peak.iter().any(|&p| (p as usize) > budget) {
        return PlanRun {
            result: PlanResult {
                traffic: u64::MAX,
                instrs: u64::MAX,
                feasible: false,
                order: inst.roots.clone(),
            },
            max_frontier: 0,
        };
    }

    // Per-stage full cone (sorted), for the cone-fit (C) outsider test and the
    // fork future-demand lookahead used to drop spent forks at each boundary.
    let stage_cones: Vec<Vec<u32>> = inst.roots.iter().map(|&r| forkset::cone(inst, r)).collect();
    let is_outsider = |s: usize, v: u32| -> bool { stage_cones[s].binary_search(&v).is_err() };
    let fork_demanded_after = |ti: usize, f: u32| -> bool {
        ((ti + 1)..t).any(|s| stage_cones[s].binary_search(&f).is_ok())
    };

    // ── Phase A: enumerate every feasible fork-residency trajectory ──
    // A trajectory is `schedule[ti]` = the (sorted) set of forks resident ENTERING
    // stage ti (schedule[0] = {}). The keep-decision after stage ti picks which
    // keepable forks survive to ti+1. No Belady/traffic here — only fork choices and
    // their (C)/budget feasibility (instrs follow from the fork schedule in Phase B).
    // DFS over partial schedules; each pop processes the last (current) stage.
    const HARD_CAP: usize = 2_000_000; // loud failure beats OOM on a pathological instance
    let mut trajectories: Vec<Vec<Vec<u32>>> = Vec::new();
    let mut stack: Vec<Vec<Vec<u32>>> = vec![vec![Vec::new()]]; // stage 0 enters with {}
    while let Some(schedule) = stack.pop() {
        let ti = schedule.len() - 1;
        let resident_in = &schedule[ti];
        let root = inst.roots[ti];
        let p_root = fi.peak[root as usize] as usize;

        // (C) feasibility of this carry: outsider forks + P[root] must fit the budget,
        // and the resident forks alone must fit. An illegal carry prunes the branch.
        let fork_outsider_w: usize = resident_in
            .iter()
            .filter(|&&f| is_outsider(ti, f))
            .map(|&f| width(f))
            .sum();
        let fork_w: usize = resident_in.iter().map(|&f| width(f)).sum();
        if fork_outsider_w + p_root > budget || fork_w > budget {
            continue;
        }

        if ti + 1 == t {
            trajectories.push(schedule);
            assert!(
                trajectories.len() <= HARD_CAP,
                "fork-trajectory enumeration exceeded {HARD_CAP}; instance too large for exhaustive M1 planner"
            );
            continue;
        }

        // Keepable forks for the next boundary: forks computed this stage (in the
        // shielded demand) plus carried forks, restricted to those still demanded.
        let demanded = demanded_with_resident(inst, root, resident_in);
        let mut keepable: Vec<u32> = Vec::new();
        for &v in &demanded {
            if fi.is_fork[v as usize] && fork_demanded_after(ti, v) {
                keepable.push(v);
            }
        }
        for &f in resident_in {
            if fork_demanded_after(ti, f) {
                keepable.push(f);
            }
        }
        keepable.sort_unstable();
        keepable.dedup();

        // Enumerate every subset of keepable forks (the keep-decision) that fits the
        // budget; (C) at the next stage prunes any that overflow its root peak.
        let m = keepable.len();
        for mask in 0u32..(1u32 << m) {
            let mut keep: Vec<u32> = Vec::new();
            let mut w = 0usize;
            for (bit, &f) in keepable.iter().enumerate() {
                if mask & (1 << bit) != 0 {
                    keep.push(f);
                    w += width(f);
                }
            }
            if w > budget {
                continue;
            }
            let mut next_schedule = schedule.clone();
            next_schedule.push(keep);
            stack.push(next_schedule);
        }
    }

    let max_frontier = trajectories.len();

    // ── Phase B + C: Belady each complete trajectory, take the min objective. ──
    let best = trajectories
        .iter()
        .map(|sch| simulate_trajectory(inst, &fi, &stage_cones, sch))
        .min()
        .unwrap_or((0, 0));

    let feasible = fi.root_peak.iter().all(|&p| (p as usize) <= budget);
    PlanRun {
        result: PlanResult {
            traffic: best.0,
            instrs: best.1,
            feasible,
            order: inst.roots.clone(),
        },
        max_frontier,
    }
}

/// Phase B: cost one complete fork-residency trajectory. `schedule[ti]` is the set
/// of forks resident entering stage ti. Because the fork schedule is fully fixed,
/// each stage's *shielded* DRAM-leaf demand is exact (a resident fork shields its
/// sub-cone), so Belady's next-use lookahead is correct — this is what the old
/// interleaved DP could not see. Returns `(traffic, instrs)`.
fn simulate_trajectory(
    inst: &OracleInstance,
    fi: &forkset::ForkInfo,
    stage_cones: &[Vec<u32>],
    schedule: &[Vec<u32>],
) -> (u64, u64) {
    let t = inst.roots.len();
    let budget = inst.budget;
    let width = |v: u32| inst.nodes[v as usize].width as usize;
    let is_outsider = |s: usize, v: u32| -> bool { stage_cones[s].binary_search(&v).is_err() };

    // Shielded per-stage DRAM-leaf demand string (sorted) for this trajectory — the
    // crux fix: lookahead uses demand AS SHIELDED by the resident forks, not the
    // static cone. A leaf hidden behind a resident fork at a later stage is correctly
    // NOT demanded there, so Belady can drop it instead of overflowing the budget.
    let demand_dram: Vec<Vec<u32>> = (0..t)
        .map(|ti| {
            let mut leaves: Vec<u32> = demanded_with_resident(inst, inst.roots[ti], &schedule[ti])
                .into_iter()
                .filter(|&v| inst.nodes[v as usize].real_dram)
                .collect();
            leaves.sort_unstable();
            leaves
        })
        .collect();

    let mut resident: Vec<u32> = Vec::new(); // resident leaf set
    let mut traffic = 0u64;
    let mut instrs = 0u64;

    for ti in 0..t {
        let root = inst.roots[ti];
        let resident_in = &schedule[ti];
        let p_root = fi.peak[root as usize] as usize;
        let fork_w: usize = resident_in.iter().map(|&f| width(f)).sum();
        let leaf_budget = budget.saturating_sub(fork_w);

        // instrs: each Add/Mul/Special in the shielded demand is computed once.
        for v in demanded_with_resident(inst, root, resident_in) {
            if matches!(
                inst.nodes[v as usize].kind,
                NodeKind::Add | NodeKind::Mul | NodeKind::Special
            ) {
                instrs += 1;
            }
        }

        // (C) cone-fit: evict carried OUTSIDER leaves (furthest next-demand first)
        // until outsider forks + outsider leaves + P[root] fit the budget. Eviction is
        // traffic-free; the value reloads later if demanded again.
        let fork_outsider_w: usize = resident_in
            .iter()
            .filter(|&&f| is_outsider(ti, f))
            .map(|&f| width(f))
            .sum();
        loop {
            let outsider_leaf_w: usize = resident
                .iter()
                .filter(|&&v| is_outsider(ti, v))
                .map(|&v| width(v))
                .sum();
            if fork_outsider_w + outsider_leaf_w + p_root <= budget {
                break;
            }
            let Some(victim_idx) = resident
                .iter()
                .enumerate()
                .filter(|&(_, &v)| is_outsider(ti, v))
                .max_by(|&(_, &a), &(_, &b)| {
                    let na = next_demand_stage(&demand_dram, ti, a);
                    let nb = next_demand_stage(&demand_dram, ti, b);
                    na.cmp(&nb).then(a.cmp(&b)) // furthest; tie -> largest id
                })
                .map(|(i, _)| i)
            else {
                break; // no outsider leaves left to evict
            };
            resident.swap_remove(victim_idx);
        }

        // Streaming Belady over this stage's shielded DRAM-leaf demand. A demanded leaf
        // streams directly from DRAM into the fold (no cache cell); we charge its read
        // traffic and then keep it resident ONLY if it has future reuse and fits the
        // leaf budget. A leaf with no later demand never occupies cache — caching it
        // would only evict a value that IS reused.
        let mut used: usize = resident.iter().map(|&v| width(v)).sum();
        for &v in &demand_dram[ti] {
            if resident.contains(&v) {
                continue; // hit (resident from a prior stage)
            }
            traffic += width(v) as u64; // miss -> stream-read
            if next_demand_stage(&demand_dram, ti, v) == usize::MAX {
                continue; // no future reuse -> stream only, do not cache
            }
            while used + width(v) > leaf_budget && !resident.is_empty() {
                let victim_idx = (0..resident.len())
                    .max_by(|&a, &b| {
                        let na = next_demand_stage(&demand_dram, ti, resident[a]);
                        let nb = next_demand_stage(&demand_dram, ti, resident[b]);
                        na.cmp(&nb).then(resident[b].cmp(&resident[a])) // furthest; tie -> smallest id
                    })
                    .unwrap();
                let victim = resident.swap_remove(victim_idx);
                used -= width(victim);
            }
            if used + width(v) <= leaf_budget {
                resident.push(v);
                used += width(v);
            }
            // else: v alone exceeds the leaf budget — reloaded on each future demand.
        }

        // Boundary cleanup: drop residents with no future demand.
        let mut i = 0;
        while i < resident.len() {
            if next_demand_stage(&demand_dram, ti, resident[i]) == usize::MAX {
                resident.swap_remove(i);
            } else {
                i += 1;
            }
        }
    }

    (traffic, instrs)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::s3_gap::instance::{NodeKind, OracleInstance, OracleNode};

    pub(super) fn n(
        id: u32,
        kind: NodeKind,
        width: u8,
        real_dram: bool,
        children: Vec<u32>,
    ) -> OracleNode {
        OracleNode {
            id,
            kind,
            width,
            real_dram,
            children,
        }
    }
    pub(super) fn three_read_add() -> OracleInstance {
        OracleInstance {
            budget: 16,
            reloadable_values: vec![],
            roots: vec![3],
            nodes: vec![
                n(0, NodeKind::Read, 4, true, vec![]),
                n(1, NodeKind::Read, 4, true, vec![]),
                n(2, NodeKind::Read, 1, true, vec![]),
                n(3, NodeKind::Add, 4, false, vec![0, 1, 2]),
            ],
        }
    }

    #[test]
    fn naive_counts_each_cone_node_once_per_stage() {
        let inst = three_read_add();
        let r = plan_naive(&inst);
        assert_eq!(r.traffic, 4 + 4 + 1); // three distinct DRAM leaves, one stage
        assert_eq!(r.instrs, 1); // the single Add
    }

    #[test]
    fn naive_recomputes_shared_leaf_once_per_stage() {
        // base Read 0 shared by two root Adds -> re-read once per stage (no caching).
        let inst = OracleInstance {
            budget: 16,
            reloadable_values: vec![],
            roots: vec![1, 2],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Add, 1, false, vec![0]),
                n(2, NodeKind::Add, 1, false, vec![0]),
            ],
        };
        let r = plan_naive(&inst);
        assert_eq!(r.traffic, 1 + 1); // Read 0 counted once per stage, two stages
        assert_eq!(r.instrs, 2);
    }

    #[test]
    fn belady_caches_shared_leaf_once() {
        let inst = OracleInstance {
            budget: 16,
            reloadable_values: vec![],
            roots: vec![1, 2],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Add, 1, false, vec![0]),
                n(2, NodeKind::Add, 1, false, vec![0]),
            ],
        };
        let r = plan_belady_leaves(&inst);
        assert_eq!(r.traffic, 1); // Read 0 loaded once, resident across both stages
        assert_eq!(r.instrs, 2);
    }

    #[test]
    fn belady_evicts_furthest_next_stage_victim() {
        // budget 2 (two width-1 leaves). stages: s0 demands {a,b}, s1 demands {c}, s2 demands {a}.
        // At s1 admitting c must evict one of {a,b}: a's next stage is s2, b's is never ->
        // Belady evicts b (furthest). s2 then finds a resident -> no reload. traffic = a+b+c = 3.
        let inst = OracleInstance {
            budget: 2,
            reloadable_values: vec![],
            roots: vec![3, 4, 5],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),     // a
                n(1, NodeKind::Read, 1, true, vec![]),     // b
                n(2, NodeKind::Read, 1, true, vec![]),     // c
                n(3, NodeKind::Add, 1, false, vec![0, 1]), // s0: {a,b}
                n(4, NodeKind::Add, 1, false, vec![2]),    // s1: {c}
                n(5, NodeKind::Add, 1, false, vec![0]),    // s2: {a}
            ],
        };
        let r = plan_belady_leaves(&inst);
        assert_eq!(r.traffic, 3); // had it evicted a instead, s2 would reload a -> 4
        assert_eq!(r.instrs, 3); // three Adds
    }

    #[test]
    #[ignore = "requires python3 + ortools"]
    fn belady_matches_oracle_e_on_no_fork_instance() {
        use crate::s3_gap::driver::{oracle_available, run_oracle, Mode};
        if !oracle_available() {
            eprintln!("ortools unavailable; skipping");
            return;
        }
        let inst = three_read_add(); // single root, no fork, (C) trivial
        let plan = plan_belady_leaves(&inst);
        let e = run_oracle(&inst, Mode::E, 0.0, 30).unwrap();
        assert_eq!(e.status, "optimal");
        assert_eq!((plan.traffic, plan.instrs), (e.traffic, e.instrs));
    }

    #[test]
    fn fork_dp_caches_shared_product_to_save_instrs() {
        // shared product Mul{0,1}=2 (base, width 1) consumed by Add{2,0}=3 and Add{2,1}=4.
        // Recompute-2: leaves 0,1 resident across stages -> traffic 2; instrs = Mul+Add(s0)=2 + Mul+Add(s1)=2 = 4.
        // Cache-2: stage0 computes 0,1,Mul2,Add3 (traffic 2, instrs 2), keep node 2 resident;
        //          stage1 sees node 2 resident (free, not descended) + Add4 (instr) -> traffic 0, instrs 1.
        // Cache total = (traffic 2, instrs 3) < recompute (2,4). DP must pick caching.
        let inst = OracleInstance {
            budget: 16,
            reloadable_values: vec![],
            roots: vec![3, 4],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Mul, 1, false, vec![0, 1]),
                n(3, NodeKind::Add, 1, false, vec![2, 0]),
                n(4, NodeKind::Add, 1, false, vec![2, 1]),
            ],
        };
        let run = plan_fixed_order(&inst);
        assert_eq!(run.result.objective(), (2, 3));
        assert!(run.max_frontier >= 1);
    }

    #[test]
    fn fork_dp_caches_shared_special_root_to_save_instrs() {
        // Degenerate corpus case (add_sub L0, extracted): roots [0,1,3] where the
        // Special terminals 0,1 are ALSO children of root 3 = Add{2,2,0,1}. A Special
        // costs 1 instr to recompute (it is resolution-pruned but still produced), so
        // it is a cacheable fork exactly like Add/Mul. Keeping 0,1 resident after
        // their own root stages shields them inside root 3's cone → 3 instrs; the old
        // Add|Mul-only fork classification could not keep a Special, recomputing both
        // → 5 instrs. traffic 0 (Special/Literal carry no DRAM). The oracle (E) reports
        // (0,3); the planner must match.
        let inst = OracleInstance {
            budget: 16,
            reloadable_values: vec![],
            roots: vec![0, 1, 3],
            nodes: vec![
                n(0, NodeKind::Special, 1, false, vec![]),
                n(1, NodeKind::Special, 1, false, vec![]),
                n(2, NodeKind::Literal, 4, false, vec![]),
                n(3, NodeKind::Add, 4, false, vec![2, 2, 0, 1]),
            ],
        };
        let run = plan_fixed_order(&inst);
        assert_eq!(run.result.objective(), (0, 3));
    }

    // Complement of fork_dp_cone_fit_c_isolated_uniform: when the intervening cone
    // STREAMS, neither (B) nor (C) forces eviction, so the carried leaf is kept.
    #[test]
    fn fork_dp_carries_leaf_when_intervening_cone_streams() {
        // budget 4. ext Read X(0,w4) used by root A=Add{0}=2 (s0) and root C=Add{0}=4 (s2).
        // Intervening root B=Add{1}=3 (s1) over ext Read Y(1,w4): under the streaming model
        // Y streams directly from DRAM (no cache cell) and P[B]=0, so carrying X costs only
        // X's own w4: X(4) + P[B](0) = 4 <= budget 4. X stays resident through B and is reused
        // at C. traffic = X@s0(4) + Y@s1(4) = 8 ; instrs = 3 -> (8,3). (Under the old model
        // that put Y in cache, X+Y=8>4 forced a reload and reported (12,3).)
        let inst = OracleInstance {
            budget: 4,
            reloadable_values: vec![],
            roots: vec![2, 3, 4],
            nodes: vec![
                n(0, NodeKind::Read, 4, true, vec![]),  // X
                n(1, NodeKind::Read, 4, true, vec![]),  // Y
                n(2, NodeKind::Add, 4, false, vec![0]), // A (s0)
                n(3, NodeKind::Add, 4, false, vec![1]), // B (s1), P=4
                n(4, NodeKind::Add, 4, false, vec![0]), // C (s2), reuses X
            ],
        };
        let run = plan_fixed_order(&inst);
        assert_eq!(run.result.objective(), (8, 3));
    }

    #[test]
    fn fork_dp_cone_fit_c_isolated_uniform() {
        // Isolates (C) under the single-accumulator STREAMING model: budget 1, all base
        // width 1. X(0) is read at A=Add{0} (s0) and reused at C=Add{0} (s2). The
        // intervening B (s1) is a fold-of-folds B=Add{g,h}, g=Add{p}, h=Add{q}: g and h
        // each need their own accumulator pass, so computing B spills its partial once
        // -> P[B]=1. A fold over plain reads would stream (peak 0) and NOT bind (C);
        // the spill is what makes (C) bite.
        // (C) at s1: X outsider(1) + P[B](1) = 2 > 1 -> X evicted before B, re-read at C.
        //   WITH (C): traffic = X@s0(1) + p,q@s1(2) + X@s2(1) = 4 ; instrs = 5 -> (4,5).
        //   WITHOUT (C) (the discriminator): X stays resident -> (3,5).
        let inst = OracleInstance {
            budget: 1,
            reloadable_values: vec![],
            roots: vec![3, 6, 7],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),     // X
                n(1, NodeKind::Read, 1, true, vec![]),     // p
                n(2, NodeKind::Read, 1, true, vec![]),     // q
                n(3, NodeKind::Add, 1, false, vec![0]),    // A (s0), reads X
                n(4, NodeKind::Add, 1, false, vec![1]),    // g
                n(5, NodeKind::Add, 1, false, vec![2]),    // h
                n(6, NodeKind::Add, 1, false, vec![4, 5]), // B (s1), fold-of-folds, P[B]=1
                n(7, NodeKind::Add, 1, false, vec![0]),    // C (s2), reuses X
            ],
        };
        let run = plan_fixed_order(&inst);
        assert_eq!(run.result.objective(), (4, 5));
    }

    #[test]
    fn fork_dp_never_worse_than_belady_baseline() {
        let inst = OracleInstance {
            budget: 16,
            reloadable_values: vec![],
            roots: vec![3, 4],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Mul, 1, false, vec![0, 1]),
                n(3, NodeKind::Add, 1, false, vec![2, 0]),
                n(4, NodeKind::Add, 1, false, vec![2, 1]),
            ],
        };
        let baseline = plan_belady_leaves(&inst);
        let run = plan_fixed_order(&inst);
        assert!(run.result.objective() <= baseline.objective());
    }

    #[test]
    #[ignore = "requires python3 + ortools"]
    fn fork_dp_matches_oracle_e_uniform_width() {
        use crate::s3_gap::driver::{oracle_available, run_oracle, Mode};
        if !oracle_available() {
            eprintln!("ortools unavailable; skipping");
            return;
        }
        let inst = OracleInstance {
            budget: 16,
            reloadable_values: vec![],
            roots: vec![3, 4],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Mul, 1, false, vec![0, 1]),
                n(3, NodeKind::Add, 1, false, vec![2, 0]),
                n(4, NodeKind::Add, 1, false, vec![2, 1]),
            ],
        };
        let run = plan_fixed_order(&inst);
        let e = run_oracle(&inst, Mode::E, 0.0, 30).unwrap();
        assert_eq!(e.status, "optimal");
        assert_eq!(run.result.objective(), (e.traffic, e.instrs)); // uniform width -> EXACT
    }

    #[test]
    #[ignore = "requires python3 + ortools"]
    fn fork_dp_matches_oracle_e_carries_when_cone_streams() {
        use crate::s3_gap::driver::{oracle_available, run_oracle, Mode};
        if !oracle_available() {
            eprintln!("ortools unavailable; skipping");
            return;
        }
        // Oracle-backed twin of fork_dp_carries_leaf_when_intervening_cone_streams:
        // budget 4, X(0) reused at A (s0) and C (s2); intervening B=Add{Y} STREAMS
        // (P[B]=0), so carrying X (4 <= 4) avoids a reload. Under the corrected
        // streaming oracle both sides report (8,3) — NOT the old model's (12,3),
        // which charged Y into cache and forced the reload.
        let inst = OracleInstance {
            budget: 4,
            reloadable_values: vec![],
            roots: vec![2, 3, 4],
            nodes: vec![
                n(0, NodeKind::Read, 4, true, vec![]),
                n(1, NodeKind::Read, 4, true, vec![]),
                n(2, NodeKind::Add, 4, false, vec![0]),
                n(3, NodeKind::Add, 4, false, vec![1]),
                n(4, NodeKind::Add, 4, false, vec![0]),
            ],
        };
        let run = plan_fixed_order(&inst);
        let e = run_oracle(&inst, Mode::E, 0.0, 30).unwrap();
        assert_eq!(e.status, "optimal");
        assert_eq!(run.result.objective(), (8, 3));
        assert_eq!(run.result.objective(), (e.traffic, e.instrs));
    }

    #[test]
    #[ignore = "requires python3 + ortools"]
    fn fork_dp_matches_oracle_e_cone_fit_c_binds() {
        use crate::s3_gap::driver::{oracle_available, run_oracle, Mode};
        if !oracle_available() {
            eprintln!("ortools unavailable; skipping");
            return;
        }
        // Oracle-backed twin of fork_dp_cone_fit_c_isolated_uniform: the case where
        // (C) GENUINELY binds under the streaming model. budget 1, all base w1.
        // X(0) read at A=Add{0} (s0) and reused at C=Add{0} (s2). The intervening
        // B (s1) is a fold-of-folds Add{Add{p}, Add{q}}, which spills its partial
        // once → P[B]=1. (C) at s1: X outsider(1) + P[B](1) = 2 > 1 forbids carrying
        // X, forcing a reload at C. Both sides must report (4,5) (a flat fold over
        // reads would stream at peak 0 and NOT bind — the spill is what makes (C) bite).
        let inst = OracleInstance {
            budget: 1,
            reloadable_values: vec![],
            roots: vec![3, 6, 7],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),     // X
                n(1, NodeKind::Read, 1, true, vec![]),     // p
                n(2, NodeKind::Read, 1, true, vec![]),     // q
                n(3, NodeKind::Add, 1, false, vec![0]),    // A (s0), reads X
                n(4, NodeKind::Add, 1, false, vec![1]),    // g
                n(5, NodeKind::Add, 1, false, vec![2]),    // h
                n(6, NodeKind::Add, 1, false, vec![4, 5]), // B (s1), fold-of-folds, P[B]=1
                n(7, NodeKind::Add, 1, false, vec![0]),    // C (s2), reuses X
            ],
        };
        let run = plan_fixed_order(&inst);
        let e = run_oracle(&inst, Mode::E, 0.0, 30).unwrap();
        assert_eq!(e.status, "optimal");
        assert_eq!(run.result.objective(), (4, 5));
        assert_eq!(run.result.objective(), (e.traffic, e.instrs));
    }

    // Regression: Belady must run AFTER fork enumeration, not interleaved with it
    // (systematic-debugging repro, randomized seed 12). Two forks {2,3}, budget 3, all
    // width 1. The optimum caches BOTH forks and drops Reads {0,1} after stage 1 —
    // betting that at stage 2 the resident forks shield {0,1}. The old interleaved DP
    // chose leaf residency stage-by-stage with a shielding-blind (static-cone) Belady
    // lookahead, so it KEPT {0,1} after stage 1 (thought stage 2 still needed them),
    // overflowed the budget, and could not cache both forks → one extra recompute.
    // Uniform width ⇒ the planner must be EXACT; the oracle-E optimum (confirmed by
    // run_oracle, status optimal) is (traffic=2, instrs=5); the buggy DP returned (2,6).
    fn repro_seed12_instance() -> OracleInstance {
        OracleInstance {
            budget: 3,
            reloadable_values: vec![],
            roots: vec![4, 5, 6],
            nodes: vec![
                n(0, NodeKind::Read, 1, true, vec![]),
                n(1, NodeKind::Read, 1, true, vec![]),
                n(2, NodeKind::Add, 1, false, vec![1, 0]),
                n(3, NodeKind::Mul, 1, false, vec![0, 1]),
                n(4, NodeKind::Add, 1, false, vec![0, 2]),
                n(5, NodeKind::Mul, 1, false, vec![3, 0]),
                n(6, NodeKind::Mul, 1, false, vec![2, 3]),
            ],
        }
    }

    #[test]
    fn fork_dp_leaf_residency_keeps_optimum() {
        let run = plan_fixed_order(&repro_seed12_instance());
        assert_eq!(run.result.objective(), (2, 5));
    }

    #[test]
    #[ignore = "requires python3 + ortools"]
    fn fork_dp_leaf_residency_matches_oracle() {
        use crate::s3_gap::driver::{oracle_available, run_oracle, Mode};
        if !oracle_available() {
            eprintln!("ortools unavailable; skipping");
            return;
        }
        let inst = repro_seed12_instance();
        let run = plan_fixed_order(&inst);
        let e = run_oracle(&inst, Mode::E, 0.0, 30).unwrap();
        assert_eq!(e.status, "optimal");
        assert_eq!(run.result.objective(), (e.traffic, e.instrs));
    }
}
