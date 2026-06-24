//! Inner planner: stage-indexed simulation + Belady stage-boundary leaf caching
//! (Task 3) + fork residency DP (Task 4). Objective matches the oracle: (traffic, instrs),
//! counted ONCE PER NODE PER STAGE (deduped cone set), residency at stage boundaries.

use crate::s3_gap::instance::{NodeKind, OracleInstance};
use super::forkset;

pub struct PlanResult { pub traffic: u64, pub instrs: u64, pub feasible: bool, pub order: Vec<u32> }
impl PlanResult { pub fn objective(&self) -> (u64, u64) { (self.traffic, self.instrs) } }

pub fn plan_naive(inst: &OracleInstance) -> PlanResult {
    let (mut traffic, mut instrs) = (0u64, 0u64);
    for &root in &inst.roots {
        for v in forkset::cone(inst, root) {            // deduped: each cone node once per stage
            let node = &inst.nodes[v as usize];
            if node.real_dram { traffic += node.width as u64; }
            if matches!(node.kind, NodeKind::Add | NodeKind::Mul | NodeKind::Special) { instrs += 1; }
        }
    }
    PlanResult { traffic, instrs, feasible: true, order: inst.roots.clone() }
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
            if node.real_dram { leaves.push(v); }
            if matches!(node.kind, NodeKind::Add | NodeKind::Mul | NodeKind::Special) { instrs += 1; }
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
            if resident.contains(&v) { continue; }      // hit (resident from a prior stage)
            traffic += width(v) as u64;                  // miss -> load
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
            if used + width(v) <= budget { resident.push(v); used += width(v); }
            // else: v alone exceeds budget — reloaded on each future demand.
        }
        // boundary cleanup: drop residents with no future demand.
        let mut i = 0;
        while i < resident.len() {
            if next_demand_stage(&stage_leaves, ti, resident[i]) == usize::MAX {
                let v = resident.swap_remove(i); used -= width(v);
            } else { i += 1; }
        }
    }

    let feasible = fi.root_peak.iter().all(|&p| (p as usize) <= budget); // (B)-only baseline
    PlanResult { traffic, instrs, feasible, order: inst.roots.clone() }
}

/// Smallest stage index strictly greater than `ti` whose cone demands leaf `v`
/// (usize::MAX if none). Stage granularity matches the oracle's per-stage compute.
fn next_demand_stage(stage_leaves: &[Vec<u32>], ti: usize, v: u32) -> usize {
    for s in (ti + 1)..stage_leaves.len() {
        if stage_leaves[s].contains(&v) { return s; }
    }
    usize::MAX
}

// ── Task 4a: fork residency DP (cache vs recompute, no binding (C)) ───────────

pub struct PlanRun {
    pub result: PlanResult,
    pub max_frontier: usize,
}

/// DP value for a resident-fork state: best lex `(traffic, instrs)` reached, plus
/// the resident leaf set carried alongside the forks (a deterministic function of
/// the fork-residency path under stage-boundary Belady).
#[derive(Clone)]
struct StateVal {
    traffic: u64,
    instrs: u64,
    leaves: Vec<u32>, // sorted resident leaf node ids
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

/// Fork-residency DP over a fixed root order. State = sorted set of resident fork
/// node ids at a stage boundary; value = min-lex `(traffic, instrs)` to reach it.
///
/// Task 4a: no binding cone-fit `(C)` — instances have `peak <= budget` so `(C)`
/// never binds. Belady stage-boundary leaf caching is simulated per DP path, with
/// the leaf cache costed against the budget left by the resident forks.
pub fn plan_fixed_order(inst: &OracleInstance) -> PlanRun {
    use std::collections::BTreeMap;

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

    // Per-stage full cone (descending through everything), sorted, for future-demand
    // lookahead on both forks and leaves, and for the cone-fit (C) outsider test.
    let stage_cones: Vec<Vec<u32>> =
        inst.roots.iter().map(|&r| forkset::cone(inst, r)).collect();
    // Future-demand stage per fork: smallest stage index > ti whose cone references
    // the fork. Used to drop forks with no remaining consumer at a boundary.
    let fork_demanded_after = |ti: usize, f: u32| -> bool {
        ((ti + 1)..t).any(|s| stage_cones[s].binary_search(&f).is_ok())
    };
    // (C) outsider: a carried value v is an outsider at stage `s` iff it is NOT in
    // cone(roots[s]). Carried leaves count exactly like carried forks.
    let is_outsider = |s: usize, v: u32| -> bool { stage_cones[s].binary_search(&v).is_err() };
    // Per-stage DRAM-leaf demand string (sorted), for Belady next-demand lookahead
    // when choosing which (C)-outsider leaf to evict.
    let stage_cones_leaves: Vec<Vec<u32>> = stage_cones
        .iter()
        .map(|c| {
            c.iter()
                .copied()
                .filter(|&v| inst.nodes[v as usize].real_dram)
                .collect::<Vec<u32>>()
        })
        .collect();

    // DP states: resident fork set (sorted, canonical) -> StateVal.
    let mut states: BTreeMap<Vec<u32>, StateVal> = BTreeMap::new();
    states.insert(Vec::new(), StateVal { traffic: 0, instrs: 0, leaves: Vec::new() });
    let mut max_frontier = 0usize;

    for ti in 0..t {
        let root = inst.roots[ti];
        let mut next: BTreeMap<Vec<u32>, StateVal> = BTreeMap::new();

        let p_root = fi.peak[root as usize] as usize;

        for (s_prev, val) in &states {
            // (C) cone fit for the root materialized this stage: carried outsiders
            // (forks AND leaves not in cone(root)) plus P[root] must fit the budget.
            // A carried fork that violates (C) makes this state illegal at this stage
            // (it should have been evicted at the prior boundary) — skip it. Carried
            // leaf outsiders are evicted here (reloaded later if demanded again), so
            // they are dropped from the carried leaf set before the Belady step.
            let fork_outsider_w: usize = s_prev
                .iter()
                .filter(|&&f| is_outsider(ti, f))
                .map(|&f| width(f))
                .sum();
            if fork_outsider_w + p_root > budget {
                continue; // illegal carry: forks alone overflow (C)
            }
            // Evict carried leaf outsiders that don't fit (C), smallest budget impact
            // first is unnecessary: any outsider eviction is traffic-free here and the
            // value reloads later. Drop outsider leaves until (C) holds.
            let mut carried_leaves: Vec<u32> = val.leaves.clone();
            {
                let mut outsider_leaf_w: usize = carried_leaves
                    .iter()
                    .filter(|&&v| is_outsider(ti, v))
                    .map(|&v| width(v))
                    .sum();
                // Outsider leaves contribute to (C) alongside outsider forks + P[root].
                // Evict outsider leaves (furthest-next-demand first, tie -> largest id)
                // until fork_outsider_w + outsider_leaf_w + p_root <= budget.
                while fork_outsider_w + outsider_leaf_w + p_root > budget {
                    let victim_idx = carried_leaves
                        .iter()
                        .enumerate()
                        .filter(|&(_, &v)| is_outsider(ti, v))
                        .max_by(|&(_, &a), &(_, &b)| {
                            let na = next_demand_stage(&stage_cones_leaves, ti, a);
                            let nb = next_demand_stage(&stage_cones_leaves, ti, b);
                            na.cmp(&nb).then(a.cmp(&b)) // furthest; tie -> largest id
                        })
                        .map(|(i, _)| i)
                        .expect("(C) overflow with no outsider leaves to evict");
                    let v = carried_leaves.remove(victim_idx);
                    outsider_leaf_w -= width(v);
                }
            }

            // Resident forks (from the carried state) are free this stage.
            let demanded = demanded_with_resident(inst, root, s_prev);

            let mut stage_instrs = 0u64;
            let mut stage_leaves: Vec<u32> = Vec::new(); // distinct demanded DRAM leaves (sorted)
            let mut computed_forks: Vec<u32> = Vec::new();
            for &v in &demanded {
                let node = &inst.nodes[v as usize];
                if node.real_dram {
                    stage_leaves.push(v);
                }
                if matches!(node.kind, NodeKind::Add | NodeKind::Mul | NodeKind::Special) {
                    stage_instrs += 1;
                }
                if fi.is_fork[v as usize] {
                    computed_forks.push(v);
                }
            }

            // Belady leaf step for this stage, against the budget left by resident
            // forks; replay from the carried leaf residency.
            let fork_budget: usize = s_prev.iter().map(|&f| width(f)).sum();
            let leaf_budget = budget.saturating_sub(fork_budget);
            let (stage_traffic, leaves_after) =
                belady_leaf_step(inst, ti, &stage_leaves, &carried_leaves, leaf_budget);

            // Candidate forks to keep resident after this stage: carried forks plus
            // forks computed this stage, restricted to those with future demand.
            let mut keepable: Vec<u32> = Vec::new();
            for &f in s_prev.iter().chain(computed_forks.iter()) {
                if fork_demanded_after(ti, f) {
                    keepable.push(f);
                }
            }
            keepable.sort_unstable();
            keepable.dedup();

            let new_traffic = val.traffic + stage_traffic;
            let new_instrs = val.instrs + stage_instrs;
            let leaf_after_width: usize = leaves_after.iter().map(|&v| width(v)).sum();

            // Enumerate subsets of keepable forks that fit the boundary budget (B)
            // alongside the surviving leaves.
            let m = keepable.len();
            for mask in 0u32..(1u32 << m) {
                let mut s_next: Vec<u32> = Vec::new();
                let mut fork_w = 0usize;
                for (bit, &f) in keepable.iter().enumerate() {
                    if mask & (1 << bit) != 0 {
                        s_next.push(f);
                        fork_w += width(f);
                    }
                }
                // (B) boundary: resident forks + surviving leaves fit the budget.
                if fork_w + leaf_after_width > budget {
                    continue;
                }
                let cand = StateVal {
                    traffic: new_traffic,
                    instrs: new_instrs,
                    leaves: leaves_after.clone(),
                };
                match next.get(&s_next) {
                    Some(existing)
                        if (existing.traffic, existing.instrs)
                            <= (cand.traffic, cand.instrs) => {}
                    _ => {
                        next.insert(s_next, cand);
                    }
                }
            }
        }

        let pruned = prune_dominated(next);
        max_frontier = max_frontier.max(pruned.len());
        states = pruned;
    }

    // Best terminal state (min lex value). Determinism: BTreeMap iteration order.
    let best = states
        .values()
        .map(|v| (v.traffic, v.instrs))
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

/// One stage of stage-boundary Belady leaf caching, against `leaf_budget` cells.
/// `prior_leaves` is the carried resident leaf set (sorted); returns
/// `(stage_traffic, leaves_after)` where `leaves_after` is the resident leaf set
/// after this stage's boundary cleanup (sorted). Mirrors `plan_belady_leaves`'s
/// per-stage step but uses only the budget left by resident forks.
fn belady_leaf_step(
    inst: &OracleInstance,
    ti: usize,
    stage_leaves: &[u32],
    prior_leaves: &[u32],
    leaf_budget: usize,
) -> (u64, Vec<u32>) {
    let width = |v: u32| inst.nodes[v as usize].width as usize;
    let t = inst.roots.len();
    // Per-stage DRAM-leaf demand string for next-demand lookahead (Belady).
    let stage_demand: Vec<Vec<u32>> = (0..t)
        .map(|s| {
            let mut leaves: Vec<u32> = forkset::cone(inst, inst.roots[s])
                .into_iter()
                .filter(|&v| inst.nodes[v as usize].real_dram)
                .collect();
            leaves.sort_unstable();
            leaves
        })
        .collect();

    let mut resident: Vec<u32> = prior_leaves.to_vec();
    let mut used: usize = resident.iter().map(|&v| width(v)).sum();
    let mut traffic = 0u64;

    for &v in stage_leaves {
        if resident.contains(&v) {
            continue; // hit
        }
        traffic += width(v) as u64; // miss -> load
        while used + width(v) > leaf_budget && !resident.is_empty() {
            let victim_idx = (0..resident.len())
                .max_by(|&a, &b| {
                    let na = next_demand_stage(&stage_demand, ti, resident[a]);
                    let nb = next_demand_stage(&stage_demand, ti, resident[b]);
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
        if next_demand_stage(&stage_demand, ti, resident[i]) == usize::MAX {
            resident.swap_remove(i);
        } else {
            i += 1;
        }
    }
    resident.sort_unstable();
    (traffic, resident)
}

/// Drop dominated states: if `S1 ⊇ S2` and `value(S1) <= value(S2)` lexically,
/// remove `S2` — eviction is traffic-free, so the larger resident set can always
/// reach the smaller one at no cost. Deterministic over the sorted BTreeMap.
fn prune_dominated(
    states: std::collections::BTreeMap<Vec<u32>, StateVal>,
) -> std::collections::BTreeMap<Vec<u32>, StateVal> {
    let entries: Vec<(Vec<u32>, StateVal)> = states.into_iter().collect();
    let mut kept: std::collections::BTreeMap<Vec<u32>, StateVal> =
        std::collections::BTreeMap::new();
    for (i, (si, vi)) in entries.iter().enumerate() {
        let vi_obj = (vi.traffic, vi.instrs);
        let dominated = entries.iter().enumerate().any(|(j, (sj, vj))| {
            if i == j {
                return false;
            }
            // sj ⊇ si and value(sj) <= value(si): sj dominates si.
            let superset = si.iter().all(|x| sj.contains(x));
            let strictly_bigger_or_better =
                (sj.len() > si.len()) || ((vj.traffic, vj.instrs) < vi_obj);
            superset && (vj.traffic, vj.instrs) <= vi_obj && strictly_bigger_or_better
        });
        if !dominated {
            kept.insert(si.clone(), vi.clone());
        }
    }
    kept
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::s3_gap::instance::{NodeKind, OracleInstance, OracleNode};

    pub(super) fn n(id: u32, kind: NodeKind, width: u8, real_dram: bool, children: Vec<u32>) -> OracleNode {
        OracleNode { id, kind, width, real_dram, children }
    }
    pub(super) fn three_read_add() -> OracleInstance {
        OracleInstance { budget: 16, roots: vec![3], nodes: vec![
            n(0, NodeKind::Read, 4, true, vec![]),
            n(1, NodeKind::Read, 4, true, vec![]),
            n(2, NodeKind::Read, 1, true, vec![]),
            n(3, NodeKind::Add, 4, false, vec![0, 1, 2]),
        ]}
    }

    #[test]
    fn naive_counts_each_cone_node_once_per_stage() {
        let inst = three_read_add();
        let r = plan_naive(&inst);
        assert_eq!(r.traffic, 4 + 4 + 1); // three distinct DRAM leaves, one stage
        assert_eq!(r.instrs, 1);          // the single Add
    }

    #[test]
    fn naive_recomputes_shared_leaf_once_per_stage() {
        // base Read 0 shared by two root Adds -> re-read once per stage (no caching).
        let inst = OracleInstance { budget: 16, roots: vec![1, 2], nodes: vec![
            n(0, NodeKind::Read, 1, true, vec![]),
            n(1, NodeKind::Add, 1, false, vec![0]),
            n(2, NodeKind::Add, 1, false, vec![0]),
        ]};
        let r = plan_naive(&inst);
        assert_eq!(r.traffic, 1 + 1); // Read 0 counted once per stage, two stages
        assert_eq!(r.instrs, 2);
    }

    #[test]
    fn belady_caches_shared_leaf_once() {
        let inst = OracleInstance { budget: 16, roots: vec![1, 2], nodes: vec![
            n(0, NodeKind::Read, 1, true, vec![]),
            n(1, NodeKind::Add, 1, false, vec![0]),
            n(2, NodeKind::Add, 1, false, vec![0]),
        ]};
        let r = plan_belady_leaves(&inst);
        assert_eq!(r.traffic, 1); // Read 0 loaded once, resident across both stages
        assert_eq!(r.instrs, 2);
    }

    #[test]
    fn belady_evicts_furthest_next_stage_victim() {
        // budget 2 (two width-1 leaves). stages: s0 demands {a,b}, s1 demands {c}, s2 demands {a}.
        // At s1 admitting c must evict one of {a,b}: a's next stage is s2, b's is never ->
        // Belady evicts b (furthest). s2 then finds a resident -> no reload. traffic = a+b+c = 3.
        let inst = OracleInstance { budget: 2, roots: vec![3, 4, 5], nodes: vec![
            n(0, NodeKind::Read, 1, true, vec![]),   // a
            n(1, NodeKind::Read, 1, true, vec![]),   // b
            n(2, NodeKind::Read, 1, true, vec![]),   // c
            n(3, NodeKind::Add, 1, false, vec![0, 1]), // s0: {a,b}
            n(4, NodeKind::Add, 1, false, vec![2]),    // s1: {c}
            n(5, NodeKind::Add, 1, false, vec![0]),    // s2: {a}
        ]};
        let r = plan_belady_leaves(&inst);
        assert_eq!(r.traffic, 3); // had it evicted a instead, s2 would reload a -> 4
        assert_eq!(r.instrs, 3);  // three Adds
    }

    #[test]
    #[ignore = "requires python3 + ortools"]
    fn belady_matches_oracle_e_on_no_fork_instance() {
        use crate::s3_gap::driver::{oracle_available, run_oracle, Mode};
        if !oracle_available() { eprintln!("ortools unavailable; skipping"); return; }
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
        let inst = OracleInstance { budget: 16, roots: vec![3, 4], nodes: vec![
            n(0, NodeKind::Read, 1, true, vec![]),
            n(1, NodeKind::Read, 1, true, vec![]),
            n(2, NodeKind::Mul, 1, false, vec![0, 1]),
            n(3, NodeKind::Add, 1, false, vec![2, 0]),
            n(4, NodeKind::Add, 1, false, vec![2, 1]),
        ]};
        let run = plan_fixed_order(&inst);
        assert_eq!(run.result.objective(), (2, 3));
        assert!(run.max_frontier >= 1);
    }

    // NOTE: this test is (B)-driven — the (B) boundary cap alone forces eviction of X
    // (X w4 + Y w4 = 8 > budget 4). See fork_dp_cone_fit_c_isolated_uniform for the (C)-isolating gate.
    #[test]
    fn fork_dp_respects_cone_fit_c_on_carried_leaf() {
        // budget 4. ext Read X(0,w4) used by root A=Add{0}=2 (s0) and root C=Add{0}=4 (s2).
        // Intervening root B=Add{1}=3 (s1) over ext Read Y(1,w4): P[B]=4=budget.
        // (C) at s1: X is an outsider (w4) not in cone(B); 4 + P[B]=4 = 8 > 4 -> X CANNOT be carried.
        // So X is evicted before B and reloaded at C: X traffic = 4 (s0) + 4 (s2). Y traffic = 4 (s1).
        // total traffic = 12; instrs = 3 (three Adds). A DP ignoring (C) would carry X and report (8,3).
        let inst = OracleInstance { budget: 4, roots: vec![2, 3, 4], nodes: vec![
            n(0, NodeKind::Read, 4, true, vec![]),    // X
            n(1, NodeKind::Read, 4, true, vec![]),    // Y
            n(2, NodeKind::Add, 4, false, vec![0]),   // A (s0)
            n(3, NodeKind::Add, 4, false, vec![1]),   // B (s1), P=4
            n(4, NodeKind::Add, 4, false, vec![0]),   // C (s2), reuses X
        ]};
        let run = plan_fixed_order(&inst);
        assert_eq!(run.result.objective(), (12, 3));
    }

    #[test]
    fn fork_dp_cone_fit_c_isolated_uniform() {
        // Isolates (C): budget 2, all base width 1. X(0) used by A=Add{0}=2 (s0) and
        // C=Add{0}=4 (s2). Intervening B=Add{1,1}=3 (s1): duplicate child edge to Y(1)
        // gives cone(B)={1,3} (Y demanded once) but P[B]=max(peak(1)=1, width 1 + 1)=2=budget.
        // (B) at s1 PERMITS carrying X: X(1)+Y(1)=2 <= 2. But (C) forbids: X outsider(1)
        // + P[B](2) = 3 > 2 -> X must be evicted before B and reloaded at C.
        //   WITH (C): traffic = X@s0(1) + Y@s1(1) + X@s2(1) = 3 ; instrs = 3 -> (3,3).
        //   WITHOUT (C) (the discriminator): X stays resident -> (2,3).
        let inst = OracleInstance { budget: 2, roots: vec![2, 3, 4], nodes: vec![
            n(0, NodeKind::Read, 1, true, vec![]),     // X
            n(1, NodeKind::Read, 1, true, vec![]),     // Y
            n(2, NodeKind::Add, 1, false, vec![0]),    // A (s0)
            n(3, NodeKind::Add, 1, false, vec![1, 1]), // B (s1): P[B]=2=budget, 1-leaf footprint
            n(4, NodeKind::Add, 1, false, vec![0]),    // C (s2), reuses X
        ]};
        let run = plan_fixed_order(&inst);
        assert_eq!(run.result.objective(), (3, 3));
    }

    #[test]
    fn fork_dp_never_worse_than_belady_baseline() {
        let inst = OracleInstance { budget: 16, roots: vec![3, 4], nodes: vec![
            n(0, NodeKind::Read, 1, true, vec![]),
            n(1, NodeKind::Read, 1, true, vec![]),
            n(2, NodeKind::Mul, 1, false, vec![0, 1]),
            n(3, NodeKind::Add, 1, false, vec![2, 0]),
            n(4, NodeKind::Add, 1, false, vec![2, 1]),
        ]};
        let baseline = plan_belady_leaves(&inst);
        let run = plan_fixed_order(&inst);
        assert!(run.result.objective() <= baseline.objective());
    }

    #[test]
    #[ignore = "requires python3 + ortools"]
    fn fork_dp_matches_oracle_e_uniform_width() {
        use crate::s3_gap::driver::{oracle_available, run_oracle, Mode};
        if !oracle_available() { eprintln!("ortools unavailable; skipping"); return; }
        let inst = OracleInstance { budget: 16, roots: vec![3, 4], nodes: vec![
            n(0, NodeKind::Read, 1, true, vec![]),
            n(1, NodeKind::Read, 1, true, vec![]),
            n(2, NodeKind::Mul, 1, false, vec![0, 1]),
            n(3, NodeKind::Add, 1, false, vec![2, 0]),
            n(4, NodeKind::Add, 1, false, vec![2, 1]),
        ]};
        let run = plan_fixed_order(&inst);
        let e = run_oracle(&inst, Mode::E, 0.0, 30).unwrap();
        assert_eq!(e.status, "optimal");
        assert_eq!(run.result.objective(), (e.traffic, e.instrs)); // uniform width -> EXACT
    }

    #[test]
    #[ignore = "requires python3 + ortools"]
    fn fork_dp_matches_oracle_e_binding_c() {
        use crate::s3_gap::driver::{oracle_available, run_oracle, Mode};
        if !oracle_available() { eprintln!("ortools unavailable; skipping"); return; }
        let inst = OracleInstance { budget: 4, roots: vec![2, 3, 4], nodes: vec![
            n(0, NodeKind::Read, 4, true, vec![]),
            n(1, NodeKind::Read, 4, true, vec![]),
            n(2, NodeKind::Add, 4, false, vec![0]),
            n(3, NodeKind::Add, 4, false, vec![1]),
            n(4, NodeKind::Add, 4, false, vec![0]),
        ]};
        let run = plan_fixed_order(&inst);
        let e = run_oracle(&inst, Mode::E, 0.0, 30).unwrap();
        assert_eq!(e.status, "optimal");
        assert_eq!(run.result.objective(), (e.traffic, e.instrs)); // (12,3): (C) forces the reload
    }

    #[test]
    #[ignore = "requires python3 + ortools"]
    fn fork_dp_matches_oracle_e_cone_fit_c_isolated() {
        use crate::s3_gap::driver::{oracle_available, run_oracle, Mode};
        if !oracle_available() { eprintln!("ortools unavailable; skipping"); return; }
        // budget 2, all base w1: X(0) used by A=Add{0}=2 (s0) and C=Add{0}=4 (s2);
        // B=Add{1,1}=3 (s1) has P[B]=2=budget but a 1-leaf footprint, so (B) permits
        // carrying X (X+Y=2<=2) while (C) (X outsider 1 + P[B] 2 = 3 > 2) forbids it.
        // Confirms the planner's (C) matches solve.py's (C): both must report (3,3), not (2,3).
        let inst = OracleInstance { budget: 2, roots: vec![2, 3, 4], nodes: vec![
            n(0, NodeKind::Read, 1, true, vec![]),
            n(1, NodeKind::Read, 1, true, vec![]),
            n(2, NodeKind::Add, 1, false, vec![0]),
            n(3, NodeKind::Add, 1, false, vec![1, 1]),
            n(4, NodeKind::Add, 1, false, vec![0]),
        ]};
        let run = plan_fixed_order(&inst);
        let e = run_oracle(&inst, Mode::E, 0.0, 30).unwrap();
        assert_eq!(e.status, "optimal");
        assert_eq!(run.result.objective(), (e.traffic, e.instrs));
    }
}
