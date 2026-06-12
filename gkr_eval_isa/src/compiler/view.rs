//! ProgramView: the program DAG. GateOutput/Place are leaves (staged sources);
//! roots are computed gate/cache inputs (-> Dst::GateIn) and non-native output
//! slots (-> Dst::Output). Uses are counted over THIS dag, not AnalysisGraph's.

use cs::gkr_compiler::codegen_ir::{CodegenLayer, ExprNode, gate_kind_input_nodes};
use gkr_design_space::graph::AnalysisGraph;

pub struct ProgramView {
    /// Program-DAG fan-out per arena node: Sum/Product consumer edges plus one
    /// per root reference (gate-in staging or output copy).
    pub uses: Vec<u32>,
    /// staging idx -> arena node. Deduplicated computed (Sum/Product) gate and
    /// cache inputs, in order of first appearance across
    /// gates -> gates_external -> caches.
    pub gate_in_roots: Vec<usize>,
    /// (original output index j, arena node) for output slots the PROGRAM
    /// writes — i.e. slots whose node is NOT a GateOutput (those are stored
    /// natively by gate logic).
    pub program_outputs: Vec<(u16, usize)>,
}

fn add_root_fn(
    node: usize,
    arena: &[ExprNode],
    is_root: &mut Vec<bool>,
    gate_in_roots: &mut Vec<usize>,
    uses: &mut Vec<u32>,
) {
    if matches!(arena[node], ExprNode::Sum { .. } | ExprNode::Product { .. }) && !is_root[node] {
        is_root[node] = true;
        gate_in_roots.push(node);
        uses[node] += 1;
    }
}

pub fn build(layer: &CodegenLayer, g: &AnalysisGraph) -> ProgramView {
    let arena: &[ExprNode] = &layer.arena.nodes;
    let mut uses = vec![0u32; arena.len()];

    // 1. Consumer edges from computed nodes only.
    for (i, n) in arena.iter().enumerate() {
        match n {
            ExprNode::Sum { terms, .. } => {
                for t in terms {
                    // arena ids are append-only CSE: children strictly precede parents
                    debug_assert!((t.0 as usize) < i);
                    uses[t.0 as usize] += 1;
                }
            }
            ExprNode::Product { factors, .. } => {
                for f in factors {
                    // arena ids are append-only CSE: children strictly precede parents
                    debug_assert!((f.0 as usize) < i);
                    uses[f.0 as usize] += 1;
                }
            }
            _ => {}
        }
    }

    // 2. Gate-input roots: computed inputs of every gate and cache, deduped.
    let mut gate_in_roots = Vec::new();
    let mut is_root = vec![false; arena.len()];

    for gate in layer.gates.iter().chain(&layer.gates_external) {
        for id in gate_kind_input_nodes(&gate.kind) {
            add_root_fn(id.0 as usize, arena, &mut is_root, &mut gate_in_roots, &mut uses);
        }
    }
    for cache in &layer.caches {
        for id in &cache.inputs {
            add_root_fn(id.0 as usize, arena, &mut is_root, &mut gate_in_roots, &mut uses);
        }
    }

    // 3. Output slots the program owns (node is not a native GateOutput).
    let mut program_outputs = Vec::new();
    for (j, out) in g.outputs.iter().enumerate() {
        if !matches!(arena[out.node], ExprNode::GateOutput { .. }) {
            program_outputs.push((j as u16, out.node));
            uses[out.node] += 1;
        }
    }

    ProgramView { uses, gate_in_roots, program_outputs }
}

/// Greedy pressure-aware topological order over the ProgramView DAG — used to
/// VALIDATE the arena-order default, and available as an emission order via
/// CompileParams. Among ready computed nodes, pick the one minimizing
/// (cells allocated for the result − cells freed by dying operands);
/// leaves/constants are always ready and emit nothing.
/// Cache-aware greedy list scheduling: among ready computed nodes, pick the
/// one whose operands need the fewest NEW source reads given a simulated
/// resident set of `budget_cells` (LRU eviction; loaded multi-use leaves and
/// computed results are residents, matching dynamic leaf residency). This was
/// the cheap constructive attack on order-dependent eviction loss — the gap
/// between dyn@S and the dyn@∞ floor. Tie-breaks: more cells freed by dying
/// operands first, then arena id (determinism).
///
/// MEASURED NEGATIVE RESULT (dynG report points): loses to dyn-on-arena-order
/// on blake2_ext (+5-9% src reads) and keccak (+27-100%) at every budget;
/// wins only on bigint at the tightest budgets (S=8 −13%, S=16 −8%). Arena
/// order is gate-lowering encounter order — already consumer-clustered cone
/// by cone — and a myopic miss-count greedy scatters that locality (an
/// LIFO/DFS readiness tie-break variant measured the same). Closing the
/// remaining gap to the dyn@∞ floor needs the heavier tools (acyclic
/// partitioning, beam/local search), deliberately deferred.
pub fn reuse_order(arena: &[ExprNode], pv: &ProgramView, budget_cells: usize) -> Vec<usize> {
    use cs::gkr_compiler::codegen_ir::Domain;
    use std::collections::HashMap;
    let n = arena.len();
    let width = |i: usize| -> usize {
        match crate::compiler::node_domain(&arena[i]) {
            Domain::Base => 1,
            Domain::Ext => 4,
        }
    };
    let children = |i: usize| -> Vec<usize> {
        match &arena[i] {
            ExprNode::Sum { terms, .. } => terms.iter().map(|t| t.0 as usize).collect(),
            ExprNode::Product { factors, .. } => factors.iter().map(|f| f.0 as usize).collect(),
            _ => vec![],
        }
    };
    let is_const = |i: usize| matches!(arena[i], ExprNode::Constant(_));

    let mut pending_children: Vec<usize> = (0..n)
        .map(|i| {
            children(i).iter().filter(|&&c| crate::compiler::is_computed(&arena[c])).count()
        })
        .collect();
    let mut remaining_uses: Vec<u32> = pv.uses.clone();
    let mut ready: Vec<usize> = (0..n)
        .filter(|&i| {
            crate::compiler::is_computed(&arena[i]) && pv.uses[i] > 0 && pending_children[i] == 0
        })
        .collect();
    let mut consumers: Vec<Vec<usize>> = vec![vec![]; n];
    for i in 0..n {
        for c in children(i) {
            consumers[c].push(i);
        }
    }

    // Simulated resident set: node -> last-touch tick (LRU), plus used cells.
    let mut resident: HashMap<usize, u64> = HashMap::new();
    let mut used_cells = 0usize;
    let mut tick = 0u64;

    let mut order = Vec::with_capacity(n);
    let mut emitted = vec![false; n];
    while !ready.is_empty() {
        // Score every ready node: distinct non-resident, non-constant operands
        // = new source reads (leaf loads / direct reads / remats) this node
        // would force right now.
        let (pos, _) = ready
            .iter()
            .enumerate()
            .min_by_key(|&(_, &i)| {
                let mut seen: Vec<usize> = Vec::new();
                let mut misses = 0usize;
                let mut freed = 0usize;
                for c in children(i) {
                    if is_const(c) || seen.contains(&c) {
                        continue;
                    }
                    seen.push(c);
                    if !resident.contains_key(&c) {
                        misses += 1;
                    }
                    if remaining_uses[c] == 1 {
                        freed += width(c);
                    }
                }
                (misses, usize::MAX - freed, i)
            })
            .unwrap();
        let i = ready.swap_remove(pos);
        emitted[i] = true;
        order.push(i);

        // Update the simulation: touch/load operands, decrement uses, release
        // dead residents, insert the result, LRU-evict on overflow.
        let mut seen: Vec<usize> = Vec::new();
        for c in children(i) {
            if is_const(c) || seen.contains(&c) {
                continue;
            }
            seen.push(c);
            tick += 1;
            if resident.contains_key(&c) {
                resident.insert(c, tick);
            } else if remaining_uses[c] >= 2 {
                // Load (leaf) or remat (computed): becomes resident.
                resident.insert(c, tick);
                used_cells += width(c);
            }
        }
        for c in children(i) {
            if is_const(c) {
                continue;
            }
            remaining_uses[c] = remaining_uses[c].saturating_sub(1);
            if remaining_uses[c] == 0 && resident.remove(&c).is_some() {
                used_cells -= width(c);
            }
        }
        tick += 1;
        resident.insert(i, tick);
        used_cells += width(i);
        while used_cells > budget_cells {
            let (&lru, _) = resident
                .iter()
                .min_by_key(|&(&node, &t)| (t, node))
                .expect("over capacity with empty resident set");
            resident.remove(&lru);
            used_cells -= width(lru);
        }

        for &parent in &consumers[i] {
            if crate::compiler::is_computed(&arena[parent])
                && pv.uses[parent] > 0
                && !emitted[parent]
            {
                pending_children[parent] -= 1;
                if pending_children[parent] == 0 {
                    ready.push(parent);
                }
            }
        }
    }
    order
}

pub fn pressure_order(arena: &[ExprNode], pv: &ProgramView) -> Vec<usize> {
    use cs::gkr_compiler::codegen_ir::Domain;
    let n = arena.len();
    let width = |i: usize| -> i64 {
        match crate::compiler::node_domain(&arena[i]) {
            Domain::Base => 1,
            Domain::Ext => 4,
        }
    };
    let children = |i: usize| -> Vec<usize> {
        match &arena[i] {
            ExprNode::Sum { terms, .. } => terms.iter().map(|t| t.0 as usize).collect(),
            ExprNode::Product { factors, .. } => factors.iter().map(|f| f.0 as usize).collect(),
            _ => vec![],
        }
    };
    // pending = number of COMPUTED children not yet emitted.
    let mut pending_children: Vec<usize> = (0..n)
        .map(|i| {
            children(i)
                .iter()
                .filter(|&&c| crate::compiler::is_computed(&arena[c]))
                .count()
        })
        .collect();
    let mut remaining_uses: Vec<u32> = pv.uses.clone();
    let mut ready: Vec<usize> = (0..n)
        .filter(|&i| {
            crate::compiler::is_computed(&arena[i]) && pv.uses[i] > 0 && pending_children[i] == 0
        })
        .collect();
    let mut consumers: Vec<Vec<usize>> = vec![vec![]; n];
    for i in 0..n {
        for c in children(i) {
            consumers[c].push(i);
        }
    }
    let mut order = Vec::new();
    let mut emitted = vec![false; n];
    while let Some(pos) = ready
        .iter()
        .enumerate()
        .min_by_key(|&(_, &i)| {
            let freed: i64 = children(i)
                .iter()
                .filter(|&&c| {
                    crate::compiler::is_computed(&arena[c]) && remaining_uses[c] == 1
                })
                .map(|&c| width(c))
                .sum();
            width(i) - freed
        })
        .map(|(p, _)| p)
    {
        let i = ready.swap_remove(pos);
        emitted[i] = true;
        order.push(i);
        for c in children(i) {
            remaining_uses[c] = remaining_uses[c].saturating_sub(1);
        }
        for &parent in &consumers[i] {
            if crate::compiler::is_computed(&arena[parent])
                && pv.uses[parent] > 0
                && !emitted[parent]
            {
                pending_children[parent] -= 1;
                if pending_children[parent] == 0 {
                    ready.push(parent);
                }
            }
        }
    }
    order
}
