//! Backward L0 value-reuse structure diagnostics (design-space analysis for the
//! fold-caching decision layer). All `#[ignore]`d — run explicitly.
//!
//! These characterize, per circuit and *without fixing an execution order*, how
//! values are reused in the distilled backward root cone, and how the relations
//! (spine terms) couple through shared values. They exist to answer the design
//! questions:
//!   1. Is the distilled backward DAG a tree, or are there reusable *intermediate*
//!      (non-Source) values? (`fanout_arity_census_l0`)
//!   2. Which reuse is DRAM-read (FiF-valid, free to re-gather cost) vs recomputable
//!      intermediate (decision-dependent)? α-powers/constants are FREE and excluded.
//!   3. How do relations cluster around shared values, and can caching a few hub
//!      values decouple them? (`cluster_analysis_l0`, `hub_class_and_fragmentation_l0`)
//!
//! Method: seed from the single distilled backward root (`d.layer.roots[d.root]`)
//! and walk its cone, mirroring `cs::…::simplify::fan_out` (root seed + Add/Mul
//! children + `LookupValue.query` edges). The distilled layer is freshly
//! hash-consed (distill.rs / arena.rs `intern_expr`), so a shared intermediate is
//! exactly a non-Source `ExprId` with fan-out ≥ 2. Ext regime throughout; the
//! structure is regime-invariant (R0 == Ext, asserted in `fanout_arity_census_l0`).
mod common;

use std::collections::{BTreeMap, HashMap, HashSet};

use common::load_layer;
use gkr_eval_ir::{Expr, SourceInfo, SourceKind};
use gkr_eval_isa::BwdRegime;
use gkr_eval_isa::bwd::compile::spine_terms;
use gkr_eval_isa::bwd::distill::distill;

const FIXTURES: &[&str] = &[
    "add_sub_lui_auipc_mop_layout_gkr.json",
    "bigint_with_extended_control_layout_gkr.json",
    "blake2_g_function_layout_gkr.json",
    "blake2_with_extended_control_layout_gkr.json",
    "inits_and_teardowns_preprocessed_layout_gkr.json",
    "jump_branch_slt_layout_gkr.json",
    "keccak_special5_layout_gkr.json",
    "mem_subword_only_layout_gkr.json",
    "mem_word_only_layout_gkr.json",
    "shift_binop_layout_gkr.json",
    "unsigned_mul_div_layout_gkr.json",
    "unified_reduced_machine_layout_gkr.json",
];

/// Class of a distilled node for the caching prize. Only `Read` costs DRAM;
/// `Challenge` (α-powers), `Constant`, `VirtualSetup` (closed-form) are FREE and
/// must NOT be counted as a caching prize. `LookupValue` is reported separately.
fn class_of(exprs: &[Expr], sources: &[SourceInfo], eid: u32) -> &'static str {
    match &exprs[eid as usize] {
        Expr::Add(_) | Expr::Mul(_) => "INTERMEDIATE",
        Expr::Source(sid) => match &sources[sid.0 as usize].kind {
            SourceKind::Read { .. } => "Read(DRAM)",
            SourceKind::Constant { .. } => "Constant(free)",
            SourceKind::Challenge { .. } => "Challenge(free)",
            SourceKind::VirtualSetup { .. } => "VirtualSetup(free)",
            SourceKind::LookupValue { .. } => "LookupValue",
        },
    }
}

fn is_cacheable(class: &str) -> bool {
    class == "Read(DRAM)" || class == "INTERMEDIATE"
}

const CLASSES: &[&str] = &[
    "Read(DRAM)",
    "LookupValue",
    "INTERMEDIATE",
    "Challenge(free)",
    "Constant(free)",
    "VirtualSetup(free)",
];

// ── fan-out-arity census ──────────────────────────────────────────────────────

/// fan-out histograms for one cone, keyed by node class.
struct Hist {
    by_class: BTreeMap<&'static str, BTreeMap<usize, usize>>,
}

fn cone_hist(name: &str, regime: BwdRegime) -> Option<Hist> {
    let (layer, cross) = load_layer(name, 0);
    let d = distill(&layer, regime, &cross, None);
    if d.skipped_decoder {
        return None;
    }
    let root_expr = d.layer.roots[d.root.0 as usize].expr;

    let mut counts: HashMap<u32, usize> = HashMap::new();
    let mut seen: HashSet<u32> = HashSet::new();
    let mut work: Vec<u32> = Vec::new();
    *counts.entry(root_expr.0).or_insert(0) += 1;
    seen.insert(root_expr.0);
    work.push(root_expr.0);
    while let Some(id) = work.pop() {
        match &d.layer.exprs[id as usize] {
            Expr::Add(children) | Expr::Mul(children) => {
                for c in children {
                    *counts.entry(c.0).or_insert(0) += 1;
                    if seen.insert(c.0) {
                        work.push(c.0);
                    }
                }
            }
            Expr::Source(sid) => {
                if let SourceKind::LookupValue { query, .. } = &d.layer.sources[sid.0 as usize].kind {
                    *counts.entry(query.0).or_insert(0) += 1;
                    if seen.insert(query.0) {
                        work.push(query.0);
                    }
                }
            }
        }
    }

    let mut h = Hist { by_class: BTreeMap::new() };
    for (&eid, &cnt) in &counts {
        let class = class_of(&d.layer.exprs, &d.layer.sources, eid);
        *h.by_class.entry(class).or_default().entry(cnt).or_insert(0) += 1;
    }
    Some(h)
}

fn fmt_dist(hist: &BTreeMap<usize, usize>) -> (usize, usize, usize, String) {
    // total nodes, shared(>=2) node count, reuse_wt = sum (fanout-1)*count over fanout>=2,
    // and the exact sparse distribution string "f×count f×count ...".
    let total: usize = hist.values().sum();
    let mut shared = 0usize;
    let mut reuse_wt = 0usize;
    for (&f, &c) in hist.iter() {
        if f >= 2 {
            shared += c;
            reuse_wt += (f - 1) * c;
        }
    }
    let dist = hist
        .iter()
        .map(|(f, c)| format!("{f}×{c}"))
        .collect::<Vec<_>>()
        .join(" ");
    (total, shared, reuse_wt, dist)
}

#[test]
#[ignore = "diagnostic: run with --ignored --nocapture"]
fn fanout_arity_census_l0() {
    println!("\n# Distilled backward L0 — EXACT fan-out-arity distribution by node class");
    println!("# dist entries are `fanout×node_count`. shared = nodes with fanout>=2.");
    println!("# reuse_wt = Σ(fanout-1)·count over fanout>=2 = redundant references a cache-once removes.");
    println!("# Read(DRAM) + INTERMEDIATE are cacheable; Challenge/Constant/VirtualSetup are FREE.\n");

    for name in FIXTURES {
        let stem = name.trim_end_matches("_layout_gkr.json");
        let h_ext = match cone_hist(name, BwdRegime::Ext) {
            Some(h) => h,
            None => {
                println!("## {stem} L0 — SKIPPED (decoder)\n");
                continue;
            }
        };
        // regime-invariance: R0 must produce identical histograms.
        if let Some(h_r0) = cone_hist(name, BwdRegime::R0) {
            assert_eq!(h_r0.by_class, h_ext.by_class, "[{stem}] class hist differs R0 vs Ext");
        }

        println!("## {stem} L0");
        let empty = BTreeMap::new();
        for &class in CLASSES {
            let hist = h_ext.by_class.get(class).unwrap_or(&empty);
            if hist.is_empty() {
                continue;
            }
            let (t, s, w, d) = fmt_dist(hist);
            println!("  {class:<19} total={t:<5} shared≥2={s:<4} reuse_wt={w}");
            println!("      dist: {d}");
        }
        println!();
    }
}

// ── union-find + shared-value extraction (cluster / fragmentation) ────────────

struct Uf {
    p: Vec<usize>,
}
impl Uf {
    fn new(n: usize) -> Self {
        Uf { p: (0..n).collect() }
    }
    fn find(&mut self, x: usize) -> usize {
        let mut r = x;
        while self.p[r] != r {
            r = self.p[r];
        }
        let mut c = x;
        while self.p[c] != c {
            let n = self.p[c];
            self.p[c] = r;
            c = n;
        }
        r
    }
    fn union(&mut self, a: usize, b: usize) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra != rb {
            self.p[ra] = rb;
        }
    }
}

/// For fixture `name` L0: the unit count and, per value in the root cone,
/// (class, gcount = total refs, consumers = distinct unit indices whose cone
/// contains it). Shared across all cluster/fragmentation diagnostics.
fn cone_reuse(name: &str) -> Option<(usize, Vec<(&'static str, usize, Vec<u32>)>)> {
    let (layer, cross) = load_layer(name, 0);
    let d = distill(&layer, BwdRegime::Ext, &cross, None);
    if d.skipped_decoder {
        return None;
    }
    let terms = spine_terms(&d);
    let n = terms.len();

    // consumers[eid] = distinct unit indices whose cone contains eid.
    let mut consumers: HashMap<u32, Vec<u32>> = HashMap::new();
    for (ti, &term) in terms.iter().enumerate() {
        let mut seen: HashSet<u32> = HashSet::new();
        let mut work = vec![term.0];
        seen.insert(term.0);
        while let Some(id) = work.pop() {
            consumers.entry(id).or_default().push(ti as u32);
            match &d.layer.exprs[id as usize] {
                Expr::Add(ch) | Expr::Mul(ch) => {
                    for c in ch {
                        if seen.insert(c.0) {
                            work.push(c.0);
                        }
                    }
                }
                Expr::Source(sid) => {
                    if let SourceKind::LookupValue { query, .. } = &d.layer.sources[sid.0 as usize].kind {
                        if seen.insert(query.0) {
                            work.push(query.0);
                        }
                    }
                }
            }
        }
    }

    // gcount[eid] = total references (fan-out) from the single root cone.
    let root_expr = d.layer.roots[d.root.0 as usize].expr;
    let mut gcount: HashMap<u32, usize> = HashMap::new();
    {
        let mut seen: HashSet<u32> = HashSet::new();
        let mut work = vec![root_expr.0];
        *gcount.entry(root_expr.0).or_insert(0) += 1;
        seen.insert(root_expr.0);
        while let Some(id) = work.pop() {
            match &d.layer.exprs[id as usize] {
                Expr::Add(ch) | Expr::Mul(ch) => {
                    for c in ch {
                        *gcount.entry(c.0).or_insert(0) += 1;
                        if seen.insert(c.0) {
                            work.push(c.0);
                        }
                    }
                }
                Expr::Source(sid) => {
                    if let SourceKind::LookupValue { query, .. } = &d.layer.sources[sid.0 as usize].kind {
                        *gcount.entry(query.0).or_insert(0) += 1;
                        if seen.insert(query.0) {
                            work.push(query.0);
                        }
                    }
                }
            }
        }
    }

    let mut out = Vec::new();
    for (&eid, cons) in &consumers {
        let class = class_of(&d.layer.exprs, &d.layer.sources, eid);
        let g = gcount.get(&eid).copied().unwrap_or(0);
        out.push((class, g, cons.clone()));
    }
    Some((n, out))
}

#[test]
#[ignore = "diagnostic: run with --ignored --nocapture"]
fn cluster_analysis_l0() {
    println!("\n# Distilled backward L0 — relation-cluster analysis (order-independent)");
    println!("# units = spine terms. cacheable value = class in {{Read(DRAM), INTERMEDIATE}}.");
    println!("# INTRA = fanout>=2 but consumed by exactly 1 unit (local reuse). INTER = consumed by >=2 units.");
    println!("# consumer_count dist shows local(2u) vs global sharing; components show separability.\n");
    println!("| circuit | units | INTRA | INTER | consumer_count dist (INTER) | components (sizes) |");
    println!("| --- | --- | --- | --- | --- | --- |");

    for name in FIXTURES {
        let stem = name.trim_end_matches("_layout_gkr.json");
        let Some((n, vals)) = cone_reuse(name) else {
            println!("| {stem} | — | SKIPPED (decoder) | | | |");
            continue;
        };
        let mut intra = 0usize;
        let mut inter_hist: BTreeMap<usize, usize> = BTreeMap::new();
        let mut uf = Uf::new(n.max(1));
        for (class, g, cons) in &vals {
            if !is_cacheable(class) {
                continue;
            }
            if cons.len() >= 2 {
                *inter_hist.entry(cons.len()).or_insert(0) += 1;
                for w in cons.windows(2) {
                    uf.union(w[0] as usize, w[1] as usize);
                }
            } else if *g >= 2 {
                intra += 1;
            }
        }
        let mut comp: HashMap<usize, usize> = HashMap::new();
        for u in 0..n {
            let r = uf.find(u);
            *comp.entry(r).or_insert(0) += 1;
        }
        let mut sizes: Vec<usize> = comp.values().copied().collect();
        sizes.sort_unstable_by(|a, b| b.cmp(a));
        let inter_total: usize = inter_hist.values().sum();
        let inter_dist = inter_hist.iter().map(|(k, v)| format!("{k}u×{v}")).collect::<Vec<_>>().join(" ");
        println!(
            "| {stem} | {n} | {intra} | {inter_total} | {inter_dist} | {} comp: {:?} |",
            sizes.len(),
            &sizes[..sizes.len().min(8)]
        );
    }
}

fn largest_component(n: usize, edges_from: &[&Vec<u32>]) -> usize {
    let mut uf = Uf::new(n.max(1));
    for cons in edges_from {
        for w in cons.windows(2) {
            uf.union(w[0] as usize, w[1] as usize);
        }
    }
    let mut sizes: HashMap<usize, usize> = HashMap::new();
    for u in 0..n {
        let r = uf.find(u);
        *sizes.entry(r).or_insert(0) += 1;
    }
    sizes.values().copied().max().unwrap_or(0)
}

#[test]
#[ignore = "diagnostic: run with --ignored --nocapture"]
fn hub_class_and_fragmentation_l0() {
    // (a) hub class split: INTER-unit shared values by class and degree.
    println!("\n# (a) INTER-unit shared values by class + degree (consumer_count)");
    println!("| circuit | Read(DRAM) INTER dist | INTERMEDIATE INTER dist | top-20 hubs R/I |");
    println!("| --- | --- | --- | --- |");
    for name in FIXTURES {
        let stem = name.trim_end_matches("_layout_gkr.json");
        let Some((_n, vals)) = cone_reuse(name) else {
            println!("| {stem} | SKIPPED | | |");
            continue;
        };
        let inter: Vec<(&str, usize)> = vals
            .iter()
            .filter(|(c, _g, cons)| is_cacheable(c) && cons.len() >= 2)
            .map(|(c, _g, cons)| (*c, cons.len()))
            .collect();
        let mut read_h: BTreeMap<usize, usize> = BTreeMap::new();
        let mut int_h: BTreeMap<usize, usize> = BTreeMap::new();
        for (c, deg) in &inter {
            let h = if *c == "Read(DRAM)" { &mut read_h } else { &mut int_h };
            *h.entry(*deg).or_insert(0) += 1;
        }
        let mut by_deg = inter.clone();
        by_deg.sort_by(|a, b| b.1.cmp(&a.1));
        let top_read = by_deg.iter().take(20).filter(|(c, _)| *c == "Read(DRAM)").count();
        let top_int = by_deg.iter().take(20).count() - top_read;
        let fmt = |h: &BTreeMap<usize, usize>| h.iter().map(|(k, v)| format!("{k}u×{v}")).collect::<Vec<_>>().join(" ");
        println!("| {stem} | {} | {} | R:{top_read} I:{top_int} |", fmt(&read_h), fmt(&int_h));
    }

    // (b) fragmentation: cache (remove) the top-k highest-degree hubs, recompute
    // the largest remaining coupled component.
    let ks = [0usize, 5, 10, 20, 30, 50, 100];
    println!("\n# (b) fragmentation — cache top-k hubs (by degree), largest remaining coupled component");
    println!("# cell = largest component size (units) after removing the k highest-degree shared values.");
    println!("| circuit | units | k=0 | k=5 | k=10 | k=20 | k=30 | k=50 | k=100 |");
    println!("| --- | --- | --- | --- | --- | --- | --- | --- | --- |");
    for name in FIXTURES {
        let stem = name.trim_end_matches("_layout_gkr.json");
        let Some((n, vals)) = cone_reuse(name) else {
            println!("| {stem} | SKIPPED | | | | | | | |");
            continue;
        };
        let mut inter: Vec<Vec<u32>> = vals
            .into_iter()
            .filter(|(c, _g, cons)| is_cacheable(c) && cons.len() >= 2)
            .map(|(_c, _g, cons)| cons)
            .collect();
        inter.sort_by(|a, b| b.len().cmp(&a.len())); // degree desc
        let cells: Vec<String> = ks
            .iter()
            .map(|&k| {
                let remaining: Vec<&Vec<u32>> = inter.iter().skip(k).collect();
                format!("{}", largest_component(n, &remaining))
            })
            .collect();
        println!("| {stem} | {n} | {} |", cells.join(" | "));
    }
}

// ── working set under a linear arrangement (ordering angle) ───────────────────

/// Reverse Cuthill-McKee ordering of `n` units over adjacency `adj` (bandwidth
/// reduction heuristic): BFS from the min-degree unvisited node, visiting
/// neighbours in ascending degree, then reverse. Returns position→unit.
fn rcm_order(n: usize, adj: &[Vec<u32>]) -> Vec<u32> {
    let deg: Vec<usize> = adj.iter().map(|a| a.len()).collect();
    let mut visited = vec![false; n];
    let mut order: Vec<u32> = Vec::with_capacity(n);
    loop {
        let Some(start) = (0..n).filter(|&u| !visited[u]).min_by_key(|&u| deg[u]) else {
            break;
        };
        let mut q = std::collections::VecDeque::new();
        visited[start] = true;
        q.push_back(start as u32);
        while let Some(u) = q.pop_front() {
            order.push(u);
            let mut nbrs: Vec<u32> =
                adj[u as usize].iter().copied().filter(|&v| !visited[v as usize]).collect();
            nbrs.sort_by_key(|&v| deg[v as usize]);
            for v in nbrs {
                if !visited[v as usize] {
                    visited[v as usize] = true;
                    q.push_back(v);
                }
            }
        }
    }
    order.reverse();
    order
}

/// Peak working set: max over unit positions of the number of values whose live
/// interval [min consumer position, max consumer position] spans that position.
/// `pos[unit]` = position of the unit in the order.
fn peak_ws(n: usize, values: &[Vec<u32>], pos: &[usize]) -> usize {
    let mut delta = vec![0i64; n + 1];
    for cons in values {
        let lo = cons.iter().map(|&u| pos[u as usize]).min().unwrap();
        let hi = cons.iter().map(|&u| pos[u as usize]).max().unwrap();
        delta[lo] += 1;
        delta[hi + 1] -= 1;
    }
    let mut cur = 0i64;
    let mut peak = 0i64;
    for d in &delta {
        cur += d;
        peak = peak.max(cur);
    }
    peak as usize
}

#[test]
#[ignore = "diagnostic: run with --ignored --nocapture"]
fn working_set_under_ordering_l0() {
    println!("\n# Distilled backward L0 — peak working set (min residents for ZERO recompute/re-gather)");
    println!("# value = cacheable (Read/Intermediate) shared across >=2 units; live [first..last consuming unit].");
    println!("# peak WS = max concurrently-live such values = cache size a given order needs for full reuse.");
    println!("# natural = spine-term order as-is; RCM = bandwidth-reduced order (a good heuristic, not optimal).");
    println!("# Compare peak WS to the FC extra-bucket budget (~8-12 Ext buckets).\n");
    println!("| circuit | units | inter values | peak WS natural | peak WS RCM |");
    println!("| --- | --- | --- | --- | --- |");

    for name in FIXTURES {
        let stem = name.trim_end_matches("_layout_gkr.json");
        let Some((n, vals)) = cone_reuse(name) else {
            println!("| {stem} | — | SKIPPED | | |");
            continue;
        };
        let inter: Vec<Vec<u32>> = vals
            .into_iter()
            .filter(|(c, _g, cons)| is_cacheable(c) && cons.len() >= 2)
            .map(|(_c, _g, cons)| cons)
            .collect();

        // natural order: unit i at position i.
        let nat_pos: Vec<usize> = (0..n).collect();
        let nat = peak_ws(n, &inter, &nat_pos);

        // RCM order over the clique-expanded unit graph.
        let mut adjset: Vec<HashSet<u32>> = vec![HashSet::new(); n];
        for cons in &inter {
            for i in 0..cons.len() {
                for j in (i + 1)..cons.len() {
                    adjset[cons[i] as usize].insert(cons[j]);
                    adjset[cons[j] as usize].insert(cons[i]);
                }
            }
        }
        let adj: Vec<Vec<u32>> = adjset.into_iter().map(|s| s.into_iter().collect()).collect();
        let ord = rcm_order(n, &adj);
        let mut rcm_pos = vec![0usize; n];
        for (p, &u) in ord.iter().enumerate() {
            rcm_pos[u as usize] = p;
        }
        let rcm = peak_ws(n, &inter, &rcm_pos);

        println!("| {stem} | {n} | {} | {nat} | {rcm} |", inter.len());
    }
    println!("\n# If peak WS (RCM) >> ~12 buckets, even a good order cannot avoid eviction => recompute is");
    println!("# forced (the decision-dependent regime). If peak WS (RCM) <= budget, ordering alone gives full reuse.");
}
