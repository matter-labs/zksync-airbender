#!/usr/bin/env python3
"""CP-SAT stage-indexed pebbling oracle for the S3 gap experiment.

Reads an `OracleInstance` JSON (plus a `"mode"` field `"J"|"E"`, and optional
`"mip_gap"` / `"max_secs"`) on stdin; writes an `OracleResult` JSON on stdout.

Stages t = 0..T-1, T = len(roots); one root materialized per stage
(J: free permutation of roots over stages; E: fixed identity order — Task 5).
Nodes are topo-ordered (children < parent).

WITHIN-STAGE CAPACITY — the soundness crux (audit HIGH-1)
=========================================================
A time-indexed scheduling model MUST charge the within-stage PEAK working set,
not just end-of-stage residency, or the budget never binds. The original model
solved a 4-input fold at budget 0 and falsely reported "optimal".

THE SINGLE-ACCUMULATOR STREAMING MACHINE MODEL
----------------------------------------------
The eval core has ONE accumulator register that is SEPARATE from the `budget`
cells (it is free — never counted). A fold evaluates as a binary-streamed
left-fold `acc = c1; acc (+|*)= c2; ...`, merging one operand at a time. The
operands stream so they do NOT occupy cache cells:

  * a leaf (Read / VirtualSetup / Special / Literal) streams directly from DRAM
    or the resolver into the accumulator — it never stages in a cell;
  * a `Mul` whose operands all stream FUSES as one FMA term (`acc += a*b`); the
    product is never materialized, so the Mul streams like a leaf;
  * the result streams to its destination (a cell only if DELIBERATELY kept
    resident across stages — a residency decision, not a compute cost).

So an `Add`, or a `Mul` with a non-streaming operand, is the only thing that
needs its own accumulator pass. The ONLY cache pressure inside a cone is spilling
a fold's partial (width(v) cells, traffic-free) when a SECOND non-streaming child
needs the accumulator. With children evaluated in descending-peak order:

    peak(leaf)              = 0                       (streams; streamable)
    streamable(Mul)         = all children streamable (fuses; peak 0)
    peak(fold v) over its NON-STREAMING children F (sorted desc by peak):
        |F| = 0   ->  0                               (everything streamed)
        |F| = 1   ->  peak(F_1)                       (lone pass, no spill)
        |F| >= 2  ->  max( peak(F_1), width(v) + peak(F_2) )  (spill partial for F_2)

This is the IDEAL (smallest-possible) peak → a TRUE LOWER BOUND on any real
schedule's cell peak. A flat reduction (`Add` of reads, or a sum of products)
streams entirely at peak 0; cells are consumed ONLY by fold-of-folds nesting,
which stacks width(v) per level (the real L0 corpus floors at 8 = two ext levels).
This mirrors `forkset::analyze` in the Rust planner EXACTLY — the planner and this
oracle share one cost model (validated by the `*_matches_oracle_e_*` differentials).

The OLD model charged `peak(leaf) = width(leaf)` and summed over ALL children,
i.e. it forced every operand into a cell. That over-charge made genuinely-feasible
real cones (add_sub L0) infeasible at the real budget 16; the streaming model is
the fix.

ENCODING (per stage t)
----------------------
`P[ri]` = streaming peak of root ri's cone (a per-cone CONSTANT, no T blow-up).
`cone[ri]` = node ids reachable from root ri.

    (B) boundary:   sum_v width[v] * res[t,v]  <=  budget
                    (at the stage boundary all residents coexist — a real instant)

    (C) cone fit:   sum_{v not in cone[ri]} width[v] * carry[t,v]  +  P[ri]  <= budget
                    enforced when mat[t,ri]=1, where
                    carry[t,v] = res[t-1,v] AND res[t,v]  (held resident across the
                    WHOLE stage → continuously live → live at the cone's peak).

(B) and (C) are UNCHANGED by the streaming model: residency is a deliberate
decision to hold a value in a cell across the stage, which genuinely occupies
cache — only the transient compute peak P[ri] changed. Why (C) is a valid lower
bound: the cone's peak instant is >= P[ri], and at that instant every value held
through the stage that is not part of the cone is also resident. Cone-internal
values are already inside P[ri], so only carried-through OUTSIDERS are added — no
double-count. A cone whose P[ri] alone exceeds budget is genuinely infeasible.

Why the budget still BINDS on reload pressure: keeping a shared DRAM leaf resident
across an intervening root (to avoid a reload) charges its width into that root's
(C) constraint via `carry`. When the intervening cone's P is near budget (a
fold-of-folds spill), the leaf cannot be carried → it must be reloaded → traffic.
That tension is exactly the order/eviction signal the gap experiment measures.
"""
import sys
import json
import time
from ortools.sat.python import cp_model


def _cone_peaks(nodes):
    """Cell-peak per node under the single-accumulator STREAMING model (mirrors
    `forkset::analyze` in the Rust planner; memoized over the shared-subexpr DAG).

    A leaf (Read/VirtualSetup/Special) streams directly from DRAM / the resolver
    into the free accumulator register, so it occupies NO cache: peak 0, streamable.
    A `Mul` whose operands all stream fuses as one FMA term (`acc += a*b`, the
    product is never materialized), so it streams too. An `Add` — or a `Mul` with a
    non-streaming operand — is a fold that needs its own accumulator pass. The only
    cache pressure is spilling a fold's partial (width(v) cells, traffic-free) when
    a SECOND non-streaming child needs the accumulator: with children sorted by
    descending peak, child c_(1) is folded before the partial exists (no spill),
    and each later non-streaming child c_(i>=2) coexists with the width(v) partial.
    A lone non-streaming child collapses to its own peak (no spill)."""
    width = {n["id"]: n["width"] for n in nodes}
    children = {n["id"]: n["children"] for n in nodes}
    kind = {n["id"]: n["kind"] for n in nodes}
    peak = {}
    streamable = {}

    def rec(v):
        if v in peak:
            return peak[v]
        ch = children[v]
        if not ch:
            streamable[v] = True
            peak[v] = 0
            return 0
        all_stream = True
        fold_peaks = []
        for c in ch:
            rec(c)
            if not streamable[c]:
                all_stream = False
                fold_peaks.append(peak[c])
        streamable[v] = (kind[v] == "Mul") and all_stream
        fold_peaks.sort(reverse=True)
        if not fold_peaks:
            p = 0                                          # all children stream
        elif len(fold_peaks) == 1:
            p = fold_peaks[0]                              # lone fold child: no spill
        else:
            p = max(fold_peaks[0], width[v] + fold_peaks[1])  # spill partial for 2nd
        peak[v] = p
        return p

    for n in nodes:
        rec(n["id"])
    return peak


def _cone_set(root, children):
    """Node ids reachable from `root` (inclusive)."""
    seen = set()
    stack = [root]
    while stack:
        u = stack.pop()
        if u in seen:
            continue
        seen.add(u)
        stack.extend(children[u])
    return seen


def solve(inst):
    nodes = inst["nodes"]
    roots = inst["roots"]
    budget = inst["budget"]
    mode = inst["mode"]
    N = len(nodes)
    T = len(roots)
    width = {n["id"]: n["width"] for n in nodes}
    children = {n["id"]: n["children"] for n in nodes}
    is_dram = {n["id"]: n["real_dram"] for n in nodes}
    # Special-gather terminals (resolution-pruned) cost 0 traffic + 1 instr (spec §3 class 3).
    is_recompute = {n["id"]: n["kind"] in ("Add", "Mul", "Special") for n in nodes}

    # Sethi-Ullman cone peaks (per-node) + per-root cone membership + peak.
    node_peak = _cone_peaks(nodes)
    P = [node_peak[r] for r in roots]
    cones = [_cone_set(r, children) for r in roots]

    # A cone whose IDEAL (Sethi-Ullman) peak already exceeds the budget cannot be
    # evaluated by ANY schedule → the instance is genuinely infeasible.
    if any(P[ri] > budget for ri in range(T)):
        return {"status": "infeasible", "traffic": 0, "instrs": 0, "bound": 0,
                "wall_ms": 0, "schedule": []}

    m = cp_model.CpModel()
    comp = {(t, v): m.NewBoolVar(f"c{t}_{v}") for t in range(T) for v in range(N)}
    res = {(t, v): m.NewBoolVar(f"r{t}_{v}") for t in range(T) for v in range(N)}

    def res_prev(t, v):
        return res[(t - 1, v)] if t > 0 else 0

    for t in range(T):
        for v in range(N):
            # precedence: computing v needs each child available this stage
            for c in children[v]:
                m.Add(res_prev(t, c) + comp[(t, c)] >= 1).OnlyEnforceIf(comp[(t, v)])
            # residency carries forward only if held or (re)computed this stage
            m.Add(res[(t, v)] <= res_prev(t, v) + comp[(t, v)])

    # carry[t,v] = res[t-1,v] AND res[t,v]: v held resident across the WHOLE stage
    # t (the model has no intra-stage eviction, so a held value is continuously
    # live and therefore live at the cone's peak instant).
    carry = {}
    for t in range(1, T):
        for v in range(N):
            cv = m.NewBoolVar(f"k{t}_{v}")
            m.Add(cv <= res[(t - 1, v)])
            m.Add(cv <= res[(t, v)])
            m.Add(cv >= res[(t - 1, v)] + res[(t, v)] - 1)
            carry[(t, v)] = cv

    # root materialization: each root produced at exactly one stage; one per stage
    mat = {(t, ri): m.NewBoolVar(f"m{t}_{ri}") for t in range(T) for ri in range(T)}
    for t in range(T):
        m.Add(sum(mat[(t, ri)] for ri in range(T)) == 1)
    for ri in range(T):
        m.Add(sum(mat[(t, ri)] for t in range(T)) == 1)
    if mode == "E":
        for t in range(T):
            m.Add(mat[(t, t)] == 1)  # fixed identity order (Task 5)
    for t in range(T):
        for ri in range(T):
            m.Add(comp[(t, roots[ri])] >= mat[(t, ri)])  # root produced at its stage

    # WITHIN-STAGE CAPACITY (sequential Sethi-Ullman charge; see module docstring).
    # (B) boundary residency: all residents coexist at the stage boundary.
    for t in range(T):
        m.Add(sum(width[v] * res[(t, v)] for v in range(N)) <= budget)
    # (C) cone peak coexists with residents carried THROUGH the stage that are not
    # part of the cone (cone-internal values are already inside P[ri]). For t=0
    # there is no carry, and P[ri] <= budget is guaranteed above, so (C) is vacuous.
    for t in range(1, T):
        for ri in range(T):
            outsiders = [v for v in range(N) if v not in cones[ri]]
            m.Add(
                sum(width[v] * carry[(t, v)] for v in outsiders) <= budget - P[ri]
            ).OnlyEnforceIf(mat[(t, ri)])

    # objective: lexicographic (traffic, instrs) via big-M
    traffic = sum(width[v] * comp[(t, v)] for t in range(T) for v in range(N) if is_dram[v])
    instrs = sum(comp[(t, v)] for t in range(T) for v in range(N) if is_recompute[v])
    BIG = N * T + 1  # instrs <= N*T < BIG always
    m.Minimize(BIG * traffic + instrs)

    solver = cp_model.CpSolver()
    solver.parameters.max_time_in_seconds = inst.get("max_secs", 1800)
    solver.parameters.relative_gap_limit = inst.get("mip_gap", 0.01)
    solver.parameters.random_seed = 0          # determinism (audit MEDIUM): fix the schedule
    solver.parameters.num_search_workers = 1   # single-worker → reproducible resident_after
    t0 = time.time()
    st = solver.Solve(m)
    wall = int((time.time() - t0) * 1000)
    status = {cp_model.OPTIMAL: "optimal", cp_model.FEASIBLE: "feasible"}.get(st, "infeasible")
    if status == "infeasible":
        return {"status": status, "traffic": 0, "instrs": 0, "bound": 0, "wall_ms": wall, "schedule": []}
    tr = sum(width[v] for t in range(T) for v in range(N) if is_dram[v] and solver.Value(comp[(t, v)]))
    ins = sum(1 for t in range(T) for v in range(N) if is_recompute[v] and solver.Value(comp[(t, v)]))
    sched = []
    for t in range(T):
        ri = next(ri for ri in range(T) if solver.Value(mat[(t, ri)]))
        sched.append({"stage": t, "root": roots[ri],
                      "resident_after": [v for v in range(N) if solver.Value(res[(t, v)])]})
    return {"status": status, "traffic": tr, "instrs": ins,
            "bound": int(solver.BestObjectiveBound() // BIG), "wall_ms": wall, "schedule": sched}


# ── --selftest cases ───────────────────────────────────────────────────────────
# The recompute-cost selftest plus the within-stage LOCK guards (audit HIGH-1).
# Each guard records the empirical feasibility cliff (budget at which infeasible
# -> feasible) under the single-accumulator STREAMING peak. fold_reads and sop
# stream entirely (cliff 0: a flat reduction / sum-of-products needs no cells);
# fold_of_folds (cliff 4) and nested2 (cliff 8) are the binding cases where a
# fold's partial must spill — nested2's 8 is the real L0 corpus ext-width floor.

def _selftest_recompute():
    # ext value (width 4) = Add of two base reads (width 1 each); budget 16.
    # node 2 is real_dram=false → it has NO reload edge; this only confirms
    # recompute cost = 2 base reads (it does NOT exercise a reload-vs-recompute
    # CHOICE — that arises only at a Prior cache-root that also has a producing
    # sub-DAG in-layer; see audit MEDIUM on the §3 trade).
    return {"budget": 16, "mode": "J", "roots": [2],
            "nodes": [{"id": 0, "kind": "Read", "width": 1, "real_dram": True, "children": []},
                      {"id": 1, "kind": "Read", "width": 1, "real_dram": True, "children": []},
                      {"id": 2, "kind": "Add", "width": 4, "real_dram": False, "children": [0, 1]}]}


def _guard_fold_reads(budget):
    # LOCK guard 1 (flat reduction streams): Add(4 ext reads)→ext. Under the
    # single-accumulator STREAMING model every read streams directly from DRAM into
    # the free accumulator register, so the fold occupies NO cache: peak 0.
    # MUST be feasible at budget 0 (the whole reduction is transient-free). The OLD
    # Sethi-Ullman model charged 4 + 4 = 8 here; that over-charge is the bug.
    return {"budget": budget, "mode": "J", "roots": [4],
            "nodes": [{"id": 0, "kind": "Read", "width": 4, "real_dram": True, "children": []},
                      {"id": 1, "kind": "Read", "width": 4, "real_dram": True, "children": []},
                      {"id": 2, "kind": "Read", "width": 4, "real_dram": True, "children": []},
                      {"id": 3, "kind": "Read", "width": 4, "real_dram": True, "children": []},
                      {"id": 4, "kind": "Add", "width": 4, "real_dram": False, "children": [0, 1, 2, 3]}]}


def _guard_sop(budget):
    # LOCK guard 2 (sum-of-products fuses): Add[Mul1,Mul2,Mul3], each Mul = two ext
    # leaves. A Mul whose operands all stream fuses as one FMA term (`acc += a*b`,
    # product never materialized), so it streams like a leaf; the parent Add over
    # three streaming products also streams. peak 0 → MUST be feasible at budget 0.
    # (OLD model: peak(Mul)=8, peak(Add)=12 → infeasible below 12.)
    nodes = [{"id": i, "kind": "Read", "width": 4, "real_dram": True, "children": []} for i in range(6)]
    nodes.append({"id": 6, "kind": "Mul", "width": 4, "real_dram": False, "children": [0, 1]})
    nodes.append({"id": 7, "kind": "Mul", "width": 4, "real_dram": False, "children": [2, 3]})
    nodes.append({"id": 8, "kind": "Mul", "width": 4, "real_dram": False, "children": [4, 5]})
    nodes.append({"id": 9, "kind": "Add", "width": 4, "real_dram": False, "children": [6, 7, 8]})
    return {"budget": budget, "mode": "J", "roots": [9], "nodes": nodes}


def _guard_fold_of_folds(budget):
    # NEW binding LOCK (one spill): v = g + h, g and h each a fold over two ext
    # reads (peak 0). The single accumulator computes g into itself, then must spill
    # g's partial (width(v) = 4 cells, traffic-free) to compute h, then re-add.
    # peak(v) = max(peak(g)=0, width(v)=4 + peak(h)=0) = 4. MUST be infeasible below
    # 4, feasible at/above 4. This is the smallest cone that consumes cache under
    # streaming: a fold whose child is itself a non-streaming fold.
    nodes = [{"id": i, "kind": "Read", "width": 4, "real_dram": True, "children": []} for i in range(4)]
    nodes.append({"id": 4, "kind": "Add", "width": 4, "real_dram": False, "children": [0, 1]})  # g
    nodes.append({"id": 5, "kind": "Add", "width": 4, "real_dram": False, "children": [2, 3]})  # h
    nodes.append({"id": 6, "kind": "Add", "width": 4, "real_dram": False, "children": [4, 5]})  # v
    return {"budget": budget, "mode": "J", "roots": [6], "nodes": nodes}


def _guard_nested2(budget):
    # NEW binding LOCK (spills stack one width per nesting level): two-level
    # fold-of-folds v = H1 + H2, each Hi = gi1 + gi2, each gij a fold over two ext
    # reads. peak(Hi) = 4, peak(v) = max(4, width(v)=4 + 4) = 8. MUST be infeasible
    # below 8, feasible at/above 8. This is exactly the cone-peak floor (8) the real
    # L0 corpus hits at ext width — the deepest reduction nesting in production.
    nodes = [{"id": i, "kind": "Read", "width": 4, "real_dram": True, "children": []} for i in range(8)]
    nodes.append({"id": 8, "kind": "Add", "width": 4, "real_dram": False, "children": [0, 1]})   # g11
    nodes.append({"id": 9, "kind": "Add", "width": 4, "real_dram": False, "children": [2, 3]})   # g12
    nodes.append({"id": 10, "kind": "Add", "width": 4, "real_dram": False, "children": [8, 9]})  # H1, peak 4
    nodes.append({"id": 11, "kind": "Add", "width": 4, "real_dram": False, "children": [4, 5]})  # g21
    nodes.append({"id": 12, "kind": "Add", "width": 4, "real_dram": False, "children": [6, 7]})  # g22
    nodes.append({"id": 13, "kind": "Add", "width": 4, "real_dram": False, "children": [11, 12]})  # H2, peak 4
    nodes.append({"id": 14, "kind": "Add", "width": 4, "real_dram": False, "children": [10, 13]})  # v, peak 8
    return {"budget": budget, "mode": "J", "roots": [14], "nodes": nodes}


def _cliff(build):
    """Return the smallest budget at which `build(b)` is feasible (scan 0..32)."""
    for b in range(0, 33):
        r = solve(build(b))
        if r["status"] in ("optimal", "feasible"):
            return b
    return None


def _run_selftest():
    out = {}
    r = solve(_selftest_recompute())
    out["recompute"] = {"status": r["status"], "traffic": r["traffic"]}

    # Guard 1: a flat reduction streams (peak 0) → feasible at budget 0.
    out["guard_fold_reads"] = {
        "feasible@0": solve(_guard_fold_reads(0))["status"],
        "cliff": _cliff(_guard_fold_reads),
        "peak": 0,
    }
    # Guard 2: sum-of-products fuses (peak 0) → feasible at budget 0.
    out["guard_sop"] = {
        "feasible@0": solve(_guard_sop(0))["status"],
        "cliff": _cliff(_guard_sop),
        "peak": 0,
    }
    # Guard 3: one fold-of-folds spill (peak 4): infeasible below 4, feasible at 4.
    cliff_fof = _cliff(_guard_fold_of_folds)
    out["guard_fold_of_folds"] = {
        "infeasible@3": solve(_guard_fold_of_folds(3))["status"],
        "feasible@4": solve(_guard_fold_of_folds(4))["status"],
        "cliff": cliff_fof,
        "peak": 4,
    }
    # Guard 4: two-level fold-of-folds (peak 8 = the real-corpus ext floor):
    # infeasible below 8, feasible at 8.
    cliff_n2 = _cliff(_guard_nested2)
    out["guard_nested2"] = {
        "infeasible@7": solve(_guard_nested2(7))["status"],
        "feasible@8": solve(_guard_nested2(8))["status"],
        "cliff": cliff_n2,
        "peak": 8,
    }

    ok = (
        out["recompute"]["status"] == "optimal"
        and out["recompute"]["traffic"] == 2
        and out["guard_fold_reads"]["feasible@0"] in ("optimal", "feasible")
        and out["guard_fold_reads"]["cliff"] == 0
        and out["guard_sop"]["feasible@0"] in ("optimal", "feasible")
        and out["guard_sop"]["cliff"] == 0
        and out["guard_fold_of_folds"]["infeasible@3"] == "infeasible"
        and out["guard_fold_of_folds"]["feasible@4"] in ("optimal", "feasible")
        and out["guard_fold_of_folds"]["cliff"] == 4
        and out["guard_nested2"]["infeasible@7"] == "infeasible"
        and out["guard_nested2"]["feasible@8"] in ("optimal", "feasible")
        and out["guard_nested2"]["cliff"] == 8
    )
    out["all_pass"] = ok
    return out, ok


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--selftest":
        result, ok = _run_selftest()
        print(json.dumps(result, indent=2))
        sys.exit(0 if ok else 1)
    print(json.dumps(solve(json.load(sys.stdin))))
