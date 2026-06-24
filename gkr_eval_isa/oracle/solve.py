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

The FIRST fix charged a per-stage `base + transient`:

    base(t)      = sum_v width[v] * live[t,v]    (residents + EVERY computed fold acc)
    transient(t) = sum_{folds f at t} max_operand(f)

That was SOUND (never under-counts) but OVER-STRICT for a cone with several
folds in one stage: it forced *all* fold accumulators simultaneously live (the
`base` over-count) AND it SUMMED the per-fold operand bumps (the `transient`
over-count). A real streaming evaluator never holds all of a sum-of-products'
intermediate products at once — it folds them one at a time. The over-strictness
made genuinely-feasible real cones (add_sub L0) infeasible at the real budget 16.

THE SEQUENTIAL (Sethi-Ullman) PEAK
----------------------------------
The minimum cells to evaluate a cone, when every n-ary fold is a binary-streamed
left-fold (`acc = c1; acc (+|*)= c2; ...`, one operand merged at a time, freed
after merging) and children are evaluated in descending-peak order, is the
Sethi-Ullman number of the cone:

    peak(leaf)           = width(leaf)
    peak(fold v; c1..ck) = max( peak(c_(1)),  width(v) + peak(c_(2)) )
                           (children sorted by DESCENDING peak; c_(2) = 2nd largest)

This is the IDEAL (smallest-possible) peak, so it is a TRUE LOWER BOUND on any
real schedule's peak: no evaluator can compute the cone with fewer cells. For a
lone n-ary fold it collapses to `width(result) + max-operand` (the old streaming
bump), so the single-fold LOCK guards are unchanged; for multi-fold cones it
correctly serializes (sum-of-3-ext-products peaks at 12, not the old 32).

ENCODING (per stage t)
----------------------
`P[ri]` = Sethi-Ullman peak of root ri's cone (a per-cone CONSTANT, no T blow-up).
`cone[ri]` = node ids reachable from root ri.

    (B) boundary:   sum_v width[v] * res[t,v]  <=  budget
                    (at the stage boundary all residents coexist — a real instant)

    (C) cone fit:   sum_{v not in cone[ri]} width[v] * carry[t,v]  +  P[ri]  <= budget
                    enforced when mat[t,ri]=1, where
                    carry[t,v] = res[t-1,v] AND res[t,v]  (held resident across the
                    WHOLE stage → continuously live → live at the cone's peak).

Why (C) is a valid lower bound (never over-rejects a real schedule): the cone's
peak instant is >= P[ri] (Sethi-Ullman optimum), and at that instant every value
HELD THROUGH the stage that is not part of the cone is also resident. Cone-internal
values (leaves and sub-results) are already counted inside P[ri], so only the
carried-through OUTSIDERS are added — no double-count. The sum (C) is therefore
<= the true peak, so any schedule whose true peak fits the budget also satisfies
(C). A cone whose P[ri] alone exceeds budget is genuinely infeasible.

Why the budget still BINDS on reload pressure: keeping a shared DRAM leaf resident
across an intervening root (to avoid a reload) charges its width into that root's
(C) constraint via `carry`. When the intervening cone's P is near budget, the leaf
cannot be carried → it must be reloaded → traffic. That tension is exactly the
order/eviction signal the gap experiment measures.
"""
import sys
import json
import time
from ortools.sat.python import cp_model


def _cone_peaks(nodes):
    """Sethi-Ullman cell-peak per node (memoized over the shared-subexpr DAG)."""
    width = {n["id"]: n["width"] for n in nodes}
    children = {n["id"]: n["children"] for n in nodes}
    peak = {}

    def rec(v):
        if v in peak:
            return peak[v]
        ch = children[v]
        if not ch:
            peak[v] = width[v]
            return peak[v]
        cps = sorted((rec(c) for c in ch), reverse=True)
        p = cps[0]
        if len(cps) >= 2:
            p = max(p, width[v] + cps[1])  # binary-streamed fold: acc + 2nd-largest child
        else:
            p = max(p, width[v])           # unary fold: accumulator holds width(v)
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
# -> feasible) under the SEQUENTIAL Sethi-Ullman charge. The single-fold guards
# (4base/4ext/8ext) are unchanged from the streaming model (peak == result +
# max-operand there); guard_sop is the NEW multi-fold lock the relaxation enables.

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


def _guard_4base(budget):
    # LOCK guard 1 (too-loose / soundness floor): Add(4 base reads)→ext.
    # Sethi-Ullman peak = width(result) + max-operand = 4 + 1 = 5.
    # MUST be infeasible below 5, feasible at/above 5 (sub-peak rejects).
    return {"budget": budget, "mode": "J", "roots": [4],
            "nodes": [{"id": 0, "kind": "Read", "width": 1, "real_dram": True, "children": []},
                      {"id": 1, "kind": "Read", "width": 1, "real_dram": True, "children": []},
                      {"id": 2, "kind": "Read", "width": 1, "real_dram": True, "children": []},
                      {"id": 3, "kind": "Read", "width": 1, "real_dram": True, "children": []},
                      {"id": 4, "kind": "Add", "width": 4, "real_dram": False, "children": [0, 1, 2, 3]}]}


def _guard_4ext(budget):
    # LOCK guard 2 (too-strict / calibration): Add(4 ext reads)→ext.
    # Sethi-Ullman peak = 4 + 4 = 8 <= 16. MUST be feasible at 16 (the
    # un-relaxed all-children charge gave 4*4 + 4 = 20 > 16 → infeasible; that
    # over-rejection is the whole reason to relax to the sequential peak).
    return {"budget": budget, "mode": "J", "roots": [4],
            "nodes": [{"id": 0, "kind": "Read", "width": 4, "real_dram": True, "children": []},
                      {"id": 1, "kind": "Read", "width": 4, "real_dram": True, "children": []},
                      {"id": 2, "kind": "Read", "width": 4, "real_dram": True, "children": []},
                      {"id": 3, "kind": "Read", "width": 4, "real_dram": True, "children": []},
                      {"id": 4, "kind": "Add", "width": 4, "real_dram": False, "children": [0, 1, 2, 3]}]}


def _guard_8ext(budget):
    # Wider ext reduction (8 ext inputs): sequential peak stays 4 + 4 = 8 <= 16.
    # MUST still be feasible at 16 (peak does not grow with arity).
    nodes = [{"id": i, "kind": "Read", "width": 4, "real_dram": True, "children": []} for i in range(8)]
    nodes.append({"id": 8, "kind": "Add", "width": 4, "real_dram": False, "children": list(range(8))})
    return {"budget": budget, "mode": "J", "roots": [8], "nodes": nodes}


def _guard_sop(budget):
    # NEW multi-fold LOCK: sum-of-3-ext-products  Add[Mul1,Mul2,Mul3], each
    # Mul = two ext leaves. The OLD base+transient model charged
    #   base = 4(Mul1)+4(Mul2)+4(Mul3)+4(Add) = 16, transient = 4+4+4+4 = 16 → 32
    # → INFEASIBLE at 16. The sequential Sethi-Ullman peak is
    #   peak(Mul) = max(4, 4+4) = 8;  peak(Add) = max(8, 4 + 8) = 12
    # → MUST be infeasible below 12 and feasible at/above 12 (and at 16).
    nodes = [{"id": i, "kind": "Read", "width": 4, "real_dram": True, "children": []} for i in range(6)]
    nodes.append({"id": 6, "kind": "Mul", "width": 4, "real_dram": False, "children": [0, 1]})
    nodes.append({"id": 7, "kind": "Mul", "width": 4, "real_dram": False, "children": [2, 3]})
    nodes.append({"id": 8, "kind": "Mul", "width": 4, "real_dram": False, "children": [4, 5]})
    nodes.append({"id": 9, "kind": "Add", "width": 4, "real_dram": False, "children": [6, 7, 8]})
    return {"budget": budget, "mode": "J", "roots": [9], "nodes": nodes}


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

    # Guard 1: sub-peak rejects. Cliff should be 5 (= 4 + 1).
    cliff_4base = _cliff(_guard_4base)
    out["guard_4base"] = {
        "infeasible@4": solve(_guard_4base(4))["status"],
        "feasible@5": solve(_guard_4base(5))["status"],
        "cliff": cliff_4base,
        "su_peak": 5,
    }
    # Guard 2: not over-rejected. Add(4 ext)→ext feasible at 16 (peak 8).
    cliff_4ext = _cliff(_guard_4ext)
    out["guard_4ext"] = {
        "feasible@16": solve(_guard_4ext(16))["status"],
        "infeasible@7": solve(_guard_4ext(7))["status"],
        "feasible@8": solve(_guard_4ext(8))["status"],
        "cliff": cliff_4ext,
        "su_peak": 8,
    }
    # Wider ext reduction: peak stays 8 → still feasible at 16.
    out["guard_8ext"] = {
        "feasible@16": solve(_guard_8ext(16))["status"],
        "cliff": _cliff(_guard_8ext),
        "su_peak": 8,
    }
    # NEW multi-fold guard: sum-of-products feasible at its SU peak 12 (the old
    # SUM model rejected this at 16); infeasible at 11.
    cliff_sop = _cliff(_guard_sop)
    out["guard_sop"] = {
        "infeasible@11": solve(_guard_sop(11))["status"],
        "feasible@12": solve(_guard_sop(12))["status"],
        "feasible@16": solve(_guard_sop(16))["status"],
        "cliff": cliff_sop,
        "su_peak": 12,
    }

    ok = (
        out["recompute"]["status"] == "optimal"
        and out["recompute"]["traffic"] == 2
        and out["guard_4base"]["infeasible@4"] == "infeasible"
        and out["guard_4base"]["feasible@5"] in ("optimal", "feasible")
        and out["guard_4base"]["cliff"] == 5
        and out["guard_4ext"]["feasible@16"] in ("optimal", "feasible")
        and out["guard_4ext"]["cliff"] == 8
        and out["guard_8ext"]["feasible@16"] in ("optimal", "feasible")
        and out["guard_sop"]["infeasible@11"] == "infeasible"
        and out["guard_sop"]["feasible@12"] in ("optimal", "feasible")
        and out["guard_sop"]["cliff"] == 12
    )
    out["all_pass"] = ok
    return out, ok


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--selftest":
        result, ok = _run_selftest()
        print(json.dumps(result, indent=2))
        sys.exit(0 if ok else 1)
    print(json.dumps(solve(json.load(sys.stdin))))
