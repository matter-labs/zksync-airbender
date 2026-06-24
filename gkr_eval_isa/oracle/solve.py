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

The brief's starting model charged ALL children of a computed fold
simultaneously live (`comp[v] -> live[c]` for every child c). That is SOUND but
too strict: an ext-input reduction with 4 ext children costs 4*4 + 4 = 20 > 16,
so real wide reductions (add_sub L0 hits MAX_ARITY=127) become infeasible at the
real budget 16.

We RELAX toward a STREAMING charge. The true minimum transient working set to
compute a k-ary fold is

    width(result) + max_i width(operand_i)

i.e. the accumulator plus the single largest operand being merged in. A real
streaming reducer loads one operand, merges it into the accumulator, frees it,
then loads the next — so only `acc + one operand` is ever co-resident for the
fold's own transient. For an ext result with ext operands that is 4 + 4 = 8; for
an ext result with base operands it is 4 + 1 = 5.

This is the IDEAL (best-case) transient, which is exactly what makes J a TRUE
LOWER BOUND: no real schedule can compute a fold with less than
`accumulator + one operand` live, and we never charge less than that.

ENCODING
--------
We keep persistent residency capacity (carried `res[t-1,v]` + the result of any
fold computed at t) as the *base* working set charged each stage, and add a
per-stage TRANSIENT bump for the folds computed at t:

    base(t)      = sum_v width[v] * live[t,v]         (residents + computed nodes)
    transient(t) = sum_{folds f computed at t} max_operand_width(f)

    base(t) + transient(t) <= budget                  (within-stage peak)

`live[t,v]` already includes `comp[t,v]` (the fold's own result == accumulator
width) and any carried residents. The transient bump adds exactly the single
largest operand being merged. So for a lone fold f computed into an otherwise
empty cell file we charge `width(f) + max_operand_width(f)`, the streaming peak.

Why this is a valid lower bound (never under-counts below result+one-operand):
`live[t,f]` forces `width(f)` to be charged whenever f is computed (the
accumulator must be live), and `transient(t)` adds at least the largest single
operand width. Their sum is >= width(f) + max_operand_width(f) for every
computed fold, so the model can never let a fold compute with less than
accumulator+operand co-resident. It is a lower bound (not the exact peak)
because it does NOT additionally force every child to be simultaneously
materialized — a streaming reducer is free not to.

Note `max_operand_width(f)` is a per-node CONSTANT (children widths are known
from the instance), so the transient bump is `const * comp[t,f]` — linear, no
auxiliary max variables needed.
"""
import sys
import json
import time
from ortools.sat.python import cp_model


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

    # Streaming transient: the largest single operand merged into a fold's
    # accumulator. Constant per node (children widths are known up front).
    # A fold's within-stage peak is width(result) [charged via live] + this.
    max_operand = {
        n["id"]: (max((width[c] for c in n["children"]), default=0))
        for n in nodes
    }

    m = cp_model.CpModel()
    comp = {(t, v): m.NewBoolVar(f"c{t}_{v}") for t in range(T) for v in range(N)}
    res = {(t, v): m.NewBoolVar(f"r{t}_{v}") for t in range(T) for v in range(N)}
    live = {(t, v): m.NewBoolVar(f"l{t}_{v}") for t in range(T) for v in range(N)}

    def avail(t, v):
        return (res[(t - 1, v)] if t > 0 else 0), comp[(t, v)]

    # Special nodes are leaf-like (resolution terminals): no fold accumulator is
    # charged for them. is_recompute INCLUDES Special (1 instr cost), but is_fold
    # does NOT (no comp->live charge). A new node kind must be classified in BOTH.
    is_fold = {n["id"]: n["kind"] in ("Add", "Mul") for n in nodes}

    for t in range(T):
        for v in range(N):
            # precedence: computing v needs each child available this stage
            for c in children[v]:
                rprev, cnow = avail(t, c)
                m.Add(rprev + cnow >= 1).OnlyEnforceIf(comp[(t, v)])
            prev = res[(t - 1, v)] if t > 0 else 0
            m.Add(res[(t, v)] <= prev + comp[(t, v)])
            m.AddImplication(res[(t, v)], live[(t, v)])  # carried residents are live
            # A FOLD's accumulator must be live while it computes (acc width).
            # A streamed leaf operand (Read/Prior/etc.) that is computed and
            # consumed within the stage is NOT individually charged here — its
            # cost is carried by its consumer fold's `max_operand` transient
            # (streaming: load one operand, merge, free, load next). Charging
            # `comp -> live` for every leaf would over-count to the
            # all-children peak (Σ child widths) and over-reject wide ext
            # reductions; see module docstring.
            if is_fold[v]:
                m.AddImplication(comp[(t, v)], live[(t, v)])
        # WITHIN-STAGE CAPACITY (audit HIGH-1), STREAMING charge:
        #   base working set  = carried residents + fold accumulators (live)
        #   transient bump    = the single largest operand of each computed fold
        # Per-fold charge >= width(result) + max_operand: the accumulator is
        # forced live (width) and the largest operand is added as transient.
        # This is the IDEAL streaming peak (acc + one operand), so it is a TRUE
        # LOWER BOUND — never under-counts below result+one-operand, and never
        # forces every child simultaneously materialized.
        base = sum(width[v] * live[(t, v)] for v in range(N))
        # NOTE (over-strict, NOT unsound): when multiple folds compute at the same
        # stage, their max_operand transients SUM rather than taking the sequential
        # max of the true streaming schedule. Over-strict for deep binary fold-trees
        # in one stage; EXACT for single n-ary L0 reductions (sum == max there).
        # If real instances come out infeasible at budget 16, relax this to a
        # per-stage MAX over folds (deferred per plan).
        transient = sum(max_operand[v] * comp[(t, v)] for v in range(N))
        m.Add(base + transient <= budget)

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
# The recompute-cost selftest plus the two within-stage LOCK guards (audit
# HIGH-1). Each guard records the empirical feasibility cliff (budget at which
# infeasible -> feasible) under the final STREAMING charge.

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
    # Streaming peak = width(result) + max-operand = 4 + 1 = 5.
    # MUST be infeasible below 5, feasible at/above 5 (sub-peak rejects).
    return {"budget": budget, "mode": "J", "roots": [4],
            "nodes": [{"id": 0, "kind": "Read", "width": 1, "real_dram": True, "children": []},
                      {"id": 1, "kind": "Read", "width": 1, "real_dram": True, "children": []},
                      {"id": 2, "kind": "Read", "width": 1, "real_dram": True, "children": []},
                      {"id": 3, "kind": "Read", "width": 1, "real_dram": True, "children": []},
                      {"id": 4, "kind": "Add", "width": 4, "real_dram": False, "children": [0, 1, 2, 3]}]}


def _guard_4ext(budget):
    # LOCK guard 2 (too-strict / calibration): Add(4 ext reads)→ext.
    # Streaming peak = 4 + 4 = 8 <= 16. MUST be feasible at 16 (the
    # un-relaxed all-children charge gave 4*4 + 4 = 20 > 16 → infeasible; that
    # over-rejection is the whole reason to relax to streaming).
    return {"budget": budget, "mode": "J", "roots": [4],
            "nodes": [{"id": 0, "kind": "Read", "width": 4, "real_dram": True, "children": []},
                      {"id": 1, "kind": "Read", "width": 4, "real_dram": True, "children": []},
                      {"id": 2, "kind": "Read", "width": 4, "real_dram": True, "children": []},
                      {"id": 3, "kind": "Read", "width": 4, "real_dram": True, "children": []},
                      {"id": 4, "kind": "Add", "width": 4, "real_dram": False, "children": [0, 1, 2, 3]}]}


def _guard_8ext(budget):
    # Wider ext reduction (8 ext inputs): streaming peak stays 4 + 4 = 8 <= 16.
    # MUST still be feasible at 16 (peak does not grow with arity).
    nodes = [{"id": i, "kind": "Read", "width": 4, "real_dram": True, "children": []} for i in range(8)]
    nodes.append({"id": 8, "kind": "Add", "width": 4, "real_dram": False, "children": list(range(8))})
    return {"budget": budget, "mode": "J", "roots": [8], "nodes": nodes}


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
        "streaming_peak": 5,
    }
    # Guard 2: not over-rejected. Add(4 ext)→ext feasible at 16 (peak 8).
    cliff_4ext = _cliff(_guard_4ext)
    out["guard_4ext"] = {
        "feasible@16": solve(_guard_4ext(16))["status"],
        "infeasible@7": solve(_guard_4ext(7))["status"],
        "feasible@8": solve(_guard_4ext(8))["status"],
        "cliff": cliff_4ext,
        "streaming_peak": 8,
    }
    # Wider ext reduction: peak stays 8 → still feasible at 16.
    out["guard_8ext"] = {
        "feasible@16": solve(_guard_8ext(16))["status"],
        "cliff": _cliff(_guard_8ext),
        "streaming_peak": 8,
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
    )
    out["all_pass"] = ok
    return out, ok


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "--selftest":
        result, ok = _run_selftest()
        print(json.dumps(result, indent=2))
        sys.exit(0 if ok else 1)
    print(json.dumps(solve(json.load(sys.stdin))))
