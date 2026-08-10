#!/usr/bin/env python3
"""Emit the v3 R6 carveout-probe decision from one ABBA session's four logs.

R6 NOTE. This script is THE SINGLE AUTHORITY for every derived decision of the probe —
the per-lane signed verdicts, the stability precondition, P1's (a)/(b)/(c) branch, the
frontier position and its right-censoring, P2's flank gate and its two deltas, the sanity
verdict and the ncu capture manifest. Nothing decision-bearing is computed by hand or in
the record; each decision line names the preregistered rule (spec
`.agents/specs/2026-08-10-gkr-uniskip-v3-r6-carveout-probe-design.md`, sections
*Preregistered decisions* and *Codex verdict*) it implements.

Everything decision-bearing is read from IN-LOG metadata — the term order, the hint state,
the round count, C, the lane plans. A FILENAME NEVER DECIDES ANYTHING: the four logs are
positional (the session's ABBA order) and the hint sequence they must carry is checked
against that position, so a mis-ordered set is rejected rather than summarized under the
wrong pairing.

The CONFIGURATION IS PINNED, not merely read: `--term-order locality`, `--carveout-hint 16`
on the hinted processes, 100 rounds and warmup 10. Every rule below is preregistered against
exactly that configuration — the sanity anchors are per-order, the 90/100 signed threshold
is keyed to the round count, and G0 proved that 16 % is the one percentage that realizes the
32 KiB carveout on this driver (25 % did not). A log outside the pin is a different
experiment and is rejected. The hint state is corroborated twice: the schedule line states
what was requested, and the harness's `carveout hint <pct>%` echo states what
`cudaFuncSetAttribute` was actually called with — they must agree, and an unhinted process
must carry no echo at all.

Contrasts are PAIRED per round: the runner executes all five lanes inside one round in a
cyclic rotation, so a round's lanes share whatever clock state that round had. The metric
is `eval + finalize`, the same quantity R5's bar was taken on — the 128 lanes run twice the
grid, so finalize is not the same work on the two block sizes and the cross-size lane
(control@256) cannot be compared on `eval` alone.

The lane SET, the signed rule and the anchors are pinned; the lane FACTS (kernel, regs,
blocks/SM, threads, grid, C, removals, admitted ids) are data-driven from the log's `ARM`
lines, which Rust fills from each lane's own planned counts. No C, kernel name or removal
count is written here.

Usage:
    python3 gpu/gkr_uniskip_bench/tools/r6_probe_table.py off1.log on1.log on2.log off2.log
"""

import sys
import re
from collections import defaultdict
from statistics import median

TAG = "CARVEOUT-PROBE"
SCHED = re.compile(
    r"^CARVEOUT-PROBE schedule order=(\S+) lanes=(\d+) rounds=(\d+) warmup=(\d+) "
    r"carveout-hint=(default|\d+)$"
)
DONE = re.compile(r"^CARVEOUT-PROBE done order=(\S+) warmup=(\d+) rounds=(\d+) lanes=(\d+)$")
ARM = re.compile(r"^ARM (\S+) (\d+) (\d+) (\d+) (\d+) (\S+) (\d+) (\d+) (\d+) (\S+)$")
SAMPLE = re.compile(r"^SAMPLE (\S+) (\d+) (\S+) ([\d.]+) ([\d.]+) (\S+)$")
# The harness's APPLIED-hint echo, matched on the RAW line (its indentation is part of the
# runner's literal). The schedule line states what was REQUESTED; this line is printed by
# the harness after `cudaFuncSetAttribute` actually ran, so the two together are what pins a
# process's hint state. A schedule line alone can be edited.
ECHO = re.compile(r"^  carveout hint       (\d+)% \(eval_lsb_pair_cached_128_lb\)$")
ECHO_ANY = "carveout hint"

# The probe rotation, pinned as an integrity gate: a log carrying a different lane set is a
# different experiment and is rejected rather than partially summarized.
LANE_ORDER = ("k24@128", "k32@128", "k40@128", "hot16@128", "control@256")
LANES = set(LANE_ORDER)
KS = ("k24@128", "k32@128", "k40@128")
HOT = "hot16@128"
CTL = "control@256"
# The K a named lane claims, cross-checked against its admitted count and its id list, so a
# mislabelled lane is caught as well as a truncated one. C is NOT here — it rides the ARM
# lines.
LANE_K = {"k24@128": 24, "k32@128": 32, "k40@128": 40, HOT: 16, CTL: 0}

# The four processes, by POSITION on the command line: the session is ABBA by hint state.
PROCS = ("off1", "on1", "on2", "off2")
OFFS = (0, 3)
ONS = (1, 2)
# The adjacent ABBA pairs P2 is defined over (spec, codex amendment 5): (off1, on1) and
# (on2, off2). Each entry is (label, off index, on index).
PAIRS = (("off1/on1", 0, 1), ("on2/off2", 3, 2))

# THE PINNED CONTRACT. The R6 probe is preregistered as ONE configuration — the locality
# (= shipping) order, the G0-verified 16 % hint, 100 rounds and warmup 10 — and every rule
# below is registered against exactly that. A log outside it has no preregistered rule to be
# decided under: the anchors are per-order, the 90/100 threshold is keyed to the round count,
# and 16 % is the ONLY percentage G0 proved realizes the 32 KiB configuration (25 % did not).
# Accepting a near-miss and summarizing it anyway is precisely what preregistration exists to
# prevent, so anything else is a stated rejection.
PINNED_ORDER = "locality"
PINNED_HINT = "16"
PINNED_ROUNDS = 100
PINNED_WARMUP = 10

# R4's frozen in-rotation anchors, by term order: (control@256, hot16@128) eval+finalize
# medians. Same constants as r4_table.py — R6 inherits them, and the hot16 anchor applies
# to the OFF processes only (the hinted ones are the thing being measured). Only the
# `locality` row is reachable under the pin above; the census row is carried verbatim
# because these are copied constants, not R6's to edit.
ANCHORS = {"census": (16.545, 15.129), "locality": (16.624, 14.836)}
SANITY_TOL = 0.02
# P2's flank agreement: the cross-process anchor must agree to this in a pair, or the pair
# carries a session shift that the bridged delta would silently absorb.
FLANK_MS = 0.05
# P1 (b): "shrink to <= half the off-process delta", pairwise against the ADJACENT off.
HALF = 0.5


def threshold(rounds):
    """The preregistered signed threshold: at least 90 % of the rounds on-sign. Integer
    ceiling, so the literal is exact at the session's 100 rounds (90) and at any fixture
    count."""
    return (9 * rounds + 9) // 10


def signed(diffs, rounds):
    """R5's signed rule, verbatim: A *wins over* B iff the median of the paired per-round
    contrasts is negative AND at least `threshold` of them are negative; *loses* is the
    mirror; anything else is a *wash*."""
    med = median(diffs)
    neg = sum(1 for x in diffs if x < 0)
    pos = sum(1 for x in diffs if x > 0)
    if med < 0 and neg >= threshold(rounds):
        return "win", med, neg
    if med > 0 and pos >= threshold(rounds):
        return "loss", med, pos
    return "wash", med, max(neg, pos)


def load(path):
    """One process. Every gate here is fail-closed: a violation exits non-zero with the
    reason, never a partially summarized log."""
    sched = done = echo = None
    arms = {}
    rounds = defaultdict(dict)
    for n, raw in enumerate(open(path), 1):
        raw = raw.rstrip("\n")
        line = raw.strip()
        m = ECHO.match(raw)
        if m:
            if echo is not None:
                sys.exit(f"{path}:{n}: a second applied-hint echo line — one log is one "
                         f"process, and the hint is set once before any launch")
            echo = int(m.group(1))
            continue
        if line.startswith(ECHO_ANY):
            sys.exit(f"{path}:{n}: `{line}` is not the harness's applied-hint echo line — "
                     f"the literal is `  carveout hint       <pct>% "
                     f"(eval_lsb_pair_cached_128_lb)`, and this gate corroborates the "
                     f"schedule line against the hint the process actually applied")
        m = SCHED.match(line)
        if m:
            if sched is not None:
                sys.exit(f"{path}:{n}: a second `{TAG} schedule` line — one log is one "
                         f"process; emit the four processes as four logs")
            sched = {"order": m.group(1), "lanes": int(m.group(2)),
                     "rounds": int(m.group(3)), "warmup": int(m.group(4)),
                     "hint": m.group(5)}
            continue
        if line.startswith(f"{TAG} schedule"):
            sys.exit(f"{path}:{n}: malformed `{TAG} schedule` line — the probe grammar is "
                     f"`{TAG} schedule order=<o> lanes=<n> rounds=<r> warmup=<w> "
                     f"carveout-hint=<default|pct>`, and the hint state is read from HERE, "
                     f"never from the filename")
        m = DONE.match(line)
        if m:
            if done is not None:
                sys.exit(f"{path}:{n}: a second `{TAG} done` trailer — the log mixes runs")
            done = {"order": m.group(1), "warmup": int(m.group(2)),
                    "rounds": int(m.group(3)), "lanes": int(m.group(4))}
            continue
        m = ARM.match(line)
        if m:
            if sched is None:
                sys.exit(f"{path}:{n}: `ARM {m.group(1)}` before the schedule line — the "
                         f"lane facts cannot be bound to a term order or a hint state")
            lane = m.group(1)
            if lane in arms:
                sys.exit(f"{path}:{n}: duplicate `ARM {lane}`")
            ids = m.group(10)
            arms[lane] = {
                "regs": int(m.group(2)), "blocks_sm": int(m.group(3)),
                "threads": int(m.group(4)), "grid": int(m.group(5)), "kernel": m.group(6),
                "c": int(m.group(7)), "removals": int(m.group(8)),
                "admitted": int(m.group(9)),
                "ids": [] if ids == "-" else [int(i) for i in ids.split(",")],
            }
            continue
        if line.startswith("ARM "):
            sys.exit(f"{path}:{n}: malformed `ARM` line — the probe rotation emits the "
                     f"frontier grammar, which carries the ordered admitted-id list "
                     f"(`-` when the lane admits nothing)")
        m = SAMPLE.match(line)
        if m:
            order, rnd, lane, ev, fin, kernel = m.groups()
            if sched is None:
                sys.exit(f"{path}:{n}: SAMPLE row before the schedule line")
            if order != sched["order"]:
                sys.exit(f"{path}:{n}: sample declares order={order} inside the "
                         f"order={sched['order']} section — mixed log")
            if lane in rounds[int(rnd)]:
                sys.exit(f"{path}:{n}: duplicate sample for round={rnd} lane={lane} — the "
                         f"log mixes runs; emit one process at a time")
            rounds[int(rnd)][lane] = (float(ev), float(fin), kernel)
            continue
        if line.startswith("SAMPLE "):
            sys.exit(f"{path}:{n}: malformed `SAMPLE` line")

    if sched is None:
        sys.exit(f"{path}: no `{TAG} schedule` line — this is not a carveout-probe log")
    if done is None:
        sys.exit(f"{path}: no `{TAG} done` trailer — the run did not finish, or the log is "
                 f"truncated")
    if (done["order"], done["rounds"], done["warmup"], done["lanes"]) != (
            sched["order"], sched["rounds"], sched["warmup"], sched["lanes"]):
        sys.exit(f"{path}: the schedule line declares order={sched['order']} "
                 f"rounds={sched['rounds']} warmup={sched['warmup']} lanes={sched['lanes']} "
                 f"but the trailer declares order={done['order']} rounds={done['rounds']} "
                 f"warmup={done['warmup']} lanes={done['lanes']} — the log mixes two runs")
    # THE PIN. One preregistered configuration; anything else has no rule to be decided
    # under (see PINNED_* above).
    if (sched["order"] != PINNED_ORDER
            or sched["rounds"] != PINNED_ROUNDS
            or sched["warmup"] != PINNED_WARMUP
            or sched["hint"] not in ("default", PINNED_HINT)):
        sys.exit(f"{path}: the R6 probe is preregistered as `--term-order {PINNED_ORDER}`, "
                 f"`--carveout-hint {PINNED_HINT}` on the hinted processes, "
                 f"`--iterations {PINNED_ROUNDS}` and `--warmup {PINNED_WARMUP}`; this log "
                 f"declares order={sched['order']} rounds={sched['rounds']} "
                 f"warmup={sched['warmup']} carveout-hint={sched['hint']} — a log outside "
                 f"the pinned contract is a different experiment, and its anchors, its "
                 f"signed threshold and the G0-verified hint are not this one's")
    # THE APPLIED HINT. The schedule line says what was asked for; the harness's echo says
    # what `cudaFuncSetAttribute` was actually called with. A schedule line is one text edit
    # away from claiming a hint state the process never ran, so the two must corroborate.
    if sched["hint"] == "default":
        if echo is not None:
            sys.exit(f"{path}: the schedule line declares carveout-hint=default but the "
                     f"process echoed an applied hint of {echo}% — the schedule line and "
                     f"the applied hint disagree; an unhinted process applies none")
    elif echo is None:
        sys.exit(f"{path}: the schedule line declares carveout-hint={sched['hint']} but the "
                 f"log carries no applied-hint echo line — the hint state is not "
                 f"corroborated by the process's own config echo")
    elif str(echo) != sched["hint"]:
        sys.exit(f"{path}: the schedule line declares carveout-hint={sched['hint']} but the "
                 f"process echoed an applied hint of {echo}% — the schedule line and the "
                 f"applied hint disagree")
    if set(arms) != LANES:
        missing = sorted(LANES - set(arms))
        extra = sorted(set(arms) - LANES)
        sys.exit(f"{path}: lane set is not the carveout-probe rotation — missing {missing}, "
                 f"unexpected {extra}")
    if len(arms) != sched["lanes"]:
        sys.exit(f"{path}: {len(arms)} ARM lines but the schedule declares "
                 f"lanes={sched['lanes']} — the log is truncated or mixes builds")
    for lane, f in arms.items():
        if len(f["ids"]) != f["admitted"]:
            sys.exit(f"{path}: lane {lane} declares {f['admitted']} admitted sources but "
                     f"lists {len(f['ids'])} ids")
        if LANE_K[lane] != f["admitted"]:
            sys.exit(f"{path}: lane {lane} admits {f['admitted']} sources but its name "
                     f"claims K = {LANE_K[lane]} — the label and the plan disagree")

    n_rounds, warmup = sched["rounds"], sched["warmup"]
    if len(rounds) != n_rounds:
        sys.exit(f"{path}: {len(rounds)} rounds carry samples, the schedule declares "
                 f"rounds={n_rounds} — truncated log")
    # ROUND IDS. The runner numbers timed rounds `warmup .. warmup + rounds - 1`, so the
    # ids are a consecutive run with a known anchor; counting alone accepts gaps and a
    # renumbered log.
    want_ids = list(range(warmup, warmup + n_rounds))
    if sorted(rounds) != want_ids:
        got = sorted(rounds)
        sys.exit(f"{path}: round ids are {got[:4]}…{got[-1]}, expected the consecutive run "
                 f"{want_ids[0]}…{want_ids[-1]} (warmup {warmup}, rounds {n_rounds}) — "
                 f"gaps, duplicates or a renumbered log, none of which is a paired rotation")
    for r in want_ids:
        if set(rounds[r]) != LANES:
            sys.exit(f"{path}: round {r} carries {sorted(rounds[r])}, expected the 5 probe "
                     f"lanes {sorted(LANES)} — incomplete rounds are not droppable, the "
                     f"contrasts are paired")
        for lane, (_, _, kernel) in rounds[r].items():
            if kernel != arms[lane]["kernel"]:
                sys.exit(f"{path}: round {r} lane {lane} ran `{kernel}` but its ARM line "
                         f"declares `{arms[lane]['kernel']}` — the log describes a kernel "
                         f"the run did not use")
    # ROTATION BALANCE. Samples arrive in execution order, so a lane's position inside a
    # round IS its rotation slot; a lane that keeps a slot carries that slot's clock state
    # into its median, which is exactly what the pairing exists to remove.
    if n_rounds % len(LANE_ORDER) != 0:
        sys.exit(f"{path}: {n_rounds} rounds over {len(LANE_ORDER)} lanes is not balanced — "
                 f"every lane must start equally often")
    per = n_rounds // len(LANE_ORDER)
    slots = defaultdict(int)
    for r in want_ids:
        for slot, lane in enumerate(rounds[r]):
            slots[(lane, slot)] += 1
    for lane in LANE_ORDER:
        for slot in range(len(LANE_ORDER)):
            if slots[(lane, slot)] != per:
                sys.exit(f"{path}: lane {lane} runs at rotation position {slot} in "
                         f"{slots[(lane, slot)]} rounds, expected {per} — the rotation is "
                         f"not balanced")
    # ALIASING GUARD. Two lanes that declare different plans cannot produce bit-identical
    # per-round samples — that is one lane's data under two labels, and it reads as a clean
    # +0.000 rather than as a bug.
    for i, a in enumerate(LANE_ORDER):
        for b in LANE_ORDER[i + 1:]:
            if all(rounds[r][a][:2] == rounds[r][b][:2] for r in want_ids):
                sys.exit(f"{path}: lanes {a} and {b} carry BIT-IDENTICAL samples in every "
                         f"round — the log aliases one lane's data onto another")

    tot = {a: [rounds[r][a][0] + rounds[r][a][1] for r in want_ids] for a in LANE_ORDER}
    return {
        "path": path, "order": sched["order"], "rounds": n_rounds, "warmup": warmup,
        "hint": sched["hint"], "arms": arms, "keys": want_ids, "tot": tot,
        "med": {a: median(tot[a]) for a in LANE_ORDER},
    }


def delta(p, lane):
    """The paired per-round contrast `lane - hot16@128` on eval+finalize, with its signed
    verdict — the P1 quantity."""
    d = [x - y for x, y in zip(p["tot"][lane], p["tot"][HOT])]
    verdict, med, on = signed(d, p["rounds"])
    return {"med": med, "on": on, "n": len(d), "verdict": verdict}


def session(paths):
    """The four processes plus the cross-log gates: one experiment, one rotation, one term
    order, and the ABBA hint sequence the positional argument order claims."""
    if len(paths) != 4:
        sys.exit(f"r6_probe_table expects exactly 4 logs in session order "
                 f"(off1 on1 on2 off2); got {len(paths)} — the ABBA pairing is positional, "
                 f"so a short or long set has no defined pairs")
    procs = [load(p) for p in paths]
    head = procs[0]
    # `order`, `rounds` and `warmup` need no cross-log identity check: the pin in `load`
    # already forces all four to the one preregistered configuration. The lane PLANS do —
    # they are not pinned to literals here (C and the admitted ids ride the ARM lines), so
    # this is where a set assembled from two different builds or trace sizes is caught.
    for tag, p in zip(PROCS[1:], procs[1:]):
        for lane in LANE_ORDER:
            if p["arms"][lane] != head["arms"][lane]:
                sys.exit(f"{p['path']} ({tag}): lane {lane} declares a different plan than "
                         f"{head['path']} (off1) — the hint is host-only, so every lane "
                         f"fact (kernel, occupancy, C, removals, admitted ids) must be "
                         f"identical across the four processes")
    hints = [p["hint"] for p in procs]
    n = hints[1]
    bad = (hints[0] != "default" or hints[3] != "default"
           or hints[1] == "default" or hints[1] != hints[2])
    if bad:
        sys.exit(f"the hint sequence is {hints}, expected [default, {PINNED_HINT}, "
                 f"{PINNED_HINT}, default] with the SAME N in both hinted processes — the "
                 f"session is ABBA by hint state and the logs are positional "
                 f"(off1 on1 on2 off2)")
    return procs, n


def lane_facts(p):
    print("### Lane facts — from the `ARM` lines, identical in all four processes\n")
    print("| lane | kernel | regs | blocks/SM | threads | grid | C | removals | admitted |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    for lane in LANE_ORDER:
        f = p["arms"][lane]
        print(f"| `{lane}` | `{f['kernel']}` | {f['regs']} | {f['blocks_sm']} | "
              f"{f['threads']} | {f['grid']} | {f['c']} | {f['removals']} | "
              f"{f['admitted']} |")


def medians_table(procs):
    print("\n### Per-process lane medians — `eval + finalize`, ms\n")
    print("| process | hint | log | " + " | ".join(f"`{a}`" for a in LANE_ORDER) + " |")
    print("| --- | --- | --- | " + " | ".join("---" for _ in LANE_ORDER) + " |")
    for tag, p in zip(PROCS, procs):
        cells = " | ".join(f"{p['med'][a]:.3f}" for a in LANE_ORDER)
        print(f"| {tag} | {p['hint']} | `{p['path']}` | {cells} |")


def delta_table(procs, deltas):
    print(f"\n### Paired deltas vs `{HOT}` — per round on `eval + finalize`\n")
    print(f"Signed rule (R5's, verbatim): WIN = median < 0 AND at least "
          f"{threshold(procs[0]['rounds'])}/{procs[0]['rounds']} rounds negative; LOSS is "
          f"the mirror; anything else is a WASH.\n")
    print("| process | hint | lane | C | median Δ (ms) | on-sign | verdict |")
    print("| --- | --- | --- | --- | --- | --- | --- |")
    for tag, p in zip(PROCS, procs):
        for lane in KS:
            d = deltas[tag][lane]
            print(f"| {tag} | {p['hint']} | `{lane}` | {p['arms'][lane]['c']} | "
                  f"**{d['med']:+.3f}** | {d['on']}/{d['n']} | **{d['verdict']}** |")


def p1(procs, deltas):
    """The preregistered P1 branch. `stable` gates everything: both OFF processes must
    reproduce R5's registered first-loser relation (k24 loses to hot16) or the probe has no
    verdict to give."""
    print("\n### P1 — does the admission frontier move under the hint?\n")
    off_k24 = [deltas[PROCS[i]]["k24@128"] for i in OFFS]
    stable = all(d["verdict"] == "loss" for d in off_k24)
    print(f"**Stability precondition** (spec, codex amendment 5: both OFF processes must "
          f"reproduce R5's registered first-loser relation, k24 losing to hot16): off1"
          f" {off_k24[0]['med']:+.3f} ms **{off_k24[0]['verdict']}**, off2 "
          f"{off_k24[1]['med']:+.3f} ms **{off_k24[1]['verdict']}**.")
    if not stable:
        print("\n> **PROBE UNSTABLE — off processes do not reproduce the R5 frontier; no "
              "verdict**\n")
        print("The tables above stand as measurements; P1 and P2 are SUPPRESSED — every "
              "one of their rules is defined against an off baseline this session did not "
              "reproduce.")
        return None
    # (a) — a WIN in BOTH hinted processes. A win in exactly one is a MIXED note and does
    # NOT satisfy (a): the rule is registered over both hinted processes.
    winners, mixed = [], []
    for lane in KS:
        won = [t for t in (PROCS[i] for i in ONS) if deltas[t][lane]["verdict"] == "win"]
        if len(won) == 2:
            winners.append(lane)
        elif won:
            mixed.append((lane, won[0]))
    if mixed:
        print()
    for lane, where in mixed:
        other = next(t for t in (PROCS[i] for i in ONS) if t != where)
        d = deltas[other][lane]
        print(f"- **MIXED** — `{lane}` wins over `{HOT}` in {where} only "
              f"({d['med']:+.3f} ms, {d['verdict']}, in {other}); a single-process win does "
              f"NOT satisfy (a).")
    if winners:
        best = max(winners, key=lambda lane: procs[ONS[0]]["arms"][lane]["c"])
        c = procs[ONS[0]]["arms"][best]["c"]
        print(f"\n⇒ **FRONTIER MOVED** (P1 a) — "
              + ", ".join(f"`{lane}`" for lane in winners)
              + f" win over `{HOT}` in BOTH hinted processes.")
        print(f"- frontier position = **C = {c}** (`{best}`), the largest C among the "
              f"winners; C is read from the `ARM` lines.")
        if "k40@128" in winners:
            print(f"- `k40@128` is the top lane of the probe rotation and wins in both "
                  f"hinted processes, so the moved frontier is reported "
                  f"**right-censored at k40** (spec, codex amendment 3).")
        return winners
    # (b) — half-shrink, PAIRWISE against the ADJACENT off process (codex amendment 5).
    print("\n**(b) half-shrink of Δk24, pairwise against the ADJACENT off process** "
          "(spec, codex amendment 5):\n")
    print("| pair | median Δk24 (off) | median Δk24 (on) | half of off | ≤ half? |")
    print("| --- | --- | --- | --- | --- |")
    shrunk = True
    for label, off_i, on_i in PAIRS:
        d_off = deltas[PROCS[off_i]]["k24@128"]["med"]
        d_on = deltas[PROCS[on_i]]["k24@128"]["med"]
        ok = d_on <= HALF * d_off
        shrunk = shrunk and ok
        print(f"| {label} | {d_off:+.3f} | {d_on:+.3f} | {HALF * d_off:+.3f} | "
              f"**{'yes' if ok else 'no'}** |")
    if shrunk:
        print("\n⇒ **CAPACITY-PRICED CONFIRMED — the knee is carveout-sensitive** (P1 b): "
              "no lane wins, but Δk24 shrinks to at most half the adjacent off process's "
              "value in BOTH pairs.")
    else:
        print("\n⇒ **carveout is not the binding capacity term** (P1 c): no lane wins in "
              "both hinted processes, and Δk24 does not shrink to half the adjacent off "
              "process's value in both pairs. Finding recorded, probe closed.")
    return []


def p2(procs):
    """hot16 under the hint, bridged through the never-hinted control@256, over the two
    ADJACENT ABBA pairs. A raw hot16(on) − hot16(off) would carry the whole session drift
    between the two processes; the bridge removes what the shared anchor also saw."""
    print("\n### P2 — does hot16's absolute time improve under the hint?\n")
    print(f"Flank gate per pair: |median `{CTL}`(off) − median `{CTL}`(on)| ≤ "
          f"{FLANK_MS:.2f} ms, else that pair is `unstable`. "
          f"δ = (H_on − C_on) − (H_off − C_off).\n")
    print("| pair | C(off) | C(on) | flank ΔC | stable | H(off) | H(on) | δ (ms) |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- |")
    stable_all, negative_all = True, True
    for label, off_i, on_i in PAIRS:
        off, on = procs[off_i], procs[on_i]
        c_off, c_on = off["med"][CTL], on["med"][CTL]
        h_off, h_on = off["med"][HOT], on["med"][HOT]
        flank = abs(c_off - c_on)
        stable = flank <= FLANK_MS
        d = (h_on - c_on) - (h_off - c_off)
        stable_all = stable_all and stable
        negative_all = negative_all and d < 0
        print(f"| {label} | {c_off:.3f} | {c_on:.3f} | {flank:.3f} | "
              f"**{'stable' if stable else 'unstable'}** | {h_off:.3f} | {h_on:.3f} | "
              f"**{d:+.3f}** |")
    if stable_all and negative_all:
        print(f"\n⇒ **hot16 improves under the hint (control-bridged, in-rotation)** — both "
              f"adjacent pairs are stable and both δ are negative.")
    elif not stable_all:
        print(f"\n⇒ **P2 verdict withheld** — a pair failed the flank gate, so its bridged "
              f"δ carries a session shift the anchor also saw. The improvement claim needs "
              f"BOTH pairs stable.")
    else:
        print(f"\n⇒ **no P2 improvement** — both pairs are stable but the two δ are not "
              f"both negative.")
    print("\nlocality/shipping order only; NOT comparable to the R5 bar layers.")


def sanity(procs):
    """spec sanity: control@256 in every process, and hot16 in the OFF processes only,
    within ±2 % of R4's frozen in-rotation medians for this term order. The banner is
    NON-FATAL — it scopes the absolutes, it does not invalidate the paired contrasts."""
    print("\n### Sanity anchors — ±2 % of R4's frozen in-rotation medians\n")
    print("| process | hint | lane | this session | anchor | delta | verdict |")
    print("| --- | --- | --- | --- | --- | --- | --- |")
    out = False
    for i, (tag, p) in enumerate(zip(PROCS, procs)):
        anchors = [(CTL, ANCHORS[p["order"]][0])]
        if i in OFFS:
            anchors.append((HOT, ANCHORS[p["order"]][1]))
        for lane, target in anchors:
            got = p["med"][lane]
            rel = (got - target) / target
            ok = abs(rel) <= SANITY_TOL
            out = out or not ok
            print(f"| {tag} | {p['hint']} | `{lane}` | {got:.3f} | {target:.3f} | "
                  f"{100.0 * rel:+.2f} % | **{'IN' if ok else 'OUT'}** |")
    print(f"\nThe hot16 anchor applies to the OFF processes only — hot16 under the hint is "
          f"the quantity P2 measures, so it is not also its own anchor.")
    if out:
        print("\n> **SANITY: anchor out of band — absolutes are session-scoped**\n")
        print("The paired per-round contrasts above stand; the raw medians are read as "
              "this session's, not as cross-session absolutes.")


def manifest(procs, winners, n_hint):
    """Emitted ONLY when P1 (a) fires: the follow-up Full Picture captures that separate
    'the carveout changed timing' from 'L1 capacity caused it' (spec, codex amendment 6).
    Each winning lane and hot16, under both hint states, order-tagged."""
    print("\n### ncu capture manifest\n")
    print(f"P1 (a) fired, so each winning lane and `{HOT}` is captured under BOTH hint "
          f"states — the hinted arm is what moved, the unhinted one is its own control, "
          f"and the pair is what distinguishes a timing change from an L1-capacity cause. "
          f"Consumed as AUTHORITATIVE; not reconstructed by hand.\n")
    order = procs[0]["order"]
    print("```")
    for lane in list(winners) + [HOT]:
        print(f"NCU-CAPTURE lane={lane} hint=on carveout-hint={n_hint} order={order}")
        print(f"NCU-CAPTURE lane={lane} hint=off carveout-hint=default order={order}")
    print("```")


def main():
    if len(sys.argv) >= 2 and sys.argv[1] in ("-h", "--help"):
        print(__doc__)
        return
    procs, n_hint = session(sys.argv[1:])
    head = procs[0]
    print(f"## v3 R6 — carveout probe, `--term-order {head['order']}`\n")
    print(f"Four processes, ABBA by hint state (off, on, on, off) at "
          f"`--carveout-hint {n_hint}`, {head['rounds']} paired rounds x "
          f"{len(LANE_ORDER)} lanes each, warmup {head['warmup']}. Every figure below is "
          f"EMITTED: this script is the single authority for the derived decisions, and "
          f"each decision line names the preregistered rule it implements. The metric is "
          f"`eval + finalize` per round; the hint state of every process is read from its "
          f"own schedule line, never from a filename.\n")
    lane_facts(head)
    medians_table(procs)
    deltas = {tag: {lane: delta(p, lane) for lane in KS}
              for tag, p in zip(PROCS, procs)}
    delta_table(procs, deltas)
    winners = p1(procs, deltas)
    if winners is not None:
        p2(procs)
    sanity(procs)
    if winners:
        manifest(procs, winners, n_hint)


if __name__ == "__main__":
    main()
