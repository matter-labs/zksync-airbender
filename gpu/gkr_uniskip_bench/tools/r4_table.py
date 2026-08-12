#!/usr/bin/env python3
"""Emit the v3 R4 factorial table from a `--cache-factorial` run log, the v3 R5
admission-frontier tables from `--frontier-factorial` / `--frontier-extension` logs, and the
v3 R8 admission-interior tables from a `--frontier-interior` session pair.

R5 NOTE. For a frontier log this script is THE SINGLE AUTHORITY for every derived
decision — the three named curves, the signed per-lane statuses, C*, the extension
trigger, the broad-knee verdict, first losers, right-censoring, the headline selector,
the sanity verdict, the R4 bridges and the ncu capture manifest. Nothing decision-bearing
is computed by hand or in the record; each decision line names the preregistered rule
(spec `.agents/specs/2026-08-10-gkr-uniskip-v3-r5-hotk-frontier-design.md` 2.3) it
implements. The mode is chosen by the LOG's own schedule keyword, never by a flag, so an
R4 log and a frontier log cannot be summarized under each other's rules.

Everything is PAIRED per round: the runner executes all eleven lanes inside one round, in a
cyclic rotation, so a round's lanes share whatever clock state that round had. Taking the
contrast round-by-round and then summarizing removes the ~1 %/session drift that would
otherwise swamp effects of this size.

The lane SET is pinned here (`EXPECTED_LANES`) as an integrity gate: a log carrying a
different rotation is a different experiment, and it is rejected rather than partially
summarized. Every per-lane FACT is data-driven from the log's `ARM` lines, which the runner
emits from Rust — registers, blocks/SM, block size, grid, kernel, C, removals, admitted-set
size. No occupancy number, kernel name or removal count is written here; R3's emitter held
all three, and the spec called that out as the thing to fix.

`eval` and `finalize` are summarized SEPARATELY. The 128 lanes run twice the grid, so
finalize reduces twice the partials; summing the two stages would fold a real block-size
effect into the arm comparison.

Every contrast NAMES its baseline. At 128 the cache-vs-control baseline is `control_lb@128`,
the bounded no-cache body, because the cached 128 lanes are bounded too — comparing them to
the unbounded `control@128` would put the launch bound's own cost inside the cache result.

Removals per lane ride the log's `ARM` line, which Rust fills from the arm's own planned
`CacheCounts` — this script holds no oracle constant, so a census change cannot silently
invalidate a slope (and the runner rejects the census knobs anyway).

R8 NOTE. The interior sweep gets a DEDICATED decision path (plan amendment A2), not a flag
threaded through the R5 one: it measures ONE contiguous admission axis and is decided by
adjacent steps and cumulative contrasts under one signed rule, never by R5's curves, C\\*,
extension trigger, broad knee or both-orders headline selector.

Usage:
    python3 gpu/gkr_uniskip_bench/tools/r4_table.py /tmp/cache.log [--order locality]
    python3 gpu/gkr_uniskip_bench/tools/r4_table.py primary.log [extension.log ...]
    python3 gpu/gkr_uniskip_bench/tools/r4_table.py interior-locality.log interior-census.log
"""

import argparse
import re
import sys
from collections import defaultdict
from statistics import median

SAMPLE = re.compile(r"^SAMPLE (\S+) (\d+) (\S+) ([\d.]+) ([\d.]+) (\S+)$")
ARM = re.compile(r"^ARM (\S+) (\d+) (\d+) (\d+) (\d+) (\S+) (\d+) (\d+) (\d+)$")
# The frontier ARM line is the R4 one PLUS the ordered admitted-id list: counts alone
# cannot detect a reversal among equal-ref, equal-class sources, so the LIST is what the
# oracle gate reads. `-` is the empty prefix (control, cache0).
ARM_IDS = re.compile(r"^ARM (\S+) (\d+) (\d+) (\d+) (\d+) (\S+) (\d+) (\d+) (\d+) (\S+)$")
R4 = "CACHE-FACTORIAL"
SCHED = re.compile(r"^(\S+) schedule order=(\S+) lanes=(\d+) rounds=(\d+) warmup=(\d+)$")
DONE = re.compile(r"^(\S+) done order=(\S+) warmup=(\d+) rounds=(\d+) lanes=(\d+)$")

# The eleven lanes the primary rotation must carry. A log with a different set is a
# different experiment and is rejected rather than partially summarized.
EXPECTED_LANES = {
    "control@256", "cache0@256", "hot4@256", "hot16@256", "allrepeat@256",
    "control@128", "control_lb@128", "cache0@128", "hot4@128", "hot16@128", "allrepeat@128",
}

# --- v3 R5 frontier ---------------------------------------------------------------
#
# One row per rotation: the pinned lane set, the PREREGISTERED round count, and the
# preregistered signed threshold that goes with it (spec 2.3 — literals 90/100 and
# 94/104, never a ratio recomputed from the log).
FRONTIER = {
    "FRONTIER-FACTORIAL": {
        "lanes": {"k24@128", "k32@128", "k40@128", "k45@128", "k46@128", "k48@128",
                  "hot16@128", "cache0@128", "control_lb@128", "control@256"},
        "rounds": 100,
        "threshold": 90,
        "what": "primary",
    },
    "FRONTIER-EXTENSION": {
        "lanes": {"k48@128", "k49@128", "k50@128", "k51@128",
                  "hot16@128", "cache0@128", "control_lb@128", "control@256"},
        "rounds": 104,
        "threshold": 94,
        "what": "extension",
    },
}

# The controller-derived admission ordering, all 55 entries, from
# `.agents/sdd/2026-08-10-v3-r5/oracle-derivation.txt` (identical under both term orders).
# Every lane's admitted-id list must be its first-K prefix, IN THIS ORDER. This is the one
# oracle literal the emitter carries: an identity, not a count or a timing.
ORACLE_ORDER = (
    [0, 1, 2, 3, 4, 5] + [48, 49, 50, 51] + list(range(6, 41))
    + [52, 53, 54, 55, 56, 57, 58] + [41, 42, 43]
)

# The K a named lane claims. Cross-checked against the length of its admitted-id list, so a
# mislabelled lane is caught as well as a reordered one.
LANE_K = {"hot16@128": 16, "cache0@128": 0, "control_lb@128": 0, "control@256": 0}
LANE_K.update({f"k{k}@128": k for k in (24, 32, 40, 45, 46, 48, 49, 50, 51)})

# R4's frozen in-rotation anchors, by order: (control@256, hot16@128) eval+finalize medians
# (spec 2.3 sanity anchoring), and R2c, the v3 R2 shipping baseline the bridges ride on.
ANCHORS = {"census": (16.545, 15.129), "locality": (16.624, 14.836)}
R2C = {"census": 16.453, "locality": 16.283}
BAR = 14.61
SANITY_TOL = 0.02
KNEE_MS = 0.10

# --- v3 R8 interior ---------------------------------------------------------------
#
# The interior rung sweeps the seven admission points R5 never sampled, between the R5
# optimum (hot16 = K16, C = 28) and R5's first loser (k24, C = 36), on the same frozen cached
# body. Its lane set, round shape and signed threshold are PREREGISTERED literals: the
# threshold is ceil(0.9 x 96) = 87 (plan amendment A1), so a log at another round count has
# no rule to be judged against.
R8 = "FRONTIER-INTERIOR"

# The K axis in admission order: the incumbent, the seven interior points, and R5's boundary
# lane, which rides along so hot16 -> ... -> k24 is paired IN SESSION rather than across one.
INTERIOR_AXIS = ["hot16@128"] + [f"k{k}@128" for k in range(17, 25)]
# The lanes that admit nothing. `hot16@128` is an anchor as well as the axis bottom, so the
# anchor list below is not a partition of the rotation.
INTERIOR_BASES = ["cache0@128", "control_lb@128", "control@256"]
INTERIOR_ANCHORS = ("control@256", "control_lb@128", "cache0@128", "hot16@128")
INTERIOR = {
    "lanes": set(INTERIOR_AXIS) | set(INTERIOR_BASES),
    "rounds": 96,
    "warmup": 12,
    "threshold": 87,
}

# THE TRACE PIN (amendment A5). The trace size appears in no log line, but the grid does: at
# `--log-trace 24` it is the trace's row count over each lane's row tile, a fact of the build
# and the trace and of nothing else. A whole session recorded at another trace is internally
# consistent, so this pin is the only thing that can see it.
INTERIOR_TRACE = 24
INTERIOR_GRID = {"control@256": 32768}
INTERIOR_GRID.update({lane: 65536 for lane in INTERIOR_AXIS + ["cache0@128",
                                                              "control_lb@128"]})

# The interior lanes' K, alongside R5's above: a lane whose label and plan disagree is caught
# in both paths by the same identity.
LANE_K.update({f"k{k}@128": k for k in range(17, 24)})

# The R5 PRIMARY session's own `eval + finalize` medians per order, from that rung's emitter
# output (`.agents/sdd/2026-08-10-v3-r5/task3-frontier.md`), as (control@256, hot16@128).
# REPORT-ONLY context (amendment A6) — the HARD band stays the R4-frozen `ANCHORS` above.
R5_SESSION = {"census": (16.666, 15.120), "locality": (16.567, 14.717)}

# The flank rule (amendment A6), computed here rather than by hand: block medians of an anchor
# lane's FIRST and LAST full cycle against max(0.05 ms, 0.5 % of that lane's session median).
FLANK_MS = 0.05
FLANK_REL = 0.005

VERDICT = {"win": "WIN", "lose": "LOSS", "wash": "WASH"}

# Every rotation keyword this emitter knows. A schedule or trailer line is bound to a section
# only for these, so a foreign grammar cannot be summarized under one of these rules.
KNOWN = {R4} | set(FRONTIER) | {R8}


def parse(paths, where):
    runs = defaultdict(lambda: defaultdict(dict))
    arms, done, sched = defaultdict(dict), {}, {}
    for path in paths:
        section = None
        for n, line in enumerate(open(path), 1):
            line = line.strip()
            m = SCHED.match(line)
            if m and m.group(1) in KNOWN:
                key = (m.group(1), m.group(2))
                if key in sched:
                    sys.exit(f"{path}:{n}: order={m.group(2)} starts twice — the log mixes runs")
                section = key
                sched[key] = (int(m.group(3)), int(m.group(4)), int(m.group(5)))
                continue
            m = ARM_IDS.match(line) or ARM.match(line)
            if m:
                if section is None:
                    sys.exit(f"{path}:{n}: `ARM {m.group(1)}` before any schedule line — the "
                             f"lane facts cannot be bound to a term order")
                if m.group(1) in arms[section]:
                    sys.exit(f"{path}:{n}: duplicate `ARM {m.group(1)}` for order={section[1]}")
                ids = m.group(10) if m.lastindex == 10 else None
                if (ids is None) != (section[0] == R4):
                    sys.exit(f"{path}:{n}: `ARM {m.group(1)}` carries "
                             f"{'an' if ids is not None else 'no'} admitted-id list under "
                             f"{section[0]} — the two grammars are not interchangeable")
                arms[section][m.group(1)] = {
                    "regs": int(m.group(2)), "blocks_sm": int(m.group(3)),
                    "threads": int(m.group(4)), "grid": int(m.group(5)), "kernel": m.group(6),
                    "c": int(m.group(7)), "removals": int(m.group(8)),
                    "admitted": int(m.group(9)),
                    "ids": [] if ids in (None, "-") else [int(i) for i in ids.split(",")],
                }
                continue
            m = SAMPLE.match(line)
            if m:
                order, rnd, lane, ev, fin, kernel = m.groups()
                if section is not None and order != section[1]:
                    sys.exit(f"{path}:{n}: sample declares order={order} inside the "
                             f"{section[0]} order={section[1]} section — mixed log")
                # Bucketed per ROTATION, so the primary and the extension may legitimately
                # reuse a round id. A row ahead of every schedule line is parked under the
                # `None` tag and collides with the section that later claims its order, so
                # a duplicate is still caught wherever in the file it sits.
                skey = (section[0] if section else None, order)
                bucket = runs[skey][int(rnd)]
                stray = runs.get((None, order), {}).get(int(rnd), {}) if section else {}
                if lane in bucket or lane in stray:
                    sys.exit(f"{path}:{n}: duplicate sample for order={order} round={rnd} "
                             f"lane={lane} — the log mixes runs; emit one session at a time")
                bucket[lane] = (float(ev), float(fin), kernel)
                continue
            m = DONE.match(line)
            if m and m.group(1) in KNOWN:
                key = (m.group(1), m.group(2))
                if key in done:
                    sys.exit(f"{path}:{n}: order={m.group(2)} completes twice — mixed log")
                done[key] = (int(m.group(3)), int(m.group(4)), int(m.group(5)))
    # Adopt the rows that preceded every schedule line into the rotation that declared
    # their order. An order no rotation declared is an error rather than an orphan bucket
    # nothing ever summarizes.
    declared = defaultdict(set)
    for tag, order in set(sched) | set(done):
        declared[order].add(tag)
    for key in [k for k in runs if k[0] is None]:
        order = key[1]
        here = declared.get(order, set())
        if len(here) != 1:
            sys.exit(f"{where}: SAMPLE rows for order={order} precede every schedule line "
                     f"and {len(here)} rotations declare that order — they cannot be bound "
                     f"to one")
        tag = next(iter(here))
        for rnd, bucket in runs.pop(key).items():
            runs[(tag, order)][rnd].update(bucket)
    return runs, arms, done, sched


def iqr(xs):
    s = sorted(xs)
    return s[len(s) // 4], s[(3 * len(s)) // 4]


def contrast(rounds, order_keys, a, b, field):
    d = [rounds[r][a][field] - rounds[r][b][field] for r in order_keys]
    med = median(d)
    lo, hi = iqr(d)
    sign = sum(1 for x in d if (x > 0) == (med > 0) and x != 0)
    return med, lo, hi, sign, len(d)


def emit(order, rounds, arms, trailer, sched):
    if not arms:
        sys.exit(f"{order}: no ARM lines for this order — old-format or truncated log")
    if trailer is None:
        sys.exit(f"{order}: no `CACHE-FACTORIAL done order={order} …` trailer — the run did "
                 f"not finish, or the log is truncated")
    if not rounds:
        sys.exit(f"{order}: the log declares this order ({sched[1]} rounds x {sched[0]} lanes) "
                 f"but carries no SAMPLE rows — a declared order is emitted or it is an "
                 f"error, never silently skipped")
    lanes = list(arms)
    if set(lanes) != EXPECTED_LANES:
        missing = sorted(EXPECTED_LANES - set(lanes))
        extra = sorted(set(lanes) - EXPECTED_LANES)
        sys.exit(f"{order}: lane set is not the primary rotation — missing {missing}, "
                 f"unexpected {extra}")
    if len(lanes) != trailer[2] or len(lanes) != sched[0]:
        sys.exit(f"{order}: {len(lanes)} ARM lines but the trailer declares {trailer[2]} "
                 f"lanes — the log is truncated or mixes builds")
    for r in sorted(rounds):
        if set(rounds[r]) != set(lanes):
            sys.exit(f"{order}: round {r} carries {sorted(rounds[r])}, expected {lanes} — "
                     f"incomplete rounds are not droppable, the contrasts are paired")
        for lane, (_, _, kernel) in rounds[r].items():
            if kernel != arms[lane]["kernel"]:
                sys.exit(f"{order}: round {r} lane {lane} ran `{kernel}` but its ARM line "
                         f"declares `{arms[lane]['kernel']}` — the log describes a kernel "
                         f"the run did not use")
    if len(rounds) % len(lanes) != 0:
        sys.exit(f"{order}: {len(rounds)} rounds over {len(lanes)} lanes is not balanced — "
                 f"every lane must start equally often")
    if len(rounds) != trailer[1]:
        sys.exit(f"{order}: {len(rounds)} rounds in the log, trailer claims rounds="
                 f"{trailer[1]} — truncated log")
    if (sched[1], sched[2]) != (trailer[1], trailer[0]):
        sys.exit(f"{order}: the schedule line declares rounds={sched[1]} warmup={sched[2]} "
                 f"but the trailer declares rounds={trailer[1]} warmup={trailer[0]} — the "
                 f"log mixes two runs, or the header does not describe what ran")
    # ROUND IDS. The runner numbers timed rounds `warmup .. warmup + rounds - 1`, so the ids
    # are a consecutive run with a known anchor. Counting rounds alone accepts gaps,
    # duplicates and a renumbered log (0, 11, 22, … passes `rounds % lanes == 0`).
    want_ids = list(range(trailer[0], trailer[0] + trailer[1]))
    if sorted(rounds) != want_ids:
        got = sorted(rounds)
        sys.exit(f"{order}: round ids are {got[:4]}…{got[-1]}, expected the consecutive run "
                 f"{want_ids[0]}…{want_ids[-1]} (warmup {trailer[0]}, rounds {trailer[1]}) — "
                 f"gaps, duplicates or a renumbered log, none of which is a paired rotation")
    # ROTATION BALANCE. Samples arrive in execution order, so a lane's position inside a
    # round IS its rotation slot. Every lane must take every slot equally often — that is
    # what makes the contrast paired; a lane that keeps a slot carries that slot's clock
    # state into its median. `rounds % lanes == 0` only counts rounds.
    per = len(rounds) // len(lanes)
    slots = defaultdict(int)
    for r in sorted(rounds):
        for slot, lane in enumerate(rounds[r]):
            slots[(lane, slot)] += 1
    for lane in lanes:
        for slot in range(len(lanes)):
            if slots[(lane, slot)] != per:
                sys.exit(f"{order}: lane {lane} runs at rotation position {slot} in "
                         f"{slots[(lane, slot)]} rounds, expected {per} — the rotation is "
                         f"not balanced, so a lane keeps a position and its median carries "
                         f"that position's clock state")
    keys = sorted(rounds)
    EV, FIN = 0, 1

    # ALIASING GUARD. Two lanes that declare different plans (C, removals, admitted) cannot
    # produce bit-identical per-round samples — that is one lane's data under two labels,
    # and it reads as a clean +0.000 rather than as a bug. R3 lost a round to exactly this.
    for i, a in enumerate(lanes):
        for b in lanes[i + 1:]:
            if (arms[a]["c"], arms[a]["removals"], arms[a]["admitted"]) == \
               (arms[b]["c"], arms[b]["removals"], arms[b]["admitted"]) and \
               arms[a]["threads"] == arms[b]["threads"] and arms[a]["removals"]:
                sys.exit(f"{order}: lanes {a} and {b} declare the SAME plan at the same "
                         f"block size — one experiment under two labels")
            if all(rounds[r][a][:2] == rounds[r][b][:2] for r in keys):
                sys.exit(f"{order}: lanes {a} and {b} carry BIT-IDENTICAL samples in every "
                         f"round — the log aliases one lane's data onto another")

    print(f"#### `--term-order {order}` — {len(keys)} paired rounds, {len(lanes)} lanes\n")
    print("| lane | kernel | regs | blocks/SM | threads | grid | median `eval` | median `finalize` | eval min | eval max |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    med = {}
    for a in lanes:
        ev = [rounds[r][a][EV] for r in keys]
        fin = [rounds[r][a][FIN] for r in keys]
        med[a] = (median(ev), median(fin))
        f = arms[a]
        print(f"| `{a}` | `{f['kernel']}` | {f['regs']} | {f['blocks_sm']} | {f['threads']} | "
              f"{f['grid']} | **{med[a][0]:.3f}** | {med[a][1]:.3f} | {min(ev):.3f} | {max(ev):.3f} |")

    print("\n**`eval` and `finalize` are separate**: the 128 lanes run twice the grid, so "
          "finalize reduces twice the partials. A summed figure would carry that into the "
          "arm comparison.\n")

    # Contrast rows, each naming its baseline explicitly.
    rows = []
    for size, ctl_bound in [("256", "control@256"), ("128", "control_lb@128")]:
        cache0 = f"cache0@{size}"
        if cache0 not in arms:
            continue
        rows.append((cache0, ctl_bound, f"machinery at {size}: the frame, the walk, no removals"))
        for arm in ("hot4", "hot16", "allrepeat"):
            lane = f"{arm}@{size}"
            if lane in arms:
                rows.append((lane, cache0,
                             f"removals alone at {size} ({arms[lane]['removals']} productions)"))
                why = ("net at 128, vs the BOUND-MATCHED control"
                       if size == "128" else "net at 256 (no bound on either side)")
                rows.append((lane, ctl_bound, why))
    if "control_lb@128" in arms and "control@128" in arms:
        rows.append(("control_lb@128", "control@128", "the launch bound's OWN cost, no cache"))
    for arm in ("hot4", "hot16", "allrepeat"):
        if f"{arm}@128" in arms and "control@256" in arms:
            rows.append((f"{arm}@128", "control@256", "the decision contrast: candidate@128 vs SHIPPING"))

    print("| contrast | baseline | median eval (ms) | IQR | % of baseline | on-sign | occupancy | what it isolates |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- |")
    for a, b, what in rows:
        m, lo, hi, sign, n = contrast(rounds, keys, a, b, EV)
        pct = 100.0 * m / med[b][0]
        occ = "same class" if arms[a]["blocks_sm"] == arms[b]["blocks_sm"] else \
              f"**{arms[a]['blocks_sm']} v {arms[b]['blocks_sm']} blocks/SM — NOT occupancy-neutral**"
        print(f"| `{a}` − `{b}` | `{b}` | **{m:+.3f}** | {lo:+.3f} … {hi:+.3f} | {pct:+.2f} % | "
              f"{sign}/{n} | {occ} | {what} |")

    # Slopes per removed production: net (vs the size's bound-matched control) and
    # machinery-corrected (vs that size's cache0).
    print("\n**Slopes per removed production** (oracle removals; none of these is \"the\" cost):\n")
    print("| lane | removals | net µs/production | machinery-corrected µs/production |")
    print("| --- | --- | --- | --- |")
    for size, base in [("256", "control@256"), ("128", "control_lb@128")]:
        for arm in ("hot4", "hot16", "allrepeat"):
            lane = f"{arm}@{size}"
            if lane not in arms or base not in arms:
                continue
            rm = arms[lane]["removals"]
            net = 1000.0 * contrast(rounds, keys, lane, base, EV)[0] / rm
            mach = 1000.0 * contrast(rounds, keys, lane, f"cache0@{size}", EV)[0] / rm
            print(f"| `{lane}` | {rm} | {net:+.2f} | {mach:+.2f} |")

    # The decision contrast on eval+finalize. finalize is exactly what differs across the
    # sizes (the 128 grid doubles the partial count), so the cross-size decision cannot be
    # taken on `eval` alone.
    print("\n**Decision contrast on `eval + finalize`** — the cross-size row where finalize "
          "is load-bearing:\n")
    print("| contrast | baseline | median eval+fin (ms) | IQR | % of baseline | on-sign |")
    print("| --- | --- | --- | --- | --- | --- |")
    for arm in ("hot4", "hot16", "allrepeat"):
        a, b = f"{arm}@128", "control@256"
        if a not in arms or b not in arms:
            continue
        d = [(rounds[r][a][EV] + rounds[r][a][FIN]) - (rounds[r][b][EV] + rounds[r][b][FIN])
             for r in keys]
        m = median(d)
        lo, hi = iqr(d)
        sign = sum(1 for x in d if (x > 0) == (m > 0) and x != 0)
        # The denominator is the median of the per-round SUM, not the sum of the two stage
        # medians: the median is not additive, and the numerator is already a per-round sum.
        base = median(rounds[r][b][EV] + rounds[r][b][FIN] for r in keys)
        print(f"| `{a}` − `{b}` | `{b}` | **{m:+.3f}** | {lo:+.3f} … {hi:+.3f} | "
              f"{100.0 * m / base:+.2f} % | {sign}/{len(d)} |")

    if all(k in arms for k in ("allrepeat@128", "allrepeat@256", "control@256", "control_lb@128")):
        inter = [
            (rounds[r]["allrepeat@128"][EV] - rounds[r]["control_lb@128"][EV])
            - (rounds[r]["allrepeat@256"][EV] - rounds[r]["control@256"][EV])
            for r in keys
        ]
        lo, hi = iqr(inter)
        print(f"\n**Block-size interaction** (allrepeat net at 128 − at 256) = "
              f"**{median(inter):+.3f} ms** (IQR {lo:+.3f} … {hi:+.3f}). Both legs are "
              f"within-size and bound-matched, so this is a block-size effect, not an "
              f"occupancy artifact — the 128 lanes hold 7 blocks/SM and the 256 lanes 3.")


# --- v3 R5 frontier emitter -------------------------------------------------------


def signed(diffs, threshold):
    """The preregistered signed rule (spec 2.3): A *wins over* B iff the median of the
    paired per-round contrasts is negative AND at least `threshold` of them are negative;
    *loses* is the mirror; anything else is a *wash*. The threshold is a literal keyed to
    the rotation's preregistered round count, never a ratio recomputed from the log."""
    med = median(diffs)
    neg = sum(1 for x in diffs if x < 0)
    pos = sum(1 for x in diffs if x > 0)
    if med < 0 and neg >= threshold:
        return "win", med, neg
    if med > 0 and pos >= threshold:
        return "lose", med, pos
    return "wash", med, max(neg, pos)


def session(key, rounds, arms, trailer, sched):
    """Every R4 integrity gate, then the two R5 ones (preregistered round count, ordered
    admitted-id prefix), then the per-lane paired series. Fail-closed throughout: a gate
    that cannot be evaluated is an error, never a skipped section."""
    tag, order = key
    spec = FRONTIER[tag]
    # The ±2 % sanity anchors and the R2c bridge base are preregistered per TERM ORDER; an
    # order nobody preregistered has neither, so it is a stated rejection rather than a
    # KeyError two hundred lines later.
    if order not in ANCHORS or order not in R2C:
        sys.exit(f"{tag}/{order}: unknown term order — the sanity anchors and the R2c "
                 f"bridge base are preregistered for {sorted(ANCHORS)} only, so a "
                 f"`{order}` section cannot be decided")
    if not arms:
        sys.exit(f"{tag}/{order}: no ARM lines for this order — old-format or truncated log")
    if trailer is None:
        sys.exit(f"{tag}/{order}: no `{tag} done order={order} …` trailer — the run did not "
                 f"finish, or the log is truncated")
    if sched is None:
        sys.exit(f"{tag}/{order}: ARM or SAMPLE rows with no `{tag} schedule` line")
    if not rounds:
        sys.exit(f"{tag}/{order}: the log declares this order ({sched[1]} rounds x {sched[0]} "
                 f"lanes) but carries no SAMPLE rows — a declared order is emitted or it is "
                 f"an error, never silently skipped")
    lanes = list(arms)
    if set(lanes) != spec["lanes"]:
        missing = sorted(spec["lanes"] - set(lanes))
        extra = sorted(set(lanes) - spec["lanes"])
        sys.exit(f"{tag}/{order}: lane set is not the {spec['what']} frontier rotation — "
                 f"missing {missing}, unexpected {extra}")
    if len(lanes) != trailer[2] or len(lanes) != sched[0]:
        sys.exit(f"{tag}/{order}: {len(lanes)} ARM lines but the trailer declares "
                 f"{trailer[2]} lanes — the log is truncated or mixes builds")
    for r in sorted(rounds):
        if set(rounds[r]) != set(lanes):
            sys.exit(f"{tag}/{order}: round {r} carries {sorted(rounds[r])}, expected "
                     f"{lanes} — incomplete rounds are not droppable, the contrasts are "
                     f"paired")
        for lane, (_, _, kernel) in rounds[r].items():
            if kernel != arms[lane]["kernel"]:
                sys.exit(f"{tag}/{order}: round {r} lane {lane} ran `{kernel}` but its ARM "
                         f"line declares `{arms[lane]['kernel']}` — the log describes a "
                         f"kernel the run did not use")
    if len(rounds) % len(lanes) != 0:
        sys.exit(f"{tag}/{order}: {len(rounds)} rounds over {len(lanes)} lanes is not "
                 f"balanced — every lane must start equally often")
    if len(rounds) != trailer[1]:
        sys.exit(f"{tag}/{order}: {len(rounds)} rounds in the log, trailer claims rounds="
                 f"{trailer[1]} — truncated log")
    if (sched[1], sched[2]) != (trailer[1], trailer[0]):
        sys.exit(f"{tag}/{order}: the schedule line declares rounds={sched[1]} "
                 f"warmup={sched[2]} but the trailer declares rounds={trailer[1]} "
                 f"warmup={trailer[0]} — the log mixes two runs, or the header does not "
                 f"describe what ran")
    # THE PREREGISTERED ROUND COUNT. The signed thresholds are literals (90/100, 94/104),
    # so a log at any other count has no threshold to be judged against — deriving one
    # from the log would be exactly the post-hoc choice preregistration exists to prevent.
    if len(rounds) != spec["rounds"]:
        sys.exit(f"{tag}/{order}: {len(rounds)} timed rounds, but the {spec['what']} "
                 f"frontier is preregistered at {spec['rounds']} with the signed threshold "
                 f"{spec['threshold']}/{spec['rounds']} — no other round count has a "
                 f"preregistered threshold, so this log cannot be decided")
    want_ids = list(range(trailer[0], trailer[0] + trailer[1]))
    if sorted(rounds) != want_ids:
        got = sorted(rounds)
        sys.exit(f"{tag}/{order}: round ids are {got[:4]}…{got[-1]}, expected the "
                 f"consecutive run {want_ids[0]}…{want_ids[-1]} (warmup {trailer[0]}, "
                 f"rounds {trailer[1]}) — gaps, duplicates or a renumbered log, none of "
                 f"which is a paired rotation")
    per = len(rounds) // len(lanes)
    slots = defaultdict(int)
    for r in sorted(rounds):
        for slot, lane in enumerate(rounds[r]):
            slots[(lane, slot)] += 1
    for lane in lanes:
        for slot in range(len(lanes)):
            if slots[(lane, slot)] != per:
                sys.exit(f"{tag}/{order}: lane {lane} runs at rotation position {slot} in "
                         f"{slots[(lane, slot)]} rounds, expected {per} — the rotation is "
                         f"not balanced, so a lane keeps a position and its median carries "
                         f"that position's clock state")
    keys = sorted(rounds)
    # ADMITTED-ID GATE. Ordered, against the controller-derived oracle prefix. Counts are
    # blind to a reversal among equal-ref, equal-class sources; only the LIST sees it.
    for lane in lanes:
        f = arms[lane]
        ids, k = f["ids"], f["admitted"]
        if len(ids) != k:
            sys.exit(f"{tag}/{order}: lane {lane} declares {k} admitted sources but lists "
                     f"{len(ids)} ids")
        if LANE_K[lane] != k:
            sys.exit(f"{tag}/{order}: lane {lane} admits {k} sources but its name claims "
                     f"K = {LANE_K[lane]} — the label and the plan disagree")
        want = ORACLE_ORDER[:k]
        if ids != want:
            at = next(i for i, (g, w) in enumerate(zip(ids, want)) if g != w)
            sys.exit(f"{tag}/{order}: lane {lane} admits source {ids[at]} at admission "
                     f"position {at}, the oracle ordering has {want[at]} — the admitted "
                     f"prefix is not the canonical one (counts cannot see this)")
    # ALIASING GUARD, R4's verbatim: two lanes that declare different plans cannot produce
    # bit-identical per-round samples, and two lanes with one plan are one experiment.
    for i, a in enumerate(lanes):
        for b in lanes[i + 1:]:
            if arms[a]["ids"] == arms[b]["ids"] and arms[a]["threads"] == arms[b]["threads"] \
               and arms[a]["removals"]:
                sys.exit(f"{tag}/{order}: lanes {a} and {b} declare the SAME plan at the "
                         f"same block size — one experiment under two labels")
            if all(rounds[r][a][:2] == rounds[r][b][:2] for r in keys):
                sys.exit(f"{tag}/{order}: lanes {a} and {b} carry BIT-IDENTICAL samples in "
                         f"every round — the log aliases one lane's data onto another")
    # eval + finalize per round IS the decision quantity (spec 2.3: the bar is on the
    # eval+finalize median, and finalize is the stage the block sizes differ on).
    tot = {a: [rounds[r][a][0] + rounds[r][a][1] for r in keys] for a in lanes}
    return {
        "tag": tag, "order": order, "spec": spec, "lanes": lanes, "arms": arms,
        "rounds": rounds, "keys": keys, "tot": tot,
        "med": {a: median(tot[a]) for a in lanes},
        "med_ev": {a: median(rounds[r][a][0] for r in keys) for a in lanes},
        "med_fin": {a: median(rounds[r][a][1] for r in keys) for a in lanes},
    }


def paired(s, a, b):
    """The paired per-round contrast `a - b` on eval+finalize, with its signed verdict."""
    d = [x - y for x, y in zip(s["tot"][a], s["tot"][b])]
    verdict, med, on = signed(d, s["spec"]["threshold"])
    lo, hi = iqr(d)
    return {"med": med, "lo": lo, "hi": hi, "on": on, "n": len(d), "verdict": verdict}


def canonical(s):
    """The canonical prefix points of one session, in C order. `cache0` and the controls
    admit nothing, so they are baselines rather than points on the frontier."""
    return sorted((a for a in s["lanes"] if s["arms"][a]["admitted"] > 0),
                  key=lambda a: s["arms"][a]["c"])


def curve(s, base, title, rule, per_removal=None):
    print(f"\n**{title}** — baseline `{base}`, paired per round on `eval + finalize`. "
          f"{rule}\n")
    head = "| lane | C | removals | median (ms) | IQR | on-sign | signed verdict |"
    rule_row = "| --- | --- | --- | --- | --- | --- | --- |"
    if per_removal:
        head += f" {per_removal} |"
        rule_row += " --- |"
    print(head)
    print(rule_row)
    for lane in canonical(s):
        if lane == base:
            continue
        f, c = s["arms"][lane], paired(s, lane, base)
        row = (f"| `{lane}` | {f['c']} | {f['removals']} | **{c['med']:+.3f}** | "
               f"{c['lo']:+.3f} … {c['hi']:+.3f} | {c['on']}/{c['n']} | **{c['verdict']}** |")
        if per_removal:
            # Removals come off the ARM lines, which Rust fills from the lane's own planned
            # counts — this script holds no removal constant of its own.
            denom = f["removals"] - s["arms"][base]["removals"]
            row += f" {1000.0 * c['med'] / denom:+.2f} |" if denom else " n/a |"
        print(row)


def frontier(orders, tags, runs, arms, done, sched, where):
    sessions = {}
    for tag in tags:
        for order in orders:
            key = (tag, order)
            if key not in sched and key not in runs:
                continue
            sessions[key] = session(key, runs[key], arms.get(key, {}), done.get(key),
                                    sched.get(key))
    if not sessions:
        sys.exit(f"{where}: no frontier section survived the order filter")

    print("## v3 R5 — admission-frontier curves\n")
    print("Every figure below is EMITTED, not transcribed: this script is the single "
          "authority for the derived decisions, and each decision line names the "
          "preregistered rule (spec 2.3) it implements. Contrasts are paired per round on "
          "`eval + finalize` — the bar quantity — and curves are NEVER pooled across term "
          "orders.\n")

    for key in sorted(sessions, key=lambda k: (k[0] != "FRONTIER-FACTORIAL",
                                               k[1] != "locality", k[1])):
        emit_session(sessions[key])

    decide(sessions, orders)


def emit_session(s):
    tag, order, spec = s["tag"], s["order"], s["spec"]
    print(f"\n### `{tag}` — `--term-order {order}`, {len(s['keys'])} paired rounds, "
          f"{len(s['lanes'])} lanes\n")
    print("| lane | kernel | regs | blocks/SM | threads | grid | C | removals | admitted | "
          "median `eval` | median `finalize` | median `eval+fin` |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    for a in s["lanes"]:
        f = s["arms"][a]
        print(f"| `{a}` | `{f['kernel']}` | {f['regs']} | {f['blocks_sm']} | {f['threads']} | "
              f"{f['grid']} | {f['c']} | {f['removals']} | {f['admitted']} | "
              f"{s['med_ev'][a]:.3f} | {s['med_fin'][a]:.3f} | **{s['med'][a]:.3f}** |")
    print(f"\nAdmitted-id lists gated ORDERED against the controller oracle "
          f"(`expected-counts-r5.md` / `oracle-derivation.txt`), all {len(s['lanes'])} "
          f"lanes. Signed rule at this rotation: "
          f"{spec['threshold']}/{spec['rounds']} (spec 2.3, preregistered literal).")

    curve(s, "control_lb@128", "Curve 1 — total-net vs `control_lb@128`",
          "The bound-matched baseline; this is the curve C\\* is read off (spec 2.3).")
    curve(s, "hot16@128", "Curve 2 — marginal vs `hot16@128`",
          "The incumbent. Per-removal column divides by the INCREMENTAL removals over "
          "hot16, from the ARM lines.", per_removal="µs / incremental removal")
    curve(s, "cache0@128", "Curve 3 — machinery-corrected refund vs `cache0@128`",
          "cache0 pays the frame, the walk and the lookup and removes nothing, so this "
          "curve is the removals alone. Per-removal column divides by the lane's own "
          "removals.", per_removal="µs / removal")

    # C* — spec 2.3: the most negative median vs control_lb@128 among lanes that WIN over
    # control_lb@128 under the signed rule.
    winners = [(paired(s, a, "control_lb@128"), a) for a in canonical(s)]
    winners = [(c, a) for c, a in winners if c["verdict"] == "win"]
    if winners:
        best = min(winners, key=lambda t: t[0]["med"])
        print(f"\n**Session optimum ({order}, {tag})** = `{best[1]}` at C = "
              f"{s['arms'][best[1]]['c']} units, {best[0]['med']:+.3f} ms vs "
              f"`control_lb@128` ({best[0]['on']}/{best[0]['n']} on-sign) — the spec 2.3 "
              f"rule applied WITHIN this rotation; C\\* for the order is taken over the "
              f"union of the rotations below.")
    else:
        print(f"\n**Session optimum ({order}, {tag})** = none — no canonical lane wins "
              f"over `control_lb@128` under the signed rule (spec 2.3).")

    # Sanity anchors — spec 2.3. The emitter states in/out; the abort/repeat/paired-only
    # rule is the measurement task's to execute.
    print(f"\n**Sanity anchors ({order})** — spec 2.3, +/-2 % of R4's frozen in-rotation "
          f"medians. The verdict below is the deterministic rule's INPUT; executing "
          f"abort -> one repeat -> PAIRED RESULTS ONLY is the measurement task's.\n")
    print("| anchor | this session | R4 frozen | delta | verdict |")
    print("| --- | --- | --- | --- | --- |")
    s["sanity"] = True
    for lane, target in zip(("control@256", "hot16@128"), ANCHORS[order]):
        got = s["med"][lane]
        rel = (got - target) / target
        ok = abs(rel) <= SANITY_TOL
        s["sanity"] = s["sanity"] and ok
        print(f"| `{lane}` | {got:.3f} | {target:.3f} | {100.0 * rel:+.2f} % | "
              f"**{'IN' if ok else 'OUT'}** |")


def union(sessions, order):
    """Every canonical lane measured in `order`, in C order, each bound to the session that
    measured it. A lane in both sessions is taken from the PRIMARY rotation (deterministic
    rule, stated in the emitted line): cross-session lanes are only ever compared through
    the anchors both rotations carry, never raw."""
    picked = {}
    for tag in ("FRONTIER-FACTORIAL", "FRONTIER-EXTENSION"):
        s = sessions.get((tag, order))
        if s is None:
            continue
        for lane in canonical(s):
            picked.setdefault(lane, s)
    return sorted(picked.items(), key=lambda kv: kv[1]["arms"][kv[0]]["c"])


def winner_of(sessions, order):
    """One computation of an order's frontier shape, shared by the emitted table and the
    ncu manifest: the union lanes in C order, their net contrasts vs `control_lb@128`, and
    the winner (spec 2.3 — most negative median among the lanes that WIN over the
    bound-matched control), or `None` when nothing wins."""
    lanes = union(sessions, order)
    nets = {lane: paired(s, lane, "control_lb@128") for lane, s in lanes}
    won = [(lane, s) for lane, s in lanes if nets[lane]["verdict"] == "win"]
    if not won:
        return lanes, nets, None, None
    winner, wsession = min(won, key=lambda t: nets[t[0]]["med"])
    return lanes, nets, winner, wsession


def first_loser_of(lanes, winner, wsession):
    """spec 2.5: the smallest-C lane ABOVE the winner that LOSES to it in that order.
    Returns `(hit, unpairable)`; the signed rule is paired, so a lane that shares no
    rotation with the winner is reported rather than guessed at."""
    unpairable = []
    for lane, s in lanes:
        if s["arms"][lane]["c"] <= wsession["arms"][winner]["c"]:
            continue
        if winner not in s["arms"]:
            unpairable.append(lane)
            continue
        if paired(s, lane, winner)["verdict"] == "lose":
            return (lane, s), unpairable
    return None, unpairable


def neighbours_of(order_list, lane, extension):
    """spec 2.5: a lane's available canonical prefix neighbours — one below, one above. The
    TOP endpoint has no lane above, so it takes its single neighbour plus the extension's
    first lane when the extension ran; the BOTTOM endpoint simply has one neighbour."""
    if lane not in order_list:
        return []
    i = order_list.index(lane)
    out = [order_list[i - 1]] if i > 0 else []
    if i + 1 < len(order_list):
        out.append(order_list[i + 1])
    elif extension and extension != lane:
        out.append(extension)
    return out


def where_measured(sessions, order, lane):
    """The rotation a lane's raw median is read from, PRIMARY first — the same rule the
    union table states, so the bar verdict and the bridges cannot drift from the curves."""
    for tag in ("FRONTIER-FACTORIAL", "FRONTIER-EXTENSION"):
        s = sessions.get((tag, order))
        if s is not None and lane in s["arms"]:
            return s
    return None


def decide(sessions, orders):
    orders = [o for o in orders if any(k[1] == o for k in sessions)]
    primary = {o: sessions.get(("FRONTIER-FACTORIAL", o)) for o in orders}
    extension_ran = any(k[0] == "FRONTIER-EXTENSION" for k in sessions)
    # Every rule below that says "either order" or "BOTH orders" needs both present. One
    # order in is a valid input, but it must be SAID, not silently collapsed.
    both_orders = len(orders) >= 2

    print("\n### Preregistered decisions\n")
    if not both_orders:
        print(f"> **SINGLE ORDER.** This log set carries `{orders[0]}` only (one order's "
              f"logs, or `--order` narrowed it). The per-order sections below stand; the "
              f"cross-order rules — the extension trigger's *either order*, the headline "
              f"selector's *BOTH orders*, the bar verdict and the bridges — are flagged "
              f"where they are not evaluable.\n")

    # EXTENSION TRIGGER — spec 2.3: triggers iff k48 WINS over k46 (signed) in either
    # order. A wash does NOT trigger.
    lines = []
    triggered = False
    for o in orders:
        s = primary[o]
        if s is None or "k46@128" not in s["arms"]:
            lines.append(f"- `{o}`: not evaluable — no primary rotation carrying k46 and k48.")
            continue
        c = paired(s, "k48@128", "k46@128")
        triggered = triggered or c["verdict"] == "win"
        lines.append(f"- `{o}`: k48 − k46 = {c['med']:+.3f} ms ({c['on']}/{c['n']} on-sign) "
                     f"⇒ **{c['verdict']}**")
    print("**Extension trigger** (spec 2.3: triggers iff k48 *wins over* k46 under the "
          "signed rule in EITHER order; a wash does not trigger):\n")
    print("\n".join(lines))
    print(f"\n⇒ extension **{'TRIGGERED' if triggered else 'NOT triggered'}**; the "
          f"extension rotation {'IS' if extension_ran else 'is NOT'} present in this log "
          f"set."
          + ("" if both_orders else
             f" **Evaluated over `{orders[0]}` ALONE** — spec 2.3's *either order* spans "
             f"both, so a NOT-triggered verdict here is provisional until the other "
             f"order's log is included."))

    # PER-ORDER FRONTIER SHAPE: winner, broad knee, first loser, right-censoring.
    broad_any = False
    for o in orders:
        lanes, nets, winner, wsession = winner_of(sessions, o)
        if not lanes:
            continue
        print(f"\n**Frontier shape — `{o}`** (union of the rotations, in C order; a lane "
              f"present in both sessions is taken from the primary rotation, and every "
              f"cross-session comparison rides the shared `control_lb@128` anchor):\n")
        print("| lane | session | C | net vs `control_lb@128` | signed verdict |")
        print("| --- | --- | --- | --- | --- |")
        for lane, s in lanes:
            print(f"| `{lane}` | {s['tag']} | {s['arms'][lane]['c']} | "
                  f"{nets[lane]['med']:+.3f} | {nets[lane]['verdict']} |")
        if winner is None:
            # spec 4's OTHER edge: nothing in the sweep beats the bound-matched control, so
            # the knee sits BELOW C = 36 rather than past the top lane. Right-censoring is
            # the opposite outcome and must not be reported here.
            print(f"\n- winner: **none** — no canonical lane wins over `control_lb@128` "
                  f"in `{o}` (spec 2.3).")
            print(f"- the knee is BELOW this sweep for `{o}`: the rung answers with "
                  f"**hot16 already ≈ optimal** (spec 4, a valid and recordable outcome). "
                  f"This is NOT right-censoring, which is the opposite edge.")
            continue
        print(f"\n- winner (C\\*): **`{winner}`** at C = {wsession['arms'][winner]['c']}, "
              f"{nets[winner]['med']:+.3f} ms vs `control_lb@128` — spec 2.3.")
        # BROAD KNEE — spec 2.3: >= 3 CONSECUTIVE canonical lanes within 0.10 ms of the
        # per-order optimum, in EITHER order. Measured in the net-vs-control_lb currency,
        # which is what makes the seam-spanning comparison legitimate.
        best = nets[winner]["med"]
        near = [abs(nets[lane]["med"] - best) <= KNEE_MS for lane, _ in lanes]
        run = best_run = 0
        for flag in near:
            run = run + 1 if flag else 0
            best_run = max(best_run, run)
        broad = best_run >= 3
        broad_any = broad_any or broad
        print(f"- broad knee in `{o}`: **{'yes' if broad else 'no'}** — longest run of "
              f"consecutive canonical lanes within {KNEE_MS:.2f} ms of the optimum is "
              f"{best_run} (spec 2.3 needs >= 3).")
        hit, unpairable = first_loser_of(lanes, winner, wsession)
        if hit:
            lane, s = hit
            c = paired(s, lane, winner)
            print(f"- first loser in `{o}`: **`{lane}`** (C = {s['arms'][lane]['c']}), "
                  f"{c['med']:+.3f} ms vs the winner, {c['on']}/{c['n']} on-sign — spec 2.5.")
        else:
            edge = lanes[-1][0]
            print(f"- first loser in `{o}`: **none** — no canonical lane above the winner "
                  f"loses to it under the signed rule.")
            print(f"- the frontier is reported **RIGHT-CENSORED at {edge}** for `{o}` and "
                  f"NO located-knee claim is made (spec 4); the follow-up decision "
                  f"(extend further vs. move to the D rung) is left to RR.")
        if unpairable:
            print(f"- not decidable across the session seam in `{o}`: "
                  f"{', '.join(f'`{x}`' for x in unpairable)} — those lanes do not share a "
                  f"rotation with the winner, and the signed rule is paired.")
    print(f"\n**Broad-knee verdict (either order, spec 2.3)**: "
          f"**{'BROAD' if broad_any else 'not broad'}** — this gates the preregistered "
          f"reuse-distance follow-up, which is NOT part of this rung.")

    # HEADLINE SELECTOR — spec 2.3, verbatim: eligible = wins over hot16@128 under BOTH
    # orders; select the maximum WORST-order improvement; ties break toward smaller C.
    #
    # BOTH orders is a REQUIREMENT of the rule, not a convenience: with one order present
    # the eligibility test degenerates to a single-order win and would silently promote a
    # lane the rule never qualified. One order in, no candidate out — and with no candidate
    # there is nothing for the bar verdict or the bridges to be about.
    print("\n**Headline selector** (spec 2.3: eligible = lanes that win over `hot16@128` "
          "under BOTH orders; select the maximum WORST-order improvement; ties break "
          "toward smaller C). Selection runs on the FULL-PRECISION medians, so two rows "
          "that print equal need not be tied:\n")
    marginal = defaultdict(dict)
    for o in orders:
        for lane, s in union(sessions, o):
            if lane == "hot16@128":
                continue
            marginal[lane][o] = (paired(s, lane, "hot16@128"), s)
    eligible = [lane for lane, per in marginal.items()
                if len(per) == len(orders)
                and all(c["verdict"] == "win" for c, _ in per.values())]
    print("| lane | C | " + " | ".join(f"vs hot16 (`{o}`)" for o in orders)
          + " | worst order | eligible |")
    print("| --- | --- | " + " | ".join("---" for _ in orders) + " | --- | --- |")
    for lane in sorted(marginal, key=lambda x: next(iter(marginal[x].values()))[1]["arms"][x]["c"]):
        per = marginal[lane]
        c_units = next(iter(per.values()))[1]["arms"][lane]["c"]
        cells = []
        for o in orders:
            if o in per:
                c, _ = per[o]
                cells.append(f"{c['med']:+.3f} ({c['verdict']})")
            else:
                cells.append("n/a")
        worst = max((per[o][0]["med"] for o in orders if o in per), default=float("nan"))
        print(f"| `{lane}` | {c_units} | " + " | ".join(cells)
              + f" | {worst:+.4f} | {'yes' if lane in eligible else 'no'} |")
    if not both_orders:
        headline = None
        print(f"\n⇒ **SINGLE ORDER — the both-order eligibility rule is not evaluable; no "
              f"headline, no bar verdict** (spec 2.3). This log set carries only "
              f"`{orders[0]}`, and eligibility requires a win over `hot16@128` under BOTH "
              f"orders; the `eligible` column above is a single-order win, NOT the rule. "
              f"Re-run the emitter over both orders' logs, without `--order`, to decide. "
              f"The R4 bridges are omitted with it — they corroborate a selected candidate.")
    elif eligible:
        headline = min(eligible, key=lambda lane: (
            max(marginal[lane][o][0]["med"] for o in orders),
            next(iter(marginal[lane].values()))[1]["arms"][lane]["c"]))
        worst = max(marginal[headline][o][0]["med"] for o in orders)
        print(f"\n⇒ **headline candidate = `{headline}`**, worst-order improvement over "
              f"`hot16@128` = {worst:+.3f} ms.")
    else:
        headline = "hot16@128"
        print("\n⇒ eligible set is EMPTY ⇒ **hot16 remains the frontier optimum** (spec "
              "2.3 — a valid outcome).")

    if headline is not None:
        # BAR — spec 2.3: the selected K's eval+finalize median under 14.61 ms in BOTH
        # orders, this session, raw.
        print(f"\n**Bar verdict** (spec 2.3: the selected lane's raw `eval+finalize` "
              f"median below {BAR} ms in BOTH orders, this session):\n")
        print("| order | lane | raw median | vs bar |")
        print("| --- | --- | --- | --- |")
        raw_ok = True
        for o in orders:
            s = where_measured(sessions, o, headline)
            if s is None:
                print(f"| `{o}` | `{headline}` | n/a | not measured |")
                raw_ok = False
                continue
            got = s["med"][headline]
            ok = got < BAR
            raw_ok = raw_ok and ok
            print(f"| `{o}` | `{headline}` | {got:.3f} | **{'under' if ok else 'over'}** |")
        print(f"\n⇒ bar **{'MET' if raw_ok else 'NOT met'}** raw. Sanity anchors "
              f"{'all IN' if all(s['sanity'] for s in sessions.values()) else 'NOT all in'} "
              f"±2 % — a session with an OUT anchor reports PAIRED RESULTS ONLY and this "
              f"raw claim does not stand (spec 2.3).")

        # R4 BRIDGES — unconditional, both forms, both bases.
        print(f"\n**R4 dual bridges for `{headline}`** (unconditional corroboration; "
              f"additive = R2c + (medW − medBase), ratio = R2c × medW / medBase, "
              f"R2c = 16.453 census / 16.283 locality):\n")
        print("| order | base | medW | medBase | additive | ratio |")
        print("| --- | --- | --- | --- | --- | --- |")
        for o in orders:
            s = where_measured(sessions, o, headline)
            if s is None:
                continue
            for base in ("control@256", "control_lb@128"):
                w, b = s["med"][headline], s["med"][base]
                print(f"| `{o}` | `{base}` | {w:.3f} | {b:.3f} | {R2C[o] + (w - b):.3f} | "
                      f"{R2C[o] * w / b:.3f} |")

    # NCU MANIFEST — machine-readable, deduplicated; consumed as authoritative.
    roles = defaultdict(set)
    orders_of = defaultdict(set)
    # "the extension's first lane" (spec 2.5) = its lowest-C canonical lane that the
    # primary rotation does not already carry; k48 rides along as the paired seam anchor.
    in_primary = {lane for k in sessions if k[0] == "FRONTIER-FACTORIAL"
                  for lane in canonical(sessions[k])}
    extension = next((lane for k in sorted(sessions) if k[0] == "FRONTIER-EXTENSION"
                      for lane in canonical(sessions[k]) if lane not in in_primary), None)
    for o in orders:
        lanes, nets, winner, wsession = winner_of(sessions, o)
        if not lanes:
            continue
        order_list = [lane for lane, _ in lanes]
        for lane in order_list:
            orders_of[lane].add(o)
        # spec 2.5 expands neighbours around EACH of "these lanes" — the order's winner AND
        # the selected headline candidate, which can be a third lane different from both
        # orders' winners. Expanding around the winners alone drops the headline's own
        # neighbours from the capture set.
        for lane in ([winner] if winner else []) + ([headline] if headline else []):
            if lane not in order_list:
                continue
            for near in neighbours_of(order_list, lane, extension):
                roles[near].add("neighbor")
        if winner is None:
            continue
        roles[winner].add("winner")
        hit, _ = first_loser_of(lanes, winner, wsession)
        if hit:
            roles[hit[0]].add("first-loser")
    if headline is not None:
        roles[headline].add("headline")
    print("\n### ncu capture manifest\n")
    print("Deduplicated union of the per-order winners, the headline candidate, the "
          "canonical neighbours of BOTH, and the per-order first losers, each under both "
          "term orders (spec 2.5). Task 4 consumes this block as AUTHORITATIVE and does "
          "not reconstruct it.\n")
    if headline is None:
        print("**Incomplete for Task 4**: no headline candidate was selectable (see the "
              "selector above), so the manifest carries the per-order winners, their "
              "neighbours and the first losers only.\n")
    print("```")
    for lane in sorted(roles, key=lambda x: (len(orders_of[x]) == 0, x)):
        print(f"NCU-CAPTURE lane={lane} orders={','.join(sorted(orders_of[lane])) or 'n/a'} "
              f"roles={','.join(sorted(roles[lane]))}")
    print("```")


# --- v3 R8 interior emitter -------------------------------------------------------
#
# DEDICATED (amendment A2). Everything above this line is written around the two R5
# rotations: their lane sets, their per-rotation thresholds, C\*, the extension trigger, the
# broad knee, the both-orders headline selector. R8 sweeps ONE contiguous axis and asks a
# different question — where the loss begins, whether it is monotone, and what each step costs
# per removed production — so it carries its own validator, its own decision rows and its own
# manifest, and the R5 path is left byte-identical.


def ipaired(s, a, b):
    """The paired per-round contrast `a - b` on `eval + finalize`, under R8's signed rule
    (amendment A1): a WIN or a LOSS needs sign-stability >= 87/96; anything below that, either
    sign, is a WASH."""
    d = [x - y for x, y in zip(s["tot"][a], s["tot"][b])]
    verdict, med, on = signed(d, INTERIOR["threshold"])
    lo, hi = iqr(d)
    return {"med": med, "lo": lo, "hi": hi, "on": on, "n": len(d), "verdict": verdict}


def interior_session(key, rounds, arms, trailer, sched):
    """The R8 log contract, fail-closed (amendment A5): exactly this rotation, recorded at
    `--log-trace 24`, at 96 rounds / 12 warmup, with ordered admitted prefixes and the
    one-BF-per-step axis the counts oracle derives. A gate that cannot be evaluated is an
    error, never a skipped section."""
    order = key[1]
    if order not in ANCHORS or order not in R5_SESSION:
        sys.exit(f"{R8}/{order}: unknown term order — the R4-frozen anchor band is "
                 f"preregistered for {sorted(ANCHORS)} only, so a `{order}` section cannot be "
                 f"adjudicated")
    if not arms:
        sys.exit(f"{R8}/{order}: no ARM lines for this order — old-format or truncated log")
    if trailer is None:
        sys.exit(f"{R8}/{order}: no `{R8} done order={order} …` trailer — the run did not "
                 f"finish, or the log is truncated")
    if sched is None:
        sys.exit(f"{R8}/{order}: ARM or SAMPLE rows with no `{R8} schedule` line")
    if not rounds:
        sys.exit(f"{R8}/{order}: the log declares this order ({sched[1]} rounds x {sched[0]} "
                 f"lanes) but carries no SAMPLE rows — a declared order is emitted or it is an "
                 f"error, never silently skipped")
    lanes = list(arms)
    if set(lanes) != INTERIOR["lanes"]:
        missing = sorted(INTERIOR["lanes"] - set(lanes))
        extra = sorted(set(lanes) - INTERIOR["lanes"])
        sys.exit(f"{R8}/{order}: lane set is not the interior rotation — missing {missing}, "
                 f"unexpected {extra}")
    if len(lanes) != trailer[2] or len(lanes) != sched[0]:
        sys.exit(f"{R8}/{order}: {len(lanes)} ARM lines but the trailer declares {trailer[2]} "
                 f"lanes — the log is truncated or mixes builds")
    for lane in lanes:
        want = INTERIOR_GRID[lane]
        if arms[lane]["grid"] != want:
            sys.exit(f"{R8}/{order}: lane {lane} declares grid={arms[lane]['grid']}, and this "
                     f"rung's lanes are preregistered at `--log-trace {INTERIOR_TRACE}`, where "
                     f"it is {want} — a session recorded at another trace is internally "
                     f"consistent, so nothing else would see it")
    if (sched[1], sched[2]) != (trailer[1], trailer[0]):
        sys.exit(f"{R8}/{order}: the schedule line declares rounds={sched[1]} "
                 f"warmup={sched[2]} but the trailer declares rounds={trailer[1]} "
                 f"warmup={trailer[0]} — the log mixes two runs, or the header does not "
                 f"describe what ran")
    # THE PREREGISTERED SHAPE. The signed threshold is a literal keyed to 96 rounds, and the
    # flank rule reads the first and last full 12-round cycle, so neither a different round
    # count nor a partial-cycle warmup has a preregistered rule to be decided under.
    if (trailer[1], trailer[0]) != (INTERIOR["rounds"], INTERIOR["warmup"]):
        sys.exit(f"{R8}/{order}: the log declares rounds={trailer[1]} warmup={trailer[0]}, "
                 f"and the interior rotation is preregistered at {INTERIOR['rounds']} rounds / "
                 f"{INTERIOR['warmup']} warmup with the signed threshold "
                 f"{INTERIOR['threshold']}/{INTERIOR['rounds']} (A1/A5) — no other shape has a "
                 f"preregistered threshold, so this log cannot be decided")
    for r in sorted(rounds):
        if set(rounds[r]) != set(lanes):
            sys.exit(f"{R8}/{order}: round {r} carries {sorted(rounds[r])}, expected {lanes} — "
                     f"incomplete rounds are not droppable, the contrasts are paired")
        for lane, (_, _, kernel) in rounds[r].items():
            if kernel != arms[lane]["kernel"]:
                sys.exit(f"{R8}/{order}: round {r} lane {lane} ran `{kernel}` but its ARM line "
                         f"declares `{arms[lane]['kernel']}` — the log describes a kernel the "
                         f"run did not use")
    if len(rounds) != trailer[1]:
        sys.exit(f"{R8}/{order}: {len(rounds)} rounds in the log, trailer claims rounds="
                 f"{trailer[1]} — truncated log")
    if len(rounds) % len(lanes) != 0:
        sys.exit(f"{R8}/{order}: {len(rounds)} rounds over {len(lanes)} lanes is not balanced — "
                 f"every lane must start equally often")
    want_ids = list(range(trailer[0], trailer[0] + trailer[1]))
    if sorted(rounds) != want_ids:
        got = sorted(rounds)
        sys.exit(f"{R8}/{order}: round ids are {got[:4]}…{got[-1]}, expected the consecutive "
                 f"run {want_ids[0]}…{want_ids[-1]} (warmup {trailer[0]}, rounds {trailer[1]}) "
                 f"— gaps, duplicates or a renumbered log, none of which is a paired rotation")
    per = len(rounds) // len(lanes)
    slots = defaultdict(int)
    for r in sorted(rounds):
        for slot, lane in enumerate(rounds[r]):
            slots[(lane, slot)] += 1
    for lane in lanes:
        for slot in range(len(lanes)):
            if slots[(lane, slot)] != per:
                sys.exit(f"{R8}/{order}: lane {lane} runs at rotation position {slot} in "
                         f"{slots[(lane, slot)]} rounds, expected {per} — the rotation is not "
                         f"balanced, so a lane keeps a position and its median carries that "
                         f"position's clock state")
    keys = sorted(rounds)
    # ADMITTED-ID GATE, ordered against the controller-derived oracle prefix. The interior
    # points differ from one another by ONE source, so a reversal among equal-ref sources moves
    # no count at all; only the list sees it.
    for lane in lanes:
        f = arms[lane]
        ids, k = f["ids"], f["admitted"]
        if len(ids) != k:
            sys.exit(f"{R8}/{order}: lane {lane} declares {k} admitted sources but lists "
                     f"{len(ids)} ids")
        if LANE_K[lane] != k:
            sys.exit(f"{R8}/{order}: lane {lane} admits {k} sources but its name claims K = "
                     f"{LANE_K[lane]} — the label and the plan disagree")
        want = ORACLE_ORDER[:k]
        if ids != want:
            at = next(i for i, (g, w) in enumerate(zip(ids, want)) if g != w)
            sys.exit(f"{R8}/{order}: lane {lane} admits source {ids[at]} at admission position "
                     f"{at}, the oracle ordering has {want[at]} — the admitted prefix is not "
                     f"the canonical one (counts cannot see this)")
    for i, a in enumerate(lanes):
        for b in lanes[i + 1:]:
            if arms[a]["ids"] == arms[b]["ids"] and arms[a]["threads"] == arms[b]["threads"] \
               and arms[a]["removals"]:
                sys.exit(f"{R8}/{order}: lanes {a} and {b} declare the SAME plan at the same "
                         f"block size — one experiment under two labels")
            if all(rounds[r][a][:2] == rounds[r][b][:2] for r in keys):
                sys.exit(f"{R8}/{order}: lanes {a} and {b} carry BIT-IDENTICAL samples in every "
                         f"round — the log aliases one lane's data onto another")
    # THE AXIS, checked rather than trusted. Every step from hot16 through k24 admits exactly
    # one more source at refs 3, which is one more slab unit and two more removals. The
    # per-removal columns divide by these DELTAS off the ARM lines, so a log whose axis is not
    # this one would be priced in a currency the rung never preregistered.
    for below, above in zip(INTERIOR_AXIS, INTERIOR_AXIS[1:]):
        step = tuple(arms[above][f] - arms[below][f] for f in ("admitted", "c", "removals"))
        if step != (1, 1, 2):
            sys.exit(f"{R8}/{order}: the step {above} − {below} moves (admitted, C, removals) "
                     f"by {step}; the interior axis is one BF source at refs 3 per step = "
                     f"(1, 1, 2), and the per-removal columns divide by those deltas")
    tot = {a: [rounds[r][a][0] + rounds[r][a][1] for r in keys] for a in lanes}
    return {
        "order": order, "lanes": lanes, "arms": arms, "rounds": rounds, "keys": keys,
        "tot": tot,
        "med": {a: median(tot[a]) for a in lanes},
        "med_ev": {a: median(rounds[r][a][0] for r in keys) for a in lanes},
        "med_fin": {a: median(rounds[r][a][1] for r in keys) for a in lanes},
    }


def interior_shape(s):
    """One order's frontier shape (amendment A1): the eight adjacent steps in axis order, the
    eight cumulative contrasts against the incumbent, the winner (most negative cumulative
    median among the signed WINs, ties toward smaller K) and the first loser (the smallest n
    whose cumulative contrast is a signed LOSS)."""
    steps = [(above, below, ipaired(s, above, below))
             for below, above in zip(INTERIOR_AXIS, INTERIOR_AXIS[1:])]
    cum = {lane: ipaired(s, lane, INTERIOR_AXIS[0]) for lane in INTERIOR_AXIS[1:]}
    wins = [lane for lane in INTERIOR_AXIS[1:] if cum[lane]["verdict"] == "win"]
    winner = min(wins, key=lambda lane: (cum[lane]["med"], LANE_K[lane])) if wins else None
    loser = next((lane for lane in INTERIOR_AXIS[1:] if cum[lane]["verdict"] == "lose"), None)
    return steps, cum, winner, loser


def interior_flank(s, lane):
    """The first and last full cycle's block medians for one anchor lane, with the scaled
    threshold that goes with it (amendment A6)."""
    cycle = len(s["lanes"])
    first = median(s["tot"][lane][:cycle])
    last = median(s["tot"][lane][-cycle:])
    return first, last, abs(last - first), max(FLANK_MS, FLANK_REL * s["med"][lane])


def interior_emit(s):
    order = s["order"]
    steps, cum, winner, loser = interior_shape(s)
    print(f"\n### `{R8}` — `--term-order {order}`, {len(s['keys'])} paired rounds, "
          f"{len(s['lanes'])} lanes\n")
    print("| lane | kernel | regs | blocks/SM | threads | grid | C | removals | admitted | "
          "median `eval` | median `finalize` | median `eval+fin` |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    for a in s["lanes"]:
        f = s["arms"][a]
        print(f"| `{a}` | `{f['kernel']}` | {f['regs']} | {f['blocks_sm']} | {f['threads']} | "
              f"{f['grid']} | {f['c']} | {f['removals']} | {f['admitted']} | "
              f"{s['med_ev'][a]:.3f} | {s['med_fin'][a]:.3f} | **{s['med'][a]:.3f}** |")
    print(f"\nAdmitted-id lists gated ORDERED against the controller oracle "
          f"(`expected-counts-r8.md` / `oracle-derivation.txt`), all {len(s['lanes'])} lanes; "
          f"grids gated against `--log-trace {INTERIOR_TRACE}`. Signed rule at this rotation: "
          f"{INTERIOR['threshold']}/{INTERIOR['rounds']} (amendment A1, preregistered "
          f"literal).")

    print(f"\n**Adjacent steps ({order})** — each step admits ONE more BF source at refs 3, so "
          f"it removes two productions; paired per round on `eval + finalize`.\n")
    print("| step | K | C step | removals step | median (ms) | IQR | on-sign | verdict | "
          "µs / removal |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    for above, below, c in steps:
        f, g = s["arms"][above], s["arms"][below]
        # The divisor is the removals DELTA off the two ARM lines, which Rust fills from each
        # lane's own planned counts — this emitter holds no removal constant.
        rm = f["removals"] - g["removals"]
        print(f"| `{above}` − `{below}` | {f['admitted']} | +{f['c'] - g['c']} | +{rm} | "
              f"**{c['med']:+.3f}** | {c['lo']:+.3f} … {c['hi']:+.3f} | {c['on']}/{c['n']} | "
              f"**{VERDICT[c['verdict']]}** | {1000.0 * c['med'] / rm:+.2f} |")

    base = INTERIOR_AXIS[0]
    print(f"\n**Cumulative vs `{base}` ({order})** — the same axis read from the incumbent, "
          f"which is what locates the winner and the first loser.\n")
    print(f"| lane | K | C | removals over `{base}` | median (ms) | IQR | on-sign | verdict | "
          f"µs / removal |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    for lane in INTERIOR_AXIS[1:]:
        f, c = s["arms"][lane], cum[lane]
        rm = f["removals"] - s["arms"][base]["removals"]
        print(f"| `{lane}` | {f['admitted']} | {f['c']} | {rm} | **{c['med']:+.3f}** | "
              f"{c['lo']:+.3f} … {c['hi']:+.3f} | {c['on']}/{c['n']} | "
              f"**{VERDICT[c['verdict']]}** | {1000.0 * c['med'] / rm:+.2f} |")

    # THE HARD GATE (amendment A6). R5-session context follows it, and is context only.
    print(f"\n**Anchor band ({order})** — the R4-frozen ±2 % band, the HARD gate: a session "
          f"with an OUT anchor is INVALID, is repeated soaked, and emits no conclusion.\n")
    print("| anchor | this session | R4 frozen | delta | verdict |")
    print("| --- | --- | --- | --- | --- |")
    s["sanity"] = True
    for lane, target in zip(("control@256", "hot16@128"), ANCHORS[order]):
        got = s["med"][lane]
        rel = (got - target) / target
        ok = abs(rel) <= SANITY_TOL
        s["sanity"] = s["sanity"] and ok
        print(f"| `{lane}` | {got:.3f} | {target:.3f} | {100.0 * rel:+.2f} % | "
              f"**{'IN' if ok else 'OUT'}** |")
    print(f"\nR5-session context (REPORT-ONLY, amendment A6) — the R5 primary rotation's own "
          f"medians, for reading this session against the rung the interior extends; nothing "
          f"below gates on them.\n")
    print("| anchor | this session | R5 session | delta |")
    print("| --- | --- | --- | --- |")
    for lane, target in zip(("control@256", "hot16@128"), R5_SESSION[order]):
        got = s["med"][lane]
        print(f"| `{lane}` | {got:.3f} | {target:.3f} | {100.0 * (got - target) / target:+.2f} "
              f"% |")

    print(f"\n**Flank ({order})** — block medians of each anchor lane's FIRST and LAST full "
          f"cycle ({len(s['lanes'])} rounds each) against max({FLANK_MS:.2f} ms, "
          f"{100.0 * FLANK_REL:.1f} % of that lane's session median), amendment A6.\n")
    print("| anchor lane | first cycle | last cycle | drift | threshold | verdict |")
    print("| --- | --- | --- | --- | --- | --- |")
    s["flank"] = True
    for lane in INTERIOR_ANCHORS:
        first, last, drift, tol = interior_flank(s, lane)
        ok = drift <= tol
        s["flank"] = s["flank"] and ok
        print(f"| `{lane}` | {first:.3f} | {last:.3f} | {drift:.3f} | {tol:.3f} | "
              f"**{'PASS' if ok else 'TRIP'}** |")


def interior_decisions(s, selecting):
    """A1's decision bullets for one order. `selecting` is the LOCALITY session; the census
    one prints the same shape as DIAGNOSTIC context and alters nothing."""
    steps, cum, winner, loser = interior_shape(s)
    role = "SELECTION" if selecting else "diagnostic only — alters nothing (A1)"
    print(f"\n**`{s['order']}` — {role}**\n")
    pattern = " ".join("−" if c["med"] < 0 else "+" if c["med"] > 0 else "0"
                       for _, _, c in steps)
    verdicts = " ".join(VERDICT[c["verdict"]] for _, _, c in steps)
    print(f"- adjacent-step sign pattern, `{steps[0][0]} − {steps[0][1]}` first: `{pattern}` "
          f"({verdicts}) — reported verbatim; this is the monotonicity evidence.")
    if winner is None:
        print(f"- winner: **none** — no interior point wins over `{INTERIOR_AXIS[0]}` under "
              f"the signed rule, so the incumbent stands.")
    else:
        c, f = cum[winner], s["arms"][winner]
        print(f"- winner: **`{winner}`** (K = {f['admitted']}, C = {f['c']}) at "
              f"{c['med']:+.3f} ms vs `{INTERIOR_AXIS[0]}`, {c['on']}/{c['n']} on-sign — the "
              f"most negative cumulative median among the signed WINs, ties toward smaller K.")
    if loser is None:
        print(f"- first loser: **none** — no cumulative contrast is a signed LOSS through "
              f"`{INTERIOR_AXIS[-1]}`.")
    else:
        c, f = cum[loser], s["arms"][loser]
        print(f"- first loser: **`{loser}`** (K = {f['admitted']}, C = {f['c']}) at "
              f"{c['med']:+.3f} ms, {c['on']}/{c['n']} on-sign — the smallest K whose "
              f"cumulative contrast is a signed LOSS.")
    print(f"- the axis is RIGHT-CENSORED at `{INTERIOR_AXIS[-1]}`: K = "
          f"{s['arms'][INTERIOR_AXIS[-1]]['admitted']} is the largest measured point and no "
          f"claim is made past it.")
    return winner, loser


def interior_report(sessions):
    print("## v3 R8 — the admission-frontier interior (K17–23)\n")
    print(f"Every figure below is EMITTED, not transcribed: this script is the single "
          f"authority for the derived decisions, and each names the preregistered rule (plan "
          f"amendments A1/A5/A6/A7) it implements. The rung sweeps ONE contiguous admission "
          f"axis — `{INTERIOR_AXIS[0]}` through `{INTERIOR_AXIS[-1]}`, one BF source at refs 3 "
          f"per step — so it is decided by the eight adjacent steps and the eight cumulative "
          f"contrasts, paired per round on `eval + finalize`, under one signed rule "
          f"({INTERIOR['threshold']}/{INTERIOR['rounds']}). Curves are NEVER pooled across "
          f"term orders: the SELECTION runs on `locality` and census is diagnostic only.\n")
    for order in ("locality", "census"):
        interior_emit(sessions[order])

    print("\n### Preregistered decisions (A1)")
    invalid =[order for order in ("locality", "census") if not sessions[order]["sanity"]]
    tripped = [order for order in ("locality", "census") if not sessions[order]["flank"]]
    if invalid:
        print(f"> **SESSION INVALID (A6)** — an anchor outside the R4-frozen ±2 % band in: "
              f"{', '.join(invalid)}. The rule is a soaked repeat, and NO conclusion is emitted "
              f"from this session; the rows above and below are printed for diagnosis only and "
              f"DO NOT STAND.\n")
    if tripped:
        print(f"> **FLANK TRIPPED (A6)** — an anchor lane whose first and last full cycle "
              f"disagree past the scaled threshold in: {', '.join(tripped)}. That session is a "
              f"soaked-repeat candidate; the flank table above names the lane that drifted.\n")
    winner, loser = interior_decisions(sessions["locality"], True)
    interior_decisions(sessions["census"], False)

    print("\n### ncu capture manifest (A7)\n")
    print(f"Deduplicated {{`{INTERIOR_AXIS[0]}`, the locality winner, the locality first "
          f"loser, `{INTERIOR_AXIS[-1]}`}}, each under BOTH term orders (amendment A7). A7's "
          f"fallback {{`{INTERIOR_AXIS[0]}`, `k20@128`, `{INTERIOR_AXIS[-1]}`}} applies when "
          f"the sweep locates NEITHER a first loser nor a winner: with no signed decision on "
          f"the axis the mechanism question is about its middle, not about a boundary nothing "
          f"found. A winner without a first loser IS the decision, so it is profiled. Task 3 "
          f"consumes this block as AUTHORITATIVE and does not reconstruct it.\n")
    roles = defaultdict(set)
    roles[INTERIOR_AXIS[0]].add("incumbent")
    roles[INTERIOR_AXIS[-1]].add("censoring-endpoint")
    if loser is not None:
        roles[loser].add("first-loser")
    if winner is not None:
        roles[winner].add("winner")
    elif loser is None:
        roles["k20@128"].add("axis-midpoint")
    if invalid:
        print(f"**NOT AUTHORITATIVE**: {', '.join(invalid)} is invalid under A6, so this "
              f"session selects no capture set. Repeat the session soaked and re-emit.")
        sys.exit(f"{R8}: session invalid — {', '.join(invalid)} carries an anchor outside the "
                 f"R4-frozen ±2 % band (A6); repeat it soaked, and do not record conclusions "
                 f"from this log set")
    print("```")
    for lane in sorted(roles, key=lambda x: LANE_K[x]):
        print(f"NCU-CAPTURE lane={lane} orders=census,locality "
              f"roles={','.join(sorted(roles[lane]))}")
    print("```")


def interior(orders, runs, arms, done, sched, where, narrowed):
    if narrowed:
        sys.exit(f"{where}: the {R8} path is preregistered on BOTH term orders (A5), so "
                 f"`--order` cannot narrow it — emit the two session logs together")
    if set(orders) != {"census", "locality"}:
        sys.exit(f"{where}: the {R8} rung is preregistered on EXACTLY both term orders (census "
                 f"and locality); this log set carries {', '.join(orders) or 'none'} — a "
                 f"one-order log set decides nothing (A5)")
    sessions = {}
    for order in ("locality", "census"):
        key = (R8, order)
        sessions[order] = interior_session(key, runs[key], arms.get(key, {}), done.get(key),
                                          sched.get(key))
    interior_report(sessions)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("log", nargs="+")
    ap.add_argument("--order", help="emit only this term order")
    args = ap.parse_args()
    where = ", ".join(args.log)
    runs, arms, done, sched = parse(args.log, where)
    keys = set(runs) | set(sched)
    tags = {tag for tag, _ in keys}
    if not keys:
        sys.exit(f"{where}: no SAMPLE lines and no `<ROTATION> schedule` line")
    # The two grammars are summarized under different preregistered rules, so a log set
    # carrying both is rejected rather than emitted under one of them.
    if R4 in tags and tags & set(FRONTIER):
        sys.exit(f"{where}: carries both {R4} and frontier sections — they are summarized "
                 f"under different preregistered rules; emit them separately")
    if tags - KNOWN:
        sys.exit(f"{where}: unknown rotation keyword(s) {sorted(tags - KNOWN)}")
    # The interior rung is decided under its own rules (amendment A2), so it is emitted alone.
    if R8 in tags and tags - {R8}:
        sys.exit(f"{where}: carries {R8} and {sorted(tags - {R8})} — the interior rung is "
                 f"decided under its own preregistered rules; emit it separately")

    # A DECLARED order is emitted or it is an error. Iterating the orders that happen to
    # carry SAMPLE rows silently drops a section whose samples were truncated away, and
    # `--order X` against a log without X used to exit 0 with no output at all.
    orders = sorted({o for _, o in keys}, key=lambda o: (o != "locality", o))
    if args.order:
        if args.order not in orders:
            sys.exit(f"{where}: no `{args.order}` section — the log carries "
                     f"{', '.join(orders)}")
        orders = [args.order]

    if R8 in tags:
        interior(orders, runs, arms, done, sched, where, args.order)
        return
    if R4 in tags:
        for order in orders:
            key = (R4, order)
            emit(order, runs[key], arms.get(key, {}), done.get(key), sched.get(key))
        return
    frontier(orders, sorted(tags), runs, arms, done, sched, where)


if __name__ == "__main__":
    main()
