#!/usr/bin/env python3
"""Emit the v3 R3 factorial table from a `--factorial` run log.

Everything here is PAIRED per round: the runner executes all five arms inside one round,
in a cyclic rotation, so a round's arms share whatever clock state that round had. Taking
the contrast round-by-round and then summarizing removes the ~1 %/session drift that would
otherwise swamp effects of this size. Per-arm medians are reported too, but the contrasts
are the measurement.

Spread is the INTERQUARTILE RANGE of the paired per-round differences (not a CI): no RNG,
no distributional assumption, and it answers the question that matters — whether the
contrast's sign is stable across rounds.

Usage:
    python3 gpu/gkr_uniskip_bench/tools/factorial_table.py /tmp/factorial.log [--order locality]
"""

import argparse
import re
import sys
from collections import defaultdict
from statistics import median

SAMPLE = re.compile(r"^SAMPLE (\S+) (\d+) (\S+) ([\d.]+) ([\d.]+)$")
DONE = re.compile(r"^FACTORIAL done order=(\S+) warmup=(\d+) rounds=(\d+) arms=(\d+)$")

# Compiled registers / blocks per SM on sm_120, from the Task 1 gate (8-register
# allocation granularity). w and wnone are over the 80-register cliff.
OCC = {"control": (72, 3), "t": (79, 3), "w": (82, 2), "wt": (80, 3), "wnone": (82, 2)}
REMOVED = 47  # productions the top-4 window skips per warp-program walk


def parse(path):
    """{order: {round: {arm: eval+finalize ms}}}, plus the trailer per order."""
    runs, done = defaultdict(lambda: defaultdict(dict)), {}
    for line in open(path):
        m = SAMPLE.match(line.strip())
        if m:
            order, rnd, arm, ev, fin = m.groups()
            runs[order][int(rnd)][arm] = float(ev) + float(fin)
            continue
        m = DONE.match(line.strip())
        if m:
            done[m.group(1)] = (int(m.group(2)), int(m.group(3)), int(m.group(4)))
    return runs, done


def iqr(xs):
    s = sorted(xs)
    n = len(s)
    return s[n // 4], s[(3 * n) // 4]


def emit(order, rounds, trailer):
    arms = ["control", "t", "w", "wt", "wnone"]
    # SAME-SESSION GUARD: every round must carry every arm, or the pairing is a fiction.
    complete = {r: v for r, v in rounds.items() if all(a in v for a in arms)}
    dropped = len(rounds) - len(complete)
    if not complete:
        sys.exit(f"{order}: no complete rounds")
    if trailer and len(complete) != trailer[1]:
        print(
            f"note: {order}: {len(complete)} complete rounds, trailer claims {trailer[1]}",
            file=sys.stderr,
        )
    if dropped:
        print(f"note: {order}: dropped {dropped} incomplete rounds", file=sys.stderr)

    print(f"#### `--term-order {order}` — {len(complete)} paired rounds, 5 arms per round\n")
    print("| arm | regs | blocks/SM | median `eval + finalize` (ms) | min | max |")
    print("| --- | --- | --- | --- | --- | --- |")
    med = {}
    for a in arms:
        xs = [complete[r][a] for r in sorted(complete)]
        med[a] = median(xs)
        regs, blocks = OCC[a]
        print(f"| `{a}` | {regs} | {blocks} | **{med[a]:.3f}** | {min(xs):.3f} | {max(xs):.3f} |")

    print("\n| paired contrast | median (ms) | IQR (ms) | median (%) | rounds with this sign | occupancy |")
    print("| --- | --- | --- | --- | --- | --- |")
    labels = {
        "t": ("`t` − `control`", "3 v 3 — occupancy-neutral"),
        "w": ("`w` − `control`", "**2 v 3 — NOT occupancy-neutral**"),
        "wt": ("`wt` − `control`", "3 v 3 — occupancy-neutral"),
        "wnone": ("`wnone` − `control`", "**2 v 3 — NOT occupancy-neutral**"),
    }
    for a in ["t", "w", "wt", "wnone"]:
        d = [complete[r][a] - complete[r]["control"] for r in sorted(complete)]
        m = median(d)
        lo, hi = iqr(d)
        same = sum(1 for x in d if (x < 0) == (m < 0))
        name, occ = labels[a]
        print(
            f"| {name} | **{m:+.3f}** | {lo:+.3f} … {hi:+.3f} | {100 * m / med['control']:+.2f} % "
            f"| {same}/{len(d)} | {occ} |"
        )
    # The two clean window contrasts the Task 1 review pinned.
    for name, a, b, occ in [
        ("`wt` − `t`", "wt", "t", "3 v 3 — the window at fixed occupancy"),
        ("`w` − `wnone`", "w", "wnone", "2 v 2 — the SCHEDULE alone, identical kernel"),
    ]:
        d = [complete[r][a] - complete[r][b] for r in sorted(complete)]
        m = median(d)
        lo, hi = iqr(d)
        same = sum(1 for x in d if (x < 0) == (m < 0))
        print(
            f"| {name} | **{m:+.3f}** | {lo:+.3f} … {hi:+.3f} | {100 * m / med[b]:+.2f} % "
            f"| {same}/{len(d)} | {occ} |"
        )

    inter = [
        complete[r]["wt"] - complete[r]["w"] - complete[r]["t"] + complete[r]["control"]
        for r in sorted(complete)
    ]
    lo, hi = iqr(inter)
    print(
        f"\n**Factorial interaction** `wt − w − t + control` = **{median(inter):+.3f} ms** "
        f"(IQR {lo:+.3f} … {hi:+.3f}). Zero means the two effects are additive; the sign says "
        f"which way they interfere. Note it mixes occupancy classes — `w` and `wt` differ by "
        f"one block/SM as well as by the launch bound."
    )

    net = [(complete[r]["control"] - complete[r]["w"]) / REMOVED for r in sorted(complete)]
    gross = [(complete[r]["wnone"] - complete[r]["w"]) / REMOVED for r in sorted(complete)]
    print(
        f"\n**Slopes over {REMOVED} removed productions** (rung-2 calibration; neither is "
        f"\"the\" production cost):\n"
        f"- net W=4 slope `(control − w)/{REMOVED}` = **{1000 * median(net):+.2f} µs/production** "
        f"— carries the 3→2 block change with it\n"
        f"- gross removal slope `(wnone − w)/{REMOVED}` = **{1000 * median(gross):+.2f} µs/production** "
        f"— same kernel and occupancy on both sides, so this is the removal alone\n"
    )


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("log")
    ap.add_argument("--order", help="emit only this term order")
    args = ap.parse_args()
    runs, done = parse(args.log)
    if not runs:
        sys.exit(f"{args.log}: no SAMPLE lines")
    for order in sorted(runs, key=lambda o: (o != "locality", o)):
        if args.order and order != args.order:
            continue
        emit(order, runs[order], done.get(order))


if __name__ == "__main__":
    main()
