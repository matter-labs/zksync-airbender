#!/usr/bin/env python3
"""Emit the v3 R3 factorial table from a `--factorial` run log.

Everything here is PAIRED per round: the runner executes every arm inside one round,
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
ARM = re.compile(r"^ARM (\S+) (\d+) (\d+)$")
SCHEDULE = re.compile(r"^FACTORIAL schedule order=(\S+) ")

REMOVED = 47  # productions the top-4 window skips per warp-program walk


def parse(path):
    """{order: {round: {arm: ms}}}, the trailer per order, and the arm occupancy facts.

    Duplicate (order, round, arm) samples are a HARD ERROR: two runs concatenated into one
    log would otherwise overwrite each other silently and still report a full set of paired
    rounds, with medians drawn from two different sessions.
    """
    runs, done = defaultdict(lambda: defaultdict(dict)), {}
    occ, section = defaultdict(dict), None
    for n, line in enumerate(open(path), 1):
        m = SCHEDULE.match(line.strip())
        if m:
            section = m.group(1)
            continue
        m = SAMPLE.match(line.strip())
        if m:
            order, rnd, arm, ev, fin = m.groups()
            bucket = runs[order][int(rnd)]
            if arm in bucket:
                sys.exit(
                    f"{path}:{n}: duplicate sample for order={order} round={rnd} arm={arm} "
                    f"— the log mixes runs; emit one session at a time"
                )
            bucket[arm] = float(ev) + float(fin)
            continue
        m = ARM.match(line.strip())
        if m:
            if section is None:
                sys.exit(
                    f"{path}:{n}: `ARM {m.group(1)}` before any `FACTORIAL schedule` line "
                    f"— occupancy metadata cannot be bound to a term order"
                )
            if m.group(1) in occ[section]:
                sys.exit(
                    f"{path}:{n}: duplicate `ARM {m.group(1)}` for order={section} "
                    f"— the log mixes runs"
                )
            occ[section][m.group(1)] = (int(m.group(2)), int(m.group(3)))
            continue
        m = DONE.match(line.strip())
        if m:
            if m.group(1) in done:
                sys.exit(f"{path}:{n}: order={m.group(1)} completes twice — mixed log")
            done[m.group(1)] = (int(m.group(2)), int(m.group(3)), int(m.group(4)))
    return runs, done, occ


def iqr(xs):
    s = sorted(xs)
    n = len(s)
    return s[n // 4], s[(3 * n) // 4]


def emit(order, rounds, trailer, occ):
    # occ and trailer are this ORDER's own: metadata never borrows across orders, so a log
    # that lost one order's ARM block or its trailer fails instead of being papered over
    # with the other order's facts.
    if not occ:
        sys.exit(
            f"{order}: no ARM lines for this order. Either this is an old-format run "
            f"(re-run with a build that emits `ARM <name> <regs> <blocks>`) or the log is "
            f"truncated — the table would otherwise be written with no occupancy labels."
        )
    if trailer is None:
        sys.exit(
            f"{order}: no `FACTORIAL done order={order} …` trailer — the run did not "
            f"finish, or the log is truncated; round and arm counts cannot be checked"
        )
    arms = [a for a in ["control", "t", "w", "wt", "wnone", "wtnone"] if a in occ]
    unknown = sorted(set(occ) - set(arms))
    if unknown:
        sys.exit(f"{order}: ARM lines name arms this emitter does not know: {unknown}")
    # SAME-SESSION GUARD, all hard errors: the pairing is a fiction unless every round
    # carries exactly the declared arm set, and a partial log must not be summarized as
    # though it were whole.
    if len(arms) != trailer[2]:
        sys.exit(
            f"{order}: {len(arms)} ARM lines but the trailer declares arms={trailer[2]} "
            f"— the log is truncated or mixes builds"
        )
    for r in sorted(rounds):
        got = set(rounds[r])
        if got != set(arms):
            sys.exit(
                f"{order}: round {r} carries {sorted(got)}, expected {arms} "
                f"— incomplete rounds are not droppable, the contrasts are paired"
            )
    complete = rounds
    if not complete:
        sys.exit(f"{order}: no complete rounds")
    if len(complete) != trailer[1]:
        sys.exit(
            f"{order}: {len(complete)} rounds in the log, trailer claims rounds="
            f"{trailer[1]} — truncated log"
        )

    print(f"#### `--term-order {order}` — {len(complete)} paired rounds, {len(arms)} arms per round\n")
    print("| arm | regs | blocks/SM | median `eval + finalize` (ms) | min | max |")
    print("| --- | --- | --- | --- | --- | --- |")
    med = {}
    for a in arms:
        xs = [complete[r][a] for r in sorted(complete)]
        med[a] = median(xs)
        regs, blocks = occ[a]
        print(f"| `{a}` | {regs} | {blocks} | **{med[a]:.3f}** | {min(xs):.3f} | {max(xs):.3f} |")

    print(
        "\n**Percentages are of the contrast's OWN baseline** — the second term of the "
        "subtraction, named in each row — not of `control`. `w` − `wnone` at −5.3 % is "
        "−5.3 % of `wnone`; against `control` the same millisecond figure is a larger "
        "fraction.\n"
    )
    print("| paired contrast | median (ms) | IQR (ms) | median (% of baseline) | baseline | rounds with this sign | occupancy |")
    print("| --- | --- | --- | --- | --- | --- | --- |")
    labels = {
        "t": ("`t` − `control`", "3 v 3 — occupancy-neutral"),
        "w": ("`w` − `control`", "**2 v 3 — NOT occupancy-neutral**"),
        "wt": ("`wt` − `control`", "3 v 3 — occupancy-neutral"),
        "wnone": ("`wnone` − `control`", "**2 v 3 — NOT occupancy-neutral**"),
        "wtnone": ("`wtnone` − `control`", "3 v 3 — occupancy-neutral"),
    }
    for a in [a for a in ["t", "w", "wt", "wnone", "wtnone"] if a in med]:
        d = [complete[r][a] - complete[r]["control"] for r in sorted(complete)]
        m = median(d)
        lo, hi = iqr(d)
        same = sum(1 for x in d if (x < 0) == (m < 0))
        name, label = labels[a]
        print(
            f"| {name} | **{m:+.3f}** | {lo:+.3f} … {hi:+.3f} | {100 * m / med['control']:+.2f} % "
            f"| `control` | {same}/{len(d)} | {label} |"
        )
    # The two clean window contrasts the Task 1 review pinned.
    clean = [
        ("`wt` − `t`", "wt", "t", "3 v 3 — machinery + removal together"),
        ("`w` − `wnone`", "w", "wnone", "2 v 2 — the SCHEDULE alone, identical kernel"),
    ]
    if "wtnone" in med:
        clean += [
            ("`wtnone` − `t`", "wtnone", "t", "3 v 3 — the MACHINERY alone"),
            ("`wt` − `wtnone`", "wt", "wtnone", "3 v 3 — the REMOVAL alone, at 3 blocks"),
        ]
    for name, a, b, label in clean:
        d = [complete[r][a] - complete[r][b] for r in sorted(complete)]
        m = median(d)
        lo, hi = iqr(d)
        same = sum(1 for x in d if (x < 0) == (m < 0))
        print(
            f"| {name} | **{m:+.3f}** | {lo:+.3f} … {hi:+.3f} | {100 * m / med[b]:+.2f} % "
            f"| `{b}` | {same}/{len(d)} | {label} |"
        )

    if "wtnone" in med:
        # The decomposition must close: machinery + removal = the pair it was split from.
        mach = median([complete[r]["wtnone"] - complete[r]["t"] for r in sorted(complete)])
        rem = median([complete[r]["wt"] - complete[r]["wtnone"] for r in sorted(complete)])
        both = median([complete[r]["wt"] - complete[r]["t"] for r in sorted(complete)])
        print(
            f"\n**Decomposition check** (`wtnone` − `t`) + (`wt` − `wtnone`) = "
            f"{mach:+.3f} {rem:+.3f} = **{mach + rem:+.3f}** against `wt` − `t` = "
            f"**{both:+.3f}** — medians are not exactly additive, so a small residual is "
            f"expected; the per-round identity is exact by construction."
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
        f"\n**Slopes over {REMOVED} removed productions** (rung-2 calibration; none of these "
        f"is \"the\" production cost):\n"
        f"- net W=4 slope `(control − w)/{REMOVED}` = **{1000 * median(net):+.2f} µs/production** "
        f"— carries the 3→2 block change with it\n"
        f"- gross removal slope at 2 blocks `(wnone − w)/{REMOVED}` = "
        f"**{1000 * median(gross):+.2f} µs/production** — same kernel and occupancy on both "
        f"sides, so this is the removal alone, but in a carrier that costs a block\n"
    )
    if "wtnone" in med:
        three = [
            (complete[r]["wtnone"] - complete[r]["wt"]) / REMOVED for r in sorted(complete)
        ]
        print(
            f"- **removal slope at 3 blocks** `(wtnone − wt)/{REMOVED}` = "
            f"**{1000 * median(three):+.2f} µs/production** — the same removal in a carrier "
            f"that keeps the control's occupancy. This is the shippable figure; the 2-block "
            f"slope above overstates it.\n"
        )


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("log")
    ap.add_argument("--order", help="emit only this term order")
    args = ap.parse_args()
    runs, done, occ = parse(args.log)
    if not runs:
        sys.exit(f"{args.log}: no SAMPLE lines")
    for order in sorted(runs, key=lambda o: (o != "locality", o)):
        if args.order and order != args.order:
            continue
        emit(order, runs[order], done.get(order), occ.get(order, {}))


if __name__ == "__main__":
    main()
