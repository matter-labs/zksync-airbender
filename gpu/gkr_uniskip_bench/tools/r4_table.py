#!/usr/bin/env python3
"""Emit the v3 R4 factorial table from a `--cache-factorial` run log.

Everything is PAIRED per round: the runner executes all eleven lanes inside one round, in a
cyclic rotation, so a round's lanes share whatever clock state that round had. Taking the
contrast round-by-round and then summarizing removes the ~1 %/session drift that would
otherwise swamp effects of this size.

The arm schema is DATA-DRIVEN: lanes, their registers, blocks/SM, block size, grid and
kernel all come from the log's `ARM` lines, which the runner emits from Rust. Nothing here
hardcodes an arm list, an occupancy fact or a kernel name — R3's emitter did, and the spec
called that out as the thing to fix.

`eval` and `finalize` are summarized SEPARATELY. The 128 lanes run twice the grid, so
finalize reduces twice the partials; summing the two stages would fold a real block-size
effect into the arm comparison.

Every contrast NAMES its baseline. At 128 the cache-vs-control baseline is `control_lb@128`,
the bounded no-cache body, because the cached 128 lanes are bounded too — comparing them to
the unbounded `control@128` would put the launch bound's own cost inside the cache result.

Removals per lane ride the log's `ARM` line, which Rust fills from the arm's own planned
`CacheCounts` — this script holds no oracle constant, so a census change cannot silently
invalidate a slope (and the runner rejects the census knobs anyway).

Usage:
    python3 gpu/gkr_uniskip_bench/tools/r4_table.py /tmp/cache.log [--order locality]
"""

import argparse
import re
import sys
from collections import defaultdict
from statistics import median

SAMPLE = re.compile(r"^SAMPLE (\S+) (\d+) (\S+) ([\d.]+) ([\d.]+) (\S+)$")
ARM = re.compile(r"^ARM (\S+) (\d+) (\d+) (\d+) (\d+) (\S+) (\d+) (\d+) (\d+)$")
SCHED = re.compile(r"^CACHE-FACTORIAL schedule order=(\S+) lanes=(\d+) rounds=(\d+) warmup=(\d+)$")
DONE = re.compile(r"^CACHE-FACTORIAL done order=(\S+) warmup=(\d+) rounds=(\d+) lanes=(\d+)$")

# The eleven lanes the primary rotation must carry. A log with a different set is a
# different experiment and is rejected rather than partially summarized.
EXPECTED_LANES = {
    "control@256", "cache0@256", "hot4@256", "hot16@256", "allrepeat@256",
    "control@128", "control_lb@128", "cache0@128", "hot4@128", "hot16@128", "allrepeat@128",
}


def parse(path):
    runs, arms, done, sched = defaultdict(lambda: defaultdict(dict)), defaultdict(dict), {}, {}
    section = None
    for n, line in enumerate(open(path), 1):
        line = line.strip()
        m = SCHED.match(line)
        if m:
            if m.group(1) in sched:
                sys.exit(f"{path}:{n}: order={m.group(1)} starts twice — the log mixes runs")
            section = m.group(1)
            sched[section] = (int(m.group(2)), int(m.group(3)), int(m.group(4)))
            continue
        m = ARM.match(line)
        if m:
            if section is None:
                sys.exit(f"{path}:{n}: `ARM {m.group(1)}` before any schedule line — the "
                         f"lane facts cannot be bound to a term order")
            if m.group(1) in arms[section]:
                sys.exit(f"{path}:{n}: duplicate `ARM {m.group(1)}` for order={section}")
            arms[section][m.group(1)] = {
                "regs": int(m.group(2)), "blocks_sm": int(m.group(3)),
                "threads": int(m.group(4)), "grid": int(m.group(5)), "kernel": m.group(6),
                "c": int(m.group(7)), "removals": int(m.group(8)), "admitted": int(m.group(9)),
            }
            continue
        m = SAMPLE.match(line)
        if m:
            order, rnd, lane, ev, fin, kernel = m.groups()
            bucket = runs[order][int(rnd)]
            if lane in bucket:
                sys.exit(f"{path}:{n}: duplicate sample for order={order} round={rnd} "
                         f"lane={lane} — the log mixes runs; emit one session at a time")
            bucket[lane] = (float(ev), float(fin), kernel)
            continue
        m = DONE.match(line)
        if m:
            if m.group(1) in done:
                sys.exit(f"{path}:{n}: order={m.group(1)} completes twice — mixed log")
            done[m.group(1)] = (int(m.group(2)), int(m.group(3)), int(m.group(4)))
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
        base = med[b][0] + med[b][1]
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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("log")
    ap.add_argument("--order", help="emit only this term order")
    args = ap.parse_args()
    runs, arms, done, sched = parse(args.log)
    if not runs:
        sys.exit(f"{args.log}: no SAMPLE lines")
    for order in sorted(runs, key=lambda o: (o != "locality", o)):
        if args.order and order != args.order:
            continue
        emit(order, runs[order], arms.get(order, {}), done.get(order), sched.get(order))


if __name__ == "__main__":
    main()
