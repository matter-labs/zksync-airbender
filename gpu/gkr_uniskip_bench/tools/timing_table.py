#!/usr/bin/env python3
"""Emit `iteration_times.md`'s stage table from a run log, instead of transcribing it.

Hand-assembling those tables cost two review rounds on the v3 R1 record — once a pasted
row made two arms byte-identical, once a stale row survived under a header claiming
re-measurement. The fix is mechanical: capture the runs, emit the markdown.

Usage:

    # capture: one session, one build, one `=== MODE=<mode> ORDER=<order>` header per run
    .agents/bin/with_gpu_lock.sh bash -c '
      B=target/release/gpu_gkr_uniskip_bench
      for spec in "lsb-pair census" "lsb-pair locality" \\
                  "lsb-recompute census" "lsb-recompute locality"; do
        set -- $spec
        echo "=== MODE=$1 ORDER=$2"
        $B --log-trace 24 --warmup 10 --iterations 100 --mode $1 --term-order $2
      done' > /tmp/runlog.txt

    # emit
    python3 gpu/gkr_uniskip_bench/tools/timing_table.py /tmp/runlog.txt \\
        --control lsb-recompute --bar census=20.713 --bar locality=20.596

The control arm's own `eval + finalize` is the "vs same-session control" denominator, so
a table can never quietly mix sessions: an arm with no control row in the same log prints
`n/a` rather than borrowing a number from elsewhere.
"""

import argparse
import re
import sys

HEADER = re.compile(r"===\s*MODE=(\S+)\s+ORDER=(\S+)")
STAGE = re.compile(r"^\s+(eval|finalize)\s+([\d.]+)\s+([\d.]+)\s+([\d.]+)\s+([\d.]+)")


def parse(path):
    """[(mode, order, {stage: (median, min, max)})] in log order."""
    runs, mode, order, cur = [], None, None, {}
    for line in open(path):
        head = HEADER.search(line)
        if head:
            if mode is not None and cur:
                runs.append((mode, order, cur))
            mode, order, cur = head.group(1), head.group(2), {}
            continue
        stage = STAGE.match(line)
        if stage and mode is not None:
            cur[stage.group(1)] = (
                float(stage.group(2)),
                float(stage.group(4)),
                float(stage.group(5)),
            )
    if mode is not None and cur:
        runs.append((mode, order, cur))
    return runs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("log")
    ap.add_argument("--control", help="mode whose rows are the same-session denominator")
    ap.add_argument(
        "--bar",
        action="append",
        default=[],
        metavar="ORDER=MS",
        help="recorded bar per term order",
    )
    args = ap.parse_args()

    bars = dict(b.split("=", 1) for b in args.bar)
    bars = {k: float(v) for k, v in bars.items()}
    runs = parse(args.log)
    if not runs:
        sys.exit(f"{args.log}: no '=== MODE=… ORDER=…' runs found")

    seen, control = set(), {}
    for mode, order, st in runs:
        if (mode, order) in seen:
            print(f"note: {mode} {order} appears more than once; all occurrences listed", file=sys.stderr)
        seen.add((mode, order))
        if mode == args.control and "eval" in st and "finalize" in st:
            control[order] = st["eval"][0] + st["finalize"][0]

    print(
        "| arm | `eval` | `finalize` | **eval + finalize** | vs recorded bar "
        "| vs same-session control | spread (`eval` min-max) |"
    )
    print("| --- | --- | --- | --- | --- | --- | --- |")
    for mode, order, st in runs:
        if "eval" not in st or "finalize" not in st:
            print(f"note: {mode} {order} has no stage rows; skipped", file=sys.stderr)
            continue
        total = st["eval"][0] + st["finalize"][0]
        bar = bars.get(order)
        ctl = control.get(order)
        vs_bar = f"{(total / bar - 1) * 100:+.1f} %" if bar else "n/a"
        if mode == args.control:
            vs_ctl = "—"
        elif ctl:
            vs_ctl = f"**{(total / ctl - 1) * 100:+.1f} %**"
        else:
            vs_ctl = "n/a"
        tag = " (control)" if mode == args.control else ""
        print(
            f"| `{mode}` {order} | {st['eval'][0]:.3f} | {st['finalize'][0]:.3f} "
            f"| **{total:.3f}**{tag} | {vs_bar} | {vs_ctl} "
            f"| {st['eval'][1]:.3f}–{st['eval'][2]:.3f} |"
        )


if __name__ == "__main__":
    main()
