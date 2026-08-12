#!/usr/bin/env python3
"""Generate the v3 R9 gate-first-reorder fixture sessions into a directory.

    python3 gpu/gkr_uniskip_bench/tools/r9_fixtures/make_fixtures.py <outdir>

Deterministic — no randomness, so a regenerated fixture is byte-identical. `check.sh`
generates into a `mktemp -d` at run time and removes it afterwards: the fixtures are DERIVED
data, so the tracked tree carries the generator that documents them, not the logs.

The grammar is the runner's (`main.rs` / `harness.rs`): the per-symbol applied-carveout echoes
and the `carveout symbols` set line, a `REORDER schedule` line, one frontier `ARM` line per lane
with its ordered admitted-id list, one `SAMPLE` per (round, lane) in the cyclic rotation
`slot = (round + offset) % lanes`, and the `done` trailer. The lane FACTS are the REAL ones —
the six lanes' registers, blocks/SM, bodies, C, removals and admitted prefixes as the shipped
binary publishes them, and the grids the arms take at `--log-trace 24` (r7_gates.sh's `r9` lane
gates those same lines against a live short rotation). Only the SAMPLE magnitudes are synthetic:
these fixtures pin the emitter's grammar, arithmetic and decision surface, and predict nothing.

Every conforming session is the preregistered shape: both term orders, 96 rounds, 6 warmup,
6 lanes = 16 full cycles. Mutants are generated fully SELF-CONSISTENT so each one fails on the
gate it is named for and not on a side effect.
"""

import os
import re
import sys
import zlib

CACHED = "eval_lsb_pair_cached_128_lb"
REORDER_LB = "eval_lsb_pair_cached_reorder_128_lb"
REORDER_FREE = "eval_lsb_pair_cached_reorder_128"
PAIR_LB = "eval_lsb_pair_128_lb"
PAIR = "eval_lsb_pair"
TAG = "REORDER"
CTL = "control@256"
CTL_LB = "control_lb@128"
HOT = "hot16@128"
BOUNDED = "reorder-hot16@128"
FLOOR = "reorder-cache0@128"
FREE = "reorder-hot16-free@128"
ROUNDS, WARMUP = 96, 6
ORDERS = ("locality", "census")

# The rotation in execution order (`REORDER` in `src/coset_cache.rs`).
LANES = [CTL, CTL_LB, HOT, BOUNDED, FLOOR, FREE]

# The hinted LOCAL symbols, in the order the harness echoes them (`LaneKernel::HINTED`), all at
# the shipped default percent — the rotation rejects `--carveout-hint`, so 16 is the only
# configuration this rung's headline contrast is ever taken at.
HINTED = [CACHED, REORDER_LB, REORDER_FREE]
HINT = 16

# lane -> (regs, blocks/SM, threads, grid, kernel, C, removals, admitted). The three cached
# lanes at hot16's plan carry the SAME C / removals / admitted set: one plan on three bodies is
# what the rung contrasts.
FACTS = {
    CTL: (72, 3, 256, 32768, PAIR, 0, 0, 0),
    CTL_LB: (72, 7, 128, 65536, PAIR_LB, 0, 0, 0),
    HOT: (72, 7, 128, 65536, CACHED, 28, 145, 16),
    BOUNDED: (70, 7, 128, 65536, REORDER_LB, 28, 145, 16),
    FLOOR: (70, 7, 128, 65536, REORDER_LB, 0, 0, 0),
    FREE: (64, 8, 128, 65536, REORDER_FREE, 28, 145, 16),
}

# The canonical admission ordering (`oracle-derivation.txt`, identical under both orders); a
# lane's admitted-id list is its first-K prefix IN THIS ORDER.
ORACLE = ([0, 1, 2, 3, 4, 5] + [48, 49, 50, 51] + list(range(6, 41))
          + [52, 53, 54, 55, 56, 57, 58] + [41, 42, 43])

# The anchor lanes' `eval + finalize` targets: R4's frozen medians for `control@256` and
# `hot16@128` (the emitter's HARD band), R5's base for `control_lb@128`, and the R5 cache0
# machinery floor for the reordered one. A conforming session lands IN band by construction, so a
# fixture that reports OUT means the band moved.
BASE = {
    "locality": {CTL: 16.624, HOT: 14.836, CTL_LB: 16.406, FLOOR: 17.071},
    "census": {CTL: 16.545, HOT: 15.129, CTL_LB: 16.219, FLOOR: 16.884},
}
# The finalize stage, held per block size: the 128 lanes reduce twice the partials.
FIN = {lane: (0.033 if FACTS[lane][2] == 256 else 0.063) for lane in LANES}

FIELDS = ("regs", "blocks", "threads", "grid", "kernel", "c", "removals", "admitted")


def facts_of(lane, patch=None):
    f = dict(zip(FIELDS, FACTS[lane]))
    f["ids"] = ORACLE[:f["admitted"]]
    f.update((patch or {}).get(lane, {}))
    return f


def arm_line(lane, patch=None):
    f = facts_of(lane, patch)
    ids = ",".join(str(i) for i in f["ids"]) if f["ids"] else "-"
    return (f"ARM {lane} {f['regs']} {f['blocks']} {f['threads']} {f['grid']} {f['kernel']} "
            f"{f['c']} {f['removals']} {f['admitted']} {ids}")


def preamble(echoes=None, symbols=True, count=None, extra=None):
    """The harness's carveout block: one applied-hint echo per hinted local symbol, then the
    set line. `echoes` is a list of (percent, symbol) pairs; `symbols` names the set line's
    list, or False to omit it. The indentation is part of the runner's literal."""
    echoes = [(HINT, sym) for sym in HINTED] if echoes is None else echoes
    out = [f"  carveout hint       {pct}% ({sym})" for pct, sym in echoes]
    if symbols:
        names = [sym for _, sym in echoes] if symbols is True else symbols
        n = len(names) if count is None else count
        out.append(f"  carveout symbols    {n} local ({', '.join(names)})")
    return out + list(extra or [])


def jitter(lane, i, amp):
    """Deterministic, zero-mean-ish wobble; `amp` is the half-width in ms. `crc32`, not
    `hash`, so a regenerated fixture does not depend on PYTHONHASHSEED."""
    h = (zlib.crc32(f"{lane}#{i}".encode()) & 0xFFFF) / 0xFFFF
    return (2.0 * h - 1.0) * amp


def flat(lane, mean, rounds=ROUNDS, amp=0.02):
    return [mean + jitter(lane, i, amp) for i in range(rounds)]


def series(order, offsets, rounds=ROUNDS, override=None):
    """Every lane's `eval + finalize` per round: the four anchors at their bases, the lanes in
    `offsets` at `hot16 + offset`, and any lane in `override` taken verbatim."""
    s = {lane: flat(lane, BASE[order][lane], rounds) for lane in BASE[order]}
    for lane, off in offsets.items():
        s[lane] = flat(lane, BASE[order][HOT] + off, rounds)
    s.update(override or {})
    return s


def log(order, s, rounds=ROUNDS, warmup=WARMUP, tag=TAG, lanes=None, patch=None, fixed=False,
        head=None):
    lanes = lanes or LANES
    n = len(lanes)
    out = list(preamble()) if head is None else list(head)
    out.append(f"{tag} schedule order={order} lanes={n} rounds={rounds} warmup={warmup}")
    out += [arm_line(lane, patch) for lane in lanes]
    for i in range(rounds):
        index = warmup + i
        for offset in range(n):
            lane = lanes[offset if fixed else (index + offset) % n]
            fin = FIN[lane]
            kernel = facts_of(lane, patch)["kernel"]
            out.append(f"SAMPLE {order} {index} {lane} {s[lane][i] - fin:.6f} {fin:.6f} "
                       f"{kernel}")
    out.append(f"{tag} done order={order} warmup={warmup} rounds={rounds} lanes={n}")
    return "\n".join(out) + "\n"


def write(outdir, name, text):
    with open(os.path.join(outdir, name), "w") as fh:
        fh.write(text)


def session(outdir, name, offsets, **kw):
    """One fixture SESSION: the two logs the emitter requires, one per term order. `offsets`
    is per order so a fixture can give the two orders different shapes — which is how the
    both-orders gate is testable at all."""
    over = {order: kw.pop(f"override_{order}", None) for order in ORDERS}
    for order in ORDERS:
        write(outdir, f"{name}-{order}.log",
              log(order, series(order, offsets[order], kw.get("rounds", ROUNDS), over[order]),
                  **kw))


def mutate(outdir, src, dst, fn):
    with open(os.path.join(outdir, src)) as fh:
        text = fh.read()
    write(outdir, dst, fn(text))


def shift(win, free):
    """One order's offsets off `hot16`: the bounded reorder body at `win` and the unbounded one at
    `free`. The reordered machinery floor rides its own base, above the bound-matched control."""
    return {BOUNDED: win, FREE: free}


def main():
    outdir = sys.argv[1]
    os.makedirs(outdir, exist_ok=True)

    # THE CONFORMING SESSION. The bounded reorder body wins in both orders and the unbounded one
    # wins by more, so the verdict row clears its wash-or-better gate, the envelope row is a WIN,
    # and the register cut selects the R10-funding cell of the outcome matrix.
    good = {"locality": shift(-0.200, -0.350), "census": shift(-0.150, -0.300)}
    session(outdir, "good", good)

    # EDGE: the verdict row is a WASH — the preregistered gate is wash-OR-BETTER, so this still
    # funds R10 on the register cut, and that is the cell most easily got wrong.
    over, offs = {}, {}
    for order in ORDERS:
        over[f"override_{order}"] = {BOUNDED: flat(BOUNDED, BASE[order][HOT], ROUNDS, 0.20)}
        offs[order] = shift(0.0, -0.350)
    session(outdir, "verdict-wash", offs, **over)

    # EDGE: the verdict row is a LOSS in both orders — the gate fails, and the register cut does
    # not rescue it.
    session(outdir, "verdict-loss",
            {order: shift(+0.250, -0.100) for order in ORDERS})

    # EDGE: a WIN in locality and a LOSS in census. The gate is preregistered on BOTH orders, so
    # one order's win cannot carry it.
    session(outdir, "verdict-split",
            {"locality": shift(-0.200, -0.350), "census": shift(+0.250, -0.100)})

    # EDGE: the reorder bodies at the INCUMBENT's register count, verdict row a WIN. The static
    # REG facts come off the ARM lines, so this selects the performance-only cell — a time win
    # that does not fund R10.
    same_regs = {BOUNDED: {"regs": 72}, FLOOR: {"regs": 72}, FREE: {"regs": 72, "blocks": 7}}
    session(outdir, "regs-unchanged", good, patch=same_regs)

    # EDGE: no register cut and no time win — the matrix's fourth cell, which records nothing.
    session(outdir, "regs-unchanged-loss",
            {order: shift(+0.250, -0.100) for order in ORDERS}, patch=same_regs)

    # EDGE: the signed threshold, at it and one below it, on the VERDICT row. hot16 is held
    # CONSTANT so the reordered body can carry an exact count of negative paired differences.
    for name, neg in (("sign-at-threshold", 87), ("sign-below-threshold", 86)):
        over, offs = {}, {}
        for order in ORDERS:
            h = BASE[order][HOT]
            over[f"override_{order}"] = {
                HOT: [h] * ROUNDS,
                BOUNDED: [h - 0.10] * neg + [h + 0.10] * (ROUNDS - neg),
            }
            offs[order] = shift(0.0, -0.350)
        session(outdir, name, offs, **over)

    # EDGE: the R4-frozen band is the HARD gate — `control@256` 3 % slow invalidates the session,
    # and no capture manifest may be selected from it.
    over = {f"override_{order}": {CTL: flat(CTL, BASE[order][CTL] * 1.03)} for order in ORDERS}
    session(outdir, "anchor-out-of-band", good, **over)

    # EDGE: the flank rule — the incumbent's LAST full cycle drifts 0.3 ms past the scaled
    # threshold while its session median stays in band, which is exactly the case a
    # session-median check cannot see.
    over = {}
    for order in ORDERS:
        s = flat(HOT, BASE[order][HOT])
        over[f"override_{order}"] = {HOT: s[:-6] + [x + 0.30 for x in s[-6:]]}
    session(outdir, "flank-tripped", good, **over)

    # THE LOG CONTRACT, each mutant self-consistent so it fails on its own gate.
    session(outdir, "wrong-warmup", good, warmup=12)
    session(outdir, "wrong-rounds", good, rounds=102)
    session(outdir, "rotation-fixed", good, fixed=True)
    # The trace appears in no log line; the grid is what carries it, so a session recorded at
    # `--log-trace 23` is internally consistent and only the grid pin sees it.
    session(outdir, "wrong-trace", good,
            patch={lane: {"grid": FACTS[lane][3] // 2} for lane in LANES})
    # The reordered lane declaring the INCUMBENT's body: every count is unchanged, and the three
    # cached lanes are one plan on three bodies, so only the per-lane body pin sees it.
    session(outdir, "body-forged", good, patch={BOUNDED: {"kernel": CACHED}})
    # The reordered lane pricing a different plan from the incumbent it is contrasted against. Its
    # admitted set and label still agree, so only the one-plan-three-bodies gate sees it.
    session(outdir, "plan-mismatch", good, patch={BOUNDED: {"c": 29, "removals": 147}})
    # A reversal among two equal-ref sources: every count is unchanged and only the ORDERED list
    # sees it.
    swapped = ORACLE[:16]
    swapped[12], swapped[13] = swapped[13], swapped[12]
    session(outdir, "ids-reversed", good, patch={FREE: {"ids": swapped}})

    # THE CARVEOUT GRAMMAR (Task 2's new log lines). The echo SET is part of the accepted
    # grammar: the rung's whole headline contrast is taken at ONE L1 configuration, so a missing,
    # wrong or spurious echo is a different arm.
    def head_session(name, **kw):
        for order in ORDERS:
            write(outdir, f"{name}-{order}.log",
                  log(order, series(order, good[order]), head=preamble(**kw)))

    head_session("echo-missing", echoes=[(HINT, CACHED), (HINT, REORDER_LB)])
    head_session("echo-wrong-pct",
                 echoes=[(HINT, CACHED), (33, REORDER_LB), (HINT, REORDER_FREE)])
    head_session("echo-extra", echoes=[(HINT, sym) for sym in HINTED + ["eval_lsb_seg_g"]])
    head_session("echo-reordered", echoes=[(HINT, sym) for sym in reversed(HINTED)])
    head_session("echo-duplicated", echoes=[(HINT, sym) for sym in HINTED + [CACHED]])
    head_session("symbols-missing", symbols=False)
    head_session("symbols-count-wrong", count=2)
    head_session("symbols-disagree", symbols=[CACHED, REORDER_LB, "eval_lsb_seg_g"])
    head_session("symbols-twice",
                 extra=[f"  carveout symbols    3 local ({', '.join(HINTED)})"])
    # A `carveout` line that is neither grammar: the strictness check exists so a runner whose
    # echo literal drifts is caught rather than read as an unhinted process.
    head_session("echo-malformed", extra=["  carveout hint       16 % (eval_lsb_pair)"])

    mutate(outdir, "good-locality.log", "wrong-tag-locality.log",
           lambda t: t.replace(TAG, "FRONTIER-INTERIOR"))
    mutate(outdir, "good-census.log", "wrong-tag-census.log",
           lambda t: t.replace(TAG, "FRONTIER-INTERIOR"))
    mutate(outdir, "good-locality.log", "unknown-order-locality.log",
           lambda t: t.replace("locality", "reverse"))
    mutate(outdir, "good-locality.log", "lane-unknown-locality.log",
           lambda t: t.replace(BOUNDED, "reorder-hot17@128"))
    mutate(outdir, "good-locality.log", "arm-without-ids-locality.log",
           lambda t: "\n".join(" ".join(l.split()[:-1]) if l.startswith(f"ARM {HOT} ") else l
                               for l in t.splitlines()) + "\n")
    mutate(outdir, "good-locality.log", "no-trailer-locality.log",
           lambda t: "\n".join(l for l in t.splitlines()
                               if not l.startswith(f"{TAG} done")) + "\n")
    mutate(outdir, "good-locality.log", "renumbered-locality.log",
           lambda t: re.sub(r"^SAMPLE locality (\d+) ",
                            lambda m: f"SAMPLE locality {int(m.group(1)) * 2} ", t, flags=re.M))
    mutate(outdir, "good-locality.log", "sample-dropped-locality.log",
           lambda t: "\n".join(l for l in t.splitlines()
                               if not l.startswith(f"SAMPLE locality 20 {BOUNDED} ")) + "\n")

    def duplicated(t):
        out = []
        for line in t.splitlines():
            out.append(line)
            if line.startswith(f"SAMPLE locality 20 {BOUNDED} "):
                out.append(line)
        return "\n".join(out) + "\n"
    mutate(outdir, "good-locality.log", "sample-duplicated-locality.log", duplicated)

    # BOTH ORDERS IN ONE LOG: one log is one process, and one process runs one term order, so the
    # carveout block cannot be bound to two orders.
    def merged(t):
        with open(os.path.join(outdir, "good-census.log")) as fh:
            census = fh.read()
        return t + "".join(l for l in census.splitlines(True)
                           if not l.startswith("  carveout "))
    mutate(outdir, "good-locality.log", "two-orders-locality.log", merged)

    # One lane's samples copied verbatim onto another: the bit-identical alias guard. The two ARM
    # lines still declare different bodies, so nothing else can catch it.
    def aliased(t):
        donor = {}
        for line in t.splitlines():
            if line.startswith("SAMPLE locality ") and f" {HOT} " in line:
                f = line.split()
                donor[f[2]] = f[4:6]
        out = []
        for line in t.splitlines():
            if line.startswith("SAMPLE locality ") and f" {BOUNDED} " in line:
                f = line.split()
                line = " ".join(f[:4] + donor[f[2]] + [f[6]])
            out.append(line)
        return "\n".join(out) + "\n"
    mutate(outdir, "good-locality.log", "lane-aliased-locality.log", aliased)

    # A lane whose SAMPLE rows name a body its ARM line does not.
    def kernel_forged(t):
        out = []
        for line in t.splitlines():
            if line.startswith(f"SAMPLE locality 20 {FREE} "):
                line = " ".join(line.split()[:-1] + [REORDER_LB])
            out.append(line)
        return "\n".join(out) + "\n"
    mutate(outdir, "good-locality.log", "kernel-forged-locality.log", kernel_forged)

    # ONE LANE'S REGISTER COUNT MOVING BETWEEN THE TWO ORDERS' LOGS: registers are a fact of the
    # BUILD, so two logs that disagree are two builds and the static outcome matrix would be read
    # off whichever one the emitter happened to look at.
    mutate(outdir, "good-locality.log", "regs-cross-order-locality.log",
           lambda t: t.replace(f"ARM {BOUNDED} 70 ", f"ARM {BOUNDED} 71 "))

    # ANOTHER RUNG'S GRAMMAR: an R4 factorial log, which is decided under different rules.
    write(outdir, "not-r9.log",
          "CACHE-FACTORIAL schedule order=locality lanes=11 rounds=22 warmup=2\n"
          f"ARM {CTL} 72 3 256 32768 {PAIR} 0 0 0\n"
          "CACHE-FACTORIAL done order=locality warmup=2 rounds=22 lanes=11\n")

    print(f"wrote {len(os.listdir(outdir))} fixture logs into {outdir}")


if __name__ == "__main__":
    main()
