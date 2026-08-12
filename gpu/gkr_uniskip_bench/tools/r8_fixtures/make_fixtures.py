#!/usr/bin/env python3
"""Generate the v3 R8 admission-interior fixture sessions into a directory.

    python3 gpu/gkr_uniskip_bench/tools/r8_fixtures/make_fixtures.py <outdir>

Deterministic — no randomness, so a regenerated fixture is byte-identical. `check.sh`
generates into a `mktemp -d` at run time and removes it afterwards: the fixtures are DERIVED
data, so the tracked tree carries the generator that documents them, not the logs.

The grammar is the runner's (`main.rs`): a `FRONTIER-INTERIOR schedule` line, one frontier
`ARM` line per lane with its ordered admitted-id list, one `SAMPLE` per (round, lane) in the
cyclic rotation `slot = (round + offset) % lanes`, and the `done` trailer. The lane FACTS are
the REAL ones — the counts oracle's C, removals and admitted prefixes for K16…K24, and the
grids the arms take at `--log-trace 24`. Only the SAMPLE magnitudes are synthetic: these
fixtures pin the emitter's grammar, arithmetic and decision surface, and predict nothing.

Every conforming session is the preregistered shape: both term orders, 96 rounds, 12 warmup,
12 lanes = 8 full cycles. Mutants are generated fully SELF-CONSISTENT so each one fails on the
gate it is named for and not on a side effect.
"""

import os
import re
import sys
import zlib

CACHED = "eval_lsb_pair_cached_128_lb"
PAIR_LB = "eval_lsb_pair_128_lb"
PAIR = "eval_lsb_pair"
TAG = "FRONTIER-INTERIOR"
HOT = "hot16@128"
CTL = "control@256"
ROUNDS, WARMUP = 96, 12
ORDERS = ("locality", "census")

# The rotation in execution order (`FRONTIER_INTERIOR` in `src/coset_cache.rs`).
LANES = [f"k{k}@128" for k in range(17, 25)] + [HOT, "cache0@128", "control_lb@128", CTL]

# lane -> (regs, blocks/SM, threads, grid, kernel, C, removals, admitted). C and removals are
# the counts oracle's (`.agents/sdd/2026-08-12-v3-r8/expected-counts-r8.md`): one BF source at
# refs 3 per step, so C +1 and removals +2 from hot16's 28/145 up to k24's 36/161.
FACTS = {HOT: (72, 7, 128, 65536, CACHED, 28, 145, 16)}
FACTS.update({f"k{k}@128": (72, 7, 128, 65536, CACHED, 12 + k, 113 + 2 * k, k)
              for k in range(17, 25)})
FACTS.update({
    "cache0@128": (72, 7, 128, 65536, CACHED, 0, 0, 0),
    "control_lb@128": (72, 7, 128, 65536, PAIR_LB, 0, 0, 0),
    CTL: (72, 3, 256, 32768, PAIR, 0, 0, 0),
})

# The canonical admission ordering (`oracle-derivation.txt`, identical under both orders); a
# lane's admitted-id list is its first-K prefix IN THIS ORDER.
ORACLE = ([0, 1, 2, 3, 4, 5] + [48, 49, 50, 51] + list(range(6, 41))
          + [52, 53, 54, 55, 56, 57, 58] + [41, 42, 43])

# The anchor lanes' `eval + finalize` targets: R4's frozen medians for `control@256` and
# `hot16@128` (the emitter's HARD band) and R5's bases for the other two. A conforming session
# lands IN band by construction, so a fixture that reports OUT means the band moved.
BASE = {
    "locality": {CTL: 16.624, HOT: 14.836, "control_lb@128": 16.406, "cache0@128": 17.071},
    "census": {CTL: 16.545, HOT: 15.129, "control_lb@128": 16.219, "cache0@128": 16.884},
}
# The finalize stage, held per block size: the 128 lanes reduce twice the partials.
FIN = {lane: (0.033 if FACTS[lane][2] == 256 else 0.063) for lane in LANES}


def arm_line(lane, patch=None):
    regs, blocks, threads, grid, kernel, c, removals, admitted = FACTS[lane]
    f = {"grid": grid, "c": c, "removals": removals, "admitted": admitted, "kernel": kernel,
         "ids": ORACLE[:admitted]}
    f.update((patch or {}).get(lane, {}))
    ids = ",".join(str(i) for i in f["ids"]) if f["ids"] else "-"
    return (f"ARM {lane} {regs} {blocks} {threads} {f['grid']} {f['kernel']} {f['c']} "
            f"{f['removals']} {f['admitted']} {ids}")


def jitter(lane, i, amp):
    """Deterministic, zero-mean-ish wobble; `amp` is the half-width in ms. `crc32`, not
    `hash`, so a regenerated fixture does not depend on PYTHONHASHSEED."""
    h = (zlib.crc32(f"{lane}#{i}".encode()) & 0xFFFF) / 0xFFFF
    return (2.0 * h - 1.0) * amp


def flat(lane, mean, rounds=ROUNDS, amp=0.02):
    return [mean + jitter(lane, i, amp) for i in range(rounds)]


def series(order, offsets, rounds=ROUNDS, override=None):
    """Every lane's `eval + finalize` per round: the four anchors at their bases, the axis
    lanes at `hot16 + offset`, and any lane in `override` taken verbatim."""
    s = {lane: flat(lane, BASE[order][lane], rounds) for lane in BASE[order]}
    for lane, off in offsets.items():
        s[lane] = flat(lane, BASE[order][HOT] + off, rounds)
    s.update(override or {})
    return s


def log(order, s, rounds=ROUNDS, warmup=WARMUP, tag=TAG, lanes=None, patch=None, fixed=False):
    lanes = lanes or LANES
    n = len(lanes)
    out = [f"{tag} schedule order={order} lanes={n} rounds={rounds} warmup={warmup}"]
    out += [arm_line(lane, patch) for lane in lanes]
    for i in range(rounds):
        index = warmup + i
        for offset in range(n):
            lane = lanes[offset if fixed else (index + offset) % n]
            fin = FIN[lane]
            kernel = (patch or {}).get(lane, {}).get("kernel", FACTS[lane][4])
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
    census-is-diagnostic-only rule is testable at all."""
    over = {order: kw.pop(f"override_{order}", None) for order in ORDERS}
    for order in ORDERS:
        write(outdir, f"{name}-{order}.log",
              log(order, series(order, offsets[order], kw.get("rounds", ROUNDS), over[order]),
                  **kw))


def mutate(outdir, src, dst, fn):
    with open(os.path.join(outdir, src)) as fh:
        text = fh.read()
    write(outdir, dst, fn(text))


def main():
    outdir = sys.argv[1]
    os.makedirs(outdir, exist_ok=True)

    # THE CONFORMING SESSION. locality peaks at k19 and turns at k21; census peaks at k18 and
    # turns at k20, so the emitted decision must name locality's pair and print census's as
    # diagnostic context (amendment A1).
    good = {
        "locality": {"k17@128": -0.20, "k18@128": -0.30, "k19@128": -0.35, "k20@128": -0.25,
                     "k21@128": +0.10, "k22@128": +0.20, "k23@128": +0.30, "k24@128": +0.40},
        "census": {"k17@128": -0.25, "k18@128": -0.30, "k19@128": -0.20, "k20@128": +0.15,
                   "k21@128": +0.25, "k22@128": +0.35, "k23@128": +0.45, "k24@128": +0.55},
    }
    session(outdir, "good", good)

    # EDGE: nothing above hot16 loses, so the axis is right-censored with no first loser. The
    # winner here is the TOP lane, which the capture set already carries as the censoring
    # endpoint, so this session pins the two roles landing on one manifest line.
    monotone = {order: {f"k{k}@128": -0.10 * (k - 16) for k in range(17, 25)}
                for order in ORDERS}
    session(outdir, "no-loser", monotone)

    # EDGE: the same right-censored shape with an INTERIOR optimum — every cumulative contrast
    # is a signed WIN, so there is no first loser, and the winner (k21) is the rung's whole
    # answer in that branch. A7's fallback midpoint would leave it unprofiled, which is the
    # failure this session exists to catch.
    interior_peak = {order: {"k17@128": -0.10, "k18@128": -0.20, "k19@128": -0.30,
                             "k20@128": -0.40, "k21@128": -0.50, "k22@128": -0.45,
                             "k23@128": -0.35, "k24@128": -0.20} for order in ORDERS}
    session(outdir, "no-loser-interior-winner", interior_peak)

    # EDGE: neither a winner nor a first loser — every axis lane wobbles around the incumbent
    # far enough that no contrast is sign-stable. THAT is the branch A7's fallback set is for,
    # so the axis midpoint appears here and nowhere else.
    over, offs = {}, {}
    for order in ORDERS:
        over[f"override_{order}"] = {lane: flat(lane, BASE[order][HOT], ROUNDS, 0.20)
                                     for lane in LANES[:8]}
        offs[order] = {}
    session(outdir, "all-wash", offs, **over)

    # EDGE: every interior point is slower than the incumbent, so there is no winner at all
    # and the first loser is the very first step.
    slower = {order: {f"k{k}@128": +0.10 * (k - 16) for k in range(17, 25)}
              for order in ORDERS}
    session(outdir, "no-winner", slower)

    # EDGE: the signed threshold, at it and one below it. hot16 is held CONSTANT so k17 can
    # carry an exact count of negative paired differences; every other lane is a clear loss,
    # so the winner is k17 or nobody and the count is what decides which.
    for name, neg in (("sign-at-threshold", 87), ("sign-below-threshold", 86)):
        over, offs = {}, {}
        for order in ORDERS:
            h = BASE[order][HOT]
            over[f"override_{order}"] = {
                HOT: [h] * ROUNDS,
                "k17@128": [h - 0.10] * neg + [h + 0.10] * (ROUNDS - neg),
            }
            offs[order] = {f"k{k}@128": 0.30 + 0.02 * (k - 17) for k in range(17, 25)}
        session(outdir, name, offs, **over)

    # EDGE: two lanes whose paired-difference multisets against a CONSTANT hot16 are exact
    # permutations of each other, so their cumulative medians are bit-identical in binary64 and
    # only the tie-break (smaller K) can decide. k24 is a loss, so the manifest must also
    # dedup: it is the censoring endpoint AND the first loser.
    over, offs = {}, {}
    wob = [round(0.40 + 0.004 * i, 6) for i in range(ROUNDS)]
    for order in ORDERS:
        h = BASE[order][HOT]
        over[f"override_{order}"] = {
            HOT: [h] * ROUNDS,
            "k19@128": [round(h - w, 6) for w in wob],
            "k22@128": [round(h - w, 6) for w in wob[48:] + wob[:48]],
        }
        offs[order] = {"k17@128": -0.10, "k18@128": -0.15, "k20@128": -0.20,
                       "k21@128": -0.20, "k23@128": -0.25, "k24@128": +0.10}
    session(outdir, "tie-smaller-k", offs, **over)

    # EDGE: the R4-frozen band is the HARD gate — `control@256` 3 % slow invalidates the
    # session, and no capture set may be selected from it.
    out_of_band = {order: dict(good[order]) for order in ORDERS}
    over = {f"override_{order}": {CTL: flat(CTL, BASE[order][CTL] * 1.03)} for order in ORDERS}
    session(outdir, "anchor-out-of-band", out_of_band, **over)

    # EDGE: the flank rule — the incumbent's LAST full cycle drifts 0.3 ms past the scaled
    # threshold while its session median stays in band, which is exactly the case a
    # session-median check cannot see.
    over = {}
    for order in ORDERS:
        s = flat(HOT, BASE[order][HOT])
        over[f"override_{order}"] = {HOT: s[:-12] + [x + 0.30 for x in s[-12:]]}
    session(outdir, "flank-tripped", {order: dict(good[order]) for order in ORDERS}, **over)

    # THE LOG CONTRACT (amendment A5), each mutant self-consistent so it fails on its own gate.
    session(outdir, "wrong-warmup", good, warmup=8)
    session(outdir, "wrong-rounds", good, rounds=108)
    session(outdir, "rotation-fixed", good, fixed=True)
    # The trace appears in no log line; the grid is what carries it, so a session recorded at
    # `--log-trace 23` is internally consistent and only the grid pin sees it.
    session(outdir, "wrong-trace", good,
            patch={lane: {"grid": FACTS[lane][3] // 2} for lane in LANES})
    # One lane's ARM line carrying its neighbour's plan: the counts move together, so the
    # label-vs-K identity is what catches it.
    session(outdir, "lane-plan-duplicated", good,
            patch={"k22@128": {"c": 33, "removals": 155, "admitted": 21, "ids": ORACLE[:21]}})
    # A step that is not one BF source at refs 3: the per-removal columns divide by these
    # deltas, so a log whose axis is not the oracle's is priced in the wrong currency.
    session(outdir, "axis-broken", good, patch={"k21@128": {"removals": 156}})
    # A reversal among two equal-ref sources: every count is unchanged and only the ORDERED
    # list sees it.
    swapped = ORACLE[:20]
    swapped[12], swapped[13] = swapped[13], swapped[12]
    session(outdir, "ids-reversed", good, patch={"k20@128": {"ids": swapped}})

    mutate(outdir, "good-locality.log", "wrong-tag-locality.log",
           lambda t: t.replace(TAG, "FRONTIER-FACTORIAL"))
    mutate(outdir, "good-census.log", "wrong-tag-census.log",
           lambda t: t.replace(TAG, "FRONTIER-FACTORIAL"))
    mutate(outdir, "good-locality.log", "unknown-order-locality.log",
           lambda t: t.replace("locality", "reverse"))
    mutate(outdir, "good-locality.log", "lane-unknown-locality.log",
           lambda t: t.replace("k19@128", "k19b@128"))
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
                               if not l.startswith("SAMPLE locality 20 k21@128 ")) + "\n")
    def duplicated(t):
        out = []
        for line in t.splitlines():
            out.append(line)
            if line.startswith("SAMPLE locality 20 k21@128 "):
                out.append(line)
        return "\n".join(out) + "\n"
    mutate(outdir, "good-locality.log", "sample-duplicated-locality.log", duplicated)

    # One lane's samples copied verbatim onto another: the bit-identical alias guard. The two
    # ARM lines still declare different plans, so nothing else can catch it.
    def aliased(t):
        donor = {}
        for line in t.splitlines():
            if line.startswith("SAMPLE locality ") and " k21@128 " in line:
                f = line.split()
                donor[f[2]] = f[4:6]
        out = []
        for line in t.splitlines():
            if line.startswith("SAMPLE locality ") and " k22@128 " in line:
                f = line.split()
                line = " ".join(f[:4] + donor[f[2]] + [f[6]])
            out.append(line)
        return "\n".join(out) + "\n"
    mutate(outdir, "good-locality.log", "lane-aliased-locality.log", aliased)

    # A lane whose SAMPLE rows name a body its ARM line does not.
    def kernel_forged(t):
        out = []
        for line in t.splitlines():
            if line.startswith("SAMPLE locality 20 k18@128 "):
                line = " ".join(line.split()[:-1] + [PAIR_LB])
            out.append(line)
        return "\n".join(out) + "\n"
    mutate(outdir, "good-locality.log", "kernel-forged-locality.log", kernel_forged)

    # ANOTHER RUNG'S GRAMMAR: an R4 factorial log, which is decided under different rules.
    write(outdir, "not-r8.log",
          "CACHE-FACTORIAL schedule order=locality lanes=11 rounds=22 warmup=2\n"
          f"ARM {CTL} 72 3 256 32768 {PAIR} 0 0 0\n"
          "CACHE-FACTORIAL done order=locality warmup=2 rounds=22 lanes=11\n")

    print(f"wrote {len(os.listdir(outdir))} fixture logs into {outdir}")


if __name__ == "__main__":
    main()
