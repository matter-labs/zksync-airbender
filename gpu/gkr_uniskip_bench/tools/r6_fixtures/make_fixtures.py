#!/usr/bin/env python3
"""Generate the v3 R6 carveout-probe fixture logs into a directory.

    python3 gpu/gkr_uniskip_bench/tools/r6_fixtures/make_fixtures.py <outdir>

Deterministic — no randomness, so a regenerated fixture is byte-identical. `check.sh`
generates into a `mktemp -d` at runtime and removes it afterwards: the fixtures are DERIVED
data, so the tracked tree carries the generator that documents them, not ~90 logs.

The grammar is the runner's, including the harness's applied-hint echo line, which the
emitter cross-checks against the schedule line. Only the SAMPLE magnitudes are synthetic,
sized so each decision edge lands on the intended branch of the preregistered rules.

Every conforming scenario runs at the PINNED configuration — locality, hint 16, 100 rounds,
warmup 10 — so the signed threshold is 90/100. A per-round DRIFT term is added to every lane
alike: it cancels in the paired deltas (that is the point of the rotation) and its median
over the hundred rounds is exactly zero, so each lane's median is its stated base.
"""

import os
import sys

LANES = ["k24@128", "k32@128", "k40@128", "hot16@128", "control@256"]
CACHED = "eval_lsb_pair_cached_128_lb"
CONTROL = "eval_lsb_pair"

# The admission-ordered id list of the real run, sliced per lane exactly as the runner does.
ADMISSION = ([0, 1, 2, 3, 4, 5, 48, 49, 50, 51] + list(range(6, 36)))

# lane -> (regs, blocks/SM, threads, grid, kernel, C, removals, admitted), from the real
# session logs (--log-trace 24).
FACTS = {
    "k24@128": (72, 7, 128, 65536, CACHED, 36, 161, 24),
    "k32@128": (72, 7, 128, 65536, CACHED, 44, 177, 32),
    "k40@128": (72, 7, 128, 65536, CACHED, 52, 193, 40),
    "hot16@128": (72, 7, 128, 65536, CACHED, 28, 145, 16),
    "control@256": (72, 3, 256, 32768, CONTROL, 0, 0, 0),
}
FIN = {"k24@128": 0.008192, "k32@128": 0.008192, "k40@128": 0.008192,
       "hot16@128": 0.008192, "control@256": 0.006144}

# The pinned contract the emitter enforces.
ROUNDS, WARMUP, HINT, ORDER = 100, 10, "16", "locality"

HOTB, CTLB = 14.836, 16.624
# The R5 locality frontier the OFF processes must reproduce: k24/k32/k40 all lose to hot16.
OFF = {"hot16@128": HOTB, "k24@128": HOTB + 0.140, "k32@128": HOTB + 0.188,
       "k40@128": HOTB + 0.240, "control@256": CTLB}


def on(k24=0.140, k32=0.188, k40=0.240, hot=0.0, ctl=0.0):
    """A hinted process, stated as offsets from the off-process bases."""
    return {"hot16@128": HOTB + hot, "k24@128": HOTB + hot + k24,
            "k32@128": HOTB + hot + k32, "k40@128": HOTB + hot + k40,
            "control@256": CTLB + ctl}


def drift(r):
    return 0.002 * ((r % 5) - 2)


def log(order, hint, bases, wobble=None, rounds=ROUNDS, warmup=WARMUP, echo="same"):
    """One process. `echo` is the APPLIED-hint echo line: "same" mirrors the schedule line
    (what the runner does), None omits it, and a value states a disagreeing percentage."""
    if echo == "same":
        echo = None if hint == "default" else hint
    out = [
        "gpu_gkr_uniskip_bench config",
        "  mode                lsb-pair",
        "  cache_arm           carveout probe (5 lanes)",
        "  block_threads       256 + 128 (both, per lane)",
        f"  term_order          {order}",
    ]
    if echo is not None:
        out.append(f"  carveout hint       {echo}% ({CACHED})")
    out += [
        "work",
        "  device              NVIDIA RTX PRO 6000 Blackwell Server Edition",
        f"CARVEOUT-PROBE schedule order={order} lanes=5 rounds={rounds} warmup={warmup} "
        f"carveout-hint={hint}",
    ]
    for lane in LANES:
        regs, blocks, threads, grid, kernel, c, removals, admitted = FACTS[lane]
        ids = ",".join(str(i) for i in ADMISSION[:admitted]) if admitted else "-"
        out.append(f"ARM {lane} {regs} {blocks} {threads} {grid} {kernel} {c} {removals} "
                   f"{admitted} {ids}")
    for i in range(rounds):
        r = warmup + i
        for j in range(len(LANES)):
            lane = LANES[(r % len(LANES) + j) % len(LANES)]
            metric = bases[lane] + drift(r) + (wobble(lane, r) if wobble else 0.0)
            fin = FIN[lane]
            out.append(f"SAMPLE {order} {r} {lane} {metric - fin:.6f} {fin:.6f} "
                       f"{FACTS[lane][4]}")
    out.append(f"CARVEOUT-PROBE done order={order} warmup={warmup} rounds={rounds} lanes=5")
    return out


def write(outdir, name, lines):
    with open(os.path.join(outdir, name), "w") as fh:
        fh.write("\n".join(lines) + "\n")


def session(outdir, name, specs):
    """One four-log ABBA session. `specs` is off1, on1, on2, off2 as kwargs for `log`."""
    for tag, spec in zip(("off1", "on1", "on2", "off2"), specs):
        write(outdir, f"{name}-{tag}.log", log(**spec))


def off(**kw):
    spec = {"order": ORDER, "hint": "default", "bases": OFF}
    spec.update(kw)
    return spec


def hinted(bases, hint=HINT, **kw):
    spec = {"order": ORDER, "hint": hint, "bases": bases}
    spec.update(kw)
    return spec


def main():
    if len(sys.argv) != 2:
        sys.exit(f"usage: {sys.argv[0]} <outdir>")
    outdir = sys.argv[1]
    os.makedirs(outdir, exist_ok=True)

    # 1. k32 wins in BOTH hinted processes -> P1 (a), frontier position C = 44.
    moved = hinted(on(k24=0.070, k32=-0.050, k40=0.164))
    session(outdir, "frontier-moved", [off(), moved, moved, off()])

    # 2. all three win -> the moved frontier is right-censored at the top lane.
    censored = hinted(on(k24=-0.040, k32=-0.060, k40=-0.080))
    session(outdir, "right-censored", [off(), censored, censored, off()])

    # 2b. the SIGNED THRESHOLD itself, pinned from both sides. k32's delta is -0.020 in most
    #     rounds and +0.030 in the rest, so the median is negative either way and only the
    #     on-sign count decides: 90/100 is a win, 89/100 is a wash. A fixture set whose lanes
    #     are all 100/100 would not notice the literal moving at all.
    def flip(rs):
        return lambda lane, r: 0.050 if lane == "k32@128" and r in rs else 0.0

    near = hinted(on(k32=-0.020))
    met = dict(near, wobble=flip(set(range(WARMUP, WARMUP + 10))))
    miss = dict(near, wobble=flip(set(range(WARMUP, WARMUP + 11))))
    session(outdir, "sign-threshold-met", [off(), met, met, off()])
    session(outdir, "sign-threshold-miss", [off(), miss, miss, off()])

    # 3. no win, Δk24 halves against BOTH adjacent off processes (0.060 <= 0.070).
    priced = hinted(on(k24=0.060, k32=0.090, k40=0.115))
    session(outdir, "capacity-priced", [off(), priced, priced, off()])

    # 3b. the half-shrink boundary, pinned from both sides (half of the off delta is +0.070)
    #     and pinned as PAIRWISE: one pair shrinking is not the rule.
    session(outdir, "half-shrink-in",
            [off(), hinted(on(k24=0.069)), hinted(on(k24=0.069)), off()])
    session(outdir, "half-shrink-out",
            [off(), hinted(on(k24=0.071)), hinted(on(k24=0.071)), off()])
    session(outdir, "half-shrink-split",
            [off(), hinted(on(k24=0.060)), hinted(on(k24=0.100)), off()])

    # 4. deltas unchanged -> P1 (c). hot16 is 2 µs faster under the hint, so P2's bridged
    #    delta is negative in both stable pairs and its positive verdict is exercised too.
    flat = hinted(on(hot=-0.002))
    session(outdir, "wash", [off(), flat, flat, off()])

    # 5. off1's k24 alternates sign round by round -> WASH, so the R5 relation is not
    #    reproduced and the whole verdict is withheld.
    unstable = dict(OFF, **{"k24@128": HOTB})
    session(outdir, "unstable-off", [
        off(bases=unstable, wobble=lambda lane, r: 0.010 * (1 if r % 2 == 0 else -1)
            if lane == "k24@128" else 0.0),
        hinted(on()), hinted(on()), off()])

    # 6. k32 wins in on1 only -> MIXED, (a) not satisfied, falls through to (b)/(c).
    session(outdir, "mixed-on", [off(), hinted(on(k32=-0.050)), hinted(on()), off()])

    # 7. the hint sequence is on/off/on/off, not the ABBA the positions claim.
    session(outdir, "bad-sequence", [hinted(on()), off(), hinted(on()), off()])

    # 7b. on2 ran unhinted: a legal log in an illegal position.
    session(outdir, "on2-unhinted", [off(), hinted(on()), off(), off()])

    # 8. THE PIN. Each of these is a well-formed log outside the one preregistered
    #    configuration, so none of them has a rule to be decided under.
    session(outdir, "mixed-order", [off(), hinted(on()),
                                    dict(hinted(on()), order="census"), off()])
    session(outdir, "census-order", [off(order="census"), hinted(on(), order="census"),
                                     hinted(on(), order="census"), off(order="census")])
    session(outdir, "hint-not-16", [off(), hinted(on(), hint="25"),
                                    hinted(on(), hint="50"), off()])
    session(outdir, "rounds-not-100", [off(rounds=10), hinted(on(), rounds=10),
                                       hinted(on(), rounds=10), off(rounds=10)])

    # 8b. THE APPLIED HINT. The schedule line is one text edit away from claiming a hint
    #     state the process never ran, so the harness's own echo has to corroborate it.
    session(outdir, "echo-mismatch", [off(), hinted(on(), echo="25"), hinted(on()), off()])
    session(outdir, "echo-missing", [off(), hinted(on(), echo=None), hinted(on()), off()])
    session(outdir, "echo-spurious", [off(), hinted(on()), hinted(on()),
                                      off(echo=HINT)])

    # 9. one lane is one sample short (built by dropping a row).
    session(outdir, "short-lane", [off(), hinted(on()), hinted(on()), off()])
    path = os.path.join(outdir, "short-lane-off2.log")
    kept = [ln for ln in open(path).read().splitlines()
            if not ln.startswith("SAMPLE locality 15 k32@128")]
    write(outdir, "short-lane-off2.log", kept)

    # 10. the off1/on1 pair's control@256 medians are 0.2 ms apart -> that pair is unstable
    #     and the P2 verdict is withheld. 0.2 ms is +1.2 % of the anchor, so the sanity band
    #     is NOT what this fixture trips.
    session(outdir, "flank-fail", [off(), hinted(on(hot=-0.002, ctl=0.200)),
                                   hinted(on(hot=-0.002)), off()])

    # 11. control@256 sits 3 % above the anchor in every process: the flanks still agree, so
    #     only the sanity banner fires.
    shift = 0.03 * CTLB
    session(outdir, "sanity-out", [
        off(bases=dict(OFF, **{"control@256": CTLB + shift})),
        hinted(on(hot=-0.002, ctl=shift)), hinted(on(hot=-0.002, ctl=shift)),
        off(bases=dict(OFF, **{"control@256": CTLB + shift}))])

    # 12. a log from a DIFFERENT rotation entirely (the R5 frontier grammar), so the probe
    #     emitter cannot be pointed at another rung's log and summarize it under R6's rules.
    write(outdir, "not-a-probe.log", [
        "FRONTIER-FACTORIAL schedule order=locality lanes=10 rounds=100 warmup=10",
        "ARM hot16@128 72 7 128 65536 eval_lsb_pair_cached_128_lb 28 145 16 "
        "0,1,2,3,4,5,48,49,50,51,6,7,8,9,10,11",
        "SAMPLE locality 10 hot16@128 14.828000 0.008192 eval_lsb_pair_cached_128_lb",
        "FRONTIER-FACTORIAL done order=locality warmup=10 rounds=100 lanes=10",
    ])


if __name__ == "__main__":
    main()
