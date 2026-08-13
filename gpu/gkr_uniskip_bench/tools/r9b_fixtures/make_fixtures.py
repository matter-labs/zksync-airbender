#!/usr/bin/env python3
"""Generate the v3 R9b fixture sessions into a directory.

    python3 gpu/gkr_uniskip_bench/tools/r9b_fixtures/make_fixtures.py <outdir>

Deterministic — no randomness, so a regenerated fixture is byte-identical. `check.sh` generates into
a `mktemp -d` at run time and removes it afterwards: the fixtures are DERIVED data, so the tracked
tree carries the generator that documents them, not the logs.

The grammar is the runner's (`main.rs` / `harness.rs`): the per-symbol applied-carveout echoes and the
`carveout symbols` set line, an `R9B schedule` line, one frontier `ARM` line per lane with its ordered
admitted-id list, one `SAMPLE` per (round, lane) in the cyclic rotation `slot = (round + offset) % 8`,
and the `done` trailer. The lane FACTS are the REAL ones — both rotations' registers, arithmetic block
tiers, kernels, C, removals and admitted prefixes as the shipped binary publishes them, and the grids
the arms take at `--log-trace 24`. Only the SAMPLE magnitudes are synthetic: these fixtures pin the
emitter's grammar, arithmetic and reporting surface, and predict nothing.

TWO ROTATIONS, ONE TAG. Both print `R9B schedule … lanes=8`, so a fixture names its shape in its
FILENAME and the emitter has to recover it from the lane label set alone. A conforming CLASS +
BUDGET pair is four logs, which is also the only way the bridge lane's two medians can be printed.

Every conforming session is the rung's shape: both term orders, 96 rounds, 8 warmup, 8 lanes = 12
full cycles. Mutants are generated fully SELF-CONSISTENT so each one produces the observation it is
named for and not a side effect. The emitter REPORTS rather than adjudicates, so most mutants prove
that a FLAG fires with the right text; only the ones that make a number impossible to compute (a
missing order, missing rounds, an incomplete round, an unknown lane, a truncated log, a foreign
rotation in the set) prove a rejection.
"""

import os
import re
import sys
import zlib

TAG = "R9B"
ROUNDS, WARMUP = 96, 8
ORDERS = ("locality", "census")

CTL, CTL_LB, HOT = "control@256", "control_lb@128", "hot16@128"
DROPIN = "reorder-hot16@128"
C, B, CD, BD = "c-hot16@128", "b-hot16@128", "cd-hot16@128", "bd-hot16@128"
INC_LB6, INC_FREE = "hot16-lb6@128", "hot16-free@128"
C_LB6, C_FREE = "c-hot16-lb6@128", "c-hot16-free@128"

PAIR = "eval_lsb_pair"
PAIR_LB = "eval_lsb_pair_128_lb"
CACHED = "eval_lsb_pair_cached_128_lb"
CACHED_LB6 = "eval_lsb_pair_cached_128_lb6"
CACHED_FREE = "eval_lsb_pair_cached_128"
REORDER_LB = "eval_lsb_pair_cached_reorder_128_lb"
C_LB_K = "eval_lsb_pair_cached_reorder_c_128_lb"
C_LB6_K = "eval_lsb_pair_cached_reorder_c_128_lb6"
C_FREE_K = "eval_lsb_pair_cached_reorder_c_128"
B_LB_K = "eval_lsb_pair_cached_reorder_b_128_lb"
CD_LB_K = "eval_lsb_pair_cached_reorder_cd_128_lb"
BD_LB_K = "eval_lsb_pair_cached_reorder_bd_128_lb"

# lane -> (regs, arith blocks/SM, threads, grid at --log-trace 24, kernel, C, removals, admitted).
# Every cached cell of both rotations sits at hot16's plan — same C, same removals, the same ordered
# admitted set — so the kernel is the only field that says which (body, budget) cell ran.
FACTS = {
    CTL: (72, 3, 256, 32768, PAIR, 0, 0, 0),
    CTL_LB: (72, 7, 128, 65536, PAIR_LB, 0, 0, 0),
    HOT: (72, 7, 128, 65536, CACHED, 28, 145, 16),
    INC_LB6: (80, 6, 128, 65536, CACHED_LB6, 28, 145, 16),
    INC_FREE: (75, 6, 128, 65536, CACHED_FREE, 28, 145, 16),
    DROPIN: (70, 7, 128, 65536, REORDER_LB, 28, 145, 16),
    C: (70, 7, 128, 65536, C_LB_K, 28, 145, 16),
    C_LB6: (75, 6, 128, 65536, C_LB6_K, 28, 145, 16),
    C_FREE: (64, 8, 128, 65536, C_FREE_K, 28, 145, 16),
    B: (70, 7, 128, 65536, B_LB_K, 28, 145, 16),
    CD: (72, 7, 128, 65536, CD_LB_K, 28, 145, 16),
    BD: (72, 7, 128, 65536, BD_LB_K, 28, 145, 16),
}

# The two rotations in EXECUTION order (`R9B_CLASS` / `R9B_BUDGET` in `src/coset_cache.rs`), and the
# hinted local symbols in the order the harness echoes them (`LaneKernel::HINTED`). NOTE the CLASS
# echo order: `cd` BEFORE `b`, which is the HINTED table's order and NOT the lane order — Task 2
# concern 3, and the reason a fixture pins the set as a SEQUENCE.
SHAPES = {
    "class": {
        "lanes": [CTL, CTL_LB, HOT, DROPIN, C, B, CD, BD],
        "hinted": [CACHED, REORDER_LB, C_LB_K, CD_LB_K, B_LB_K, BD_LB_K],
    },
    "budget": {
        "lanes": [CTL, CTL_LB, HOT, INC_LB6, INC_FREE, C, C_LB6, C_FREE],
        "hinted": [CACHED, CACHED_LB6, CACHED_FREE, C_LB_K, C_LB6_K, C_FREE_K],
    },
}
# This literal is the fixture's own: it describes what the runner writes today, while the emitter
# reads the tier off the log and holds no expected value — which is why a re-pin needs no emitter
# change.
HINT = 16

# The canonical admission ordering (`oracle-derivation.txt`, identical under both orders); a lane's
# admitted-id list is its first-K prefix IN THIS ORDER.
ORACLE = ([0, 1, 2, 3, 4, 5] + [48, 49, 50, 51] + list(range(6, 41))
          + [52, 53, 54, 55, 56, 57, 58] + [41, 42, 43])

# The anchor lanes' `eval + finalize` targets, THREE of them since the re-base. The emitter FLAGS a
# delta past 1.5 % against the CAMPAIGN BASELINE — this rung's own session, keyed by rotation — and
# against nothing else, so a conforming session need only sit inside 1.5 % of both rotations' rows.
# It does, on all three anchors in both orders, which is what makes "no flags" a meaningful fixture
# state; `anchor-offset` trips it on purpose. The PRE-PROVENANCE references are computed and printed
# but can never flag: `baseline-exact` is the fixture that proves it, sitting +2.16 % off R4-frozen
# with no ANCHOR flag raised.
BASE = {
    "locality": {CTL: 16.650, CTL_LB: 16.474, HOT: 14.790},
    "census": {CTL: 16.775, CTL_LB: 16.613, HOT: 15.290},
}
# The committed baseline itself, per rotation and order, as (control@256, control_lb@128, hot16@128).
# `baseline-exact` places a session ON it: every baseline delta is then 0.00 % while the historical
# rows still read +2.16 % — the two-tier model in one fixture.
BASELINE = {
    "class": {"locality": (16.725, 16.455, 14.793), "census": (16.903, 16.620, 15.352)},
    "budget": {"locality": (16.778, 16.493, 14.823), "census": (16.893, 16.607, 15.347)},
}
# The finalize stage, held per block size: the 128 lanes reduce twice the partials.
FIN = {lane: (0.033 if FACTS[lane][2] == 256 else 0.063) for lane in FACTS}

# The conforming offsets off `hot16@128`. `C`'s offset is IDENTICAL in the two rotations per order, so
# the bridge lane reads the same median in both sessions and the bridge row is a clean zero — the one
# state in which the bridge says "these two sessions are comparable" and nothing else.
CLASS_OFF = {
    "locality": {DROPIN: 0.800, C: -0.150, B: -0.050, CD: 0.100, BD: 0.250},
    "census": {DROPIN: 0.850, C: -0.120, B: -0.030, CD: 0.130, BD: 0.280},
}
BUDGET_OFF = {
    "locality": {INC_LB6: 0.200, INC_FREE: -0.100, C: -0.150, C_LB6: -0.250, C_FREE: -0.400},
    "census": {INC_LB6: 0.230, INC_FREE: -0.080, C: -0.120, C_LB6: -0.220, C_FREE: -0.370},
}
OFF = {"class": CLASS_OFF, "budget": BUDGET_OFF}

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


def preamble(shape, echoes=None, symbols=True, count=None, extra=None):
    """The harness's carveout block: one applied-hint echo per hinted local symbol, then the set
    line. `echoes` is a list of (percent, symbol) pairs; `symbols` names the set line's list, or
    False to omit it. The indentation is part of the runner's literal."""
    hinted = SHAPES[shape]["hinted"]
    echoes = [(HINT, sym) for sym in hinted] if echoes is None else echoes
    out = [f"  carveout hint       {pct}% ({sym})" for pct, sym in echoes]
    if symbols:
        names = [sym for _, sym in echoes] if symbols is True else symbols
        n = len(names) if count is None else count
        out.append(f"  carveout symbols    {n} local ({', '.join(names)})")
    return out + list(extra or [])


def jitter(lane, i, amp):
    """Deterministic, zero-mean-ish wobble; `amp` is the half-width in ms. `crc32`, not `hash`, so a
    regenerated fixture does not depend on PYTHONHASHSEED."""
    h = (zlib.crc32(f"{lane}#{i}".encode()) & 0xFFFF) / 0xFFFF
    return (2.0 * h - 1.0) * amp


def flat(lane, mean, rounds=ROUNDS, amp=0.02):
    return [mean + jitter(lane, i, amp) for i in range(rounds)]


def series(shape, order, offsets, rounds=ROUNDS, override=None):
    """Every lane's `eval + finalize` per round: the three anchors at their bases, every other lane
    at `hot16 + offset`, and any lane in `override` taken verbatim."""
    s = {lane: flat(lane, BASE[order][lane], rounds) for lane in BASE[order]}
    for lane, off in offsets.items():
        s[lane] = flat(lane, BASE[order][HOT] + off, rounds)
    s.update(override or {})
    return {lane: s[lane] for lane in SHAPES[shape]["lanes"]}


def log(shape, order, s, rounds=ROUNDS, warmup=WARMUP, tag=TAG, lanes=None, patch=None, fixed=False,
        head=None, lanes_field=None):
    lanes = lanes or SHAPES[shape]["lanes"]
    n = len(lanes)
    # The header's OWN count, separable from the ARM lines: that disagreement is a header-consistency
    # observation, and nothing else in the log can see it.
    declared = n if lanes_field is None else lanes_field
    out = list(preamble(shape)) if head is None else list(head)
    out.append(f"{tag} schedule order={order} lanes={declared} rounds={rounds} warmup={warmup}")
    out += [arm_line(lane, patch) for lane in lanes]
    for i in range(rounds):
        index = warmup + i
        for offset in range(n):
            lane = lanes[offset if fixed else (index + offset) % n]
            fin = FIN[lane]
            kernel = facts_of(lane, patch)["kernel"]
            out.append(f"SAMPLE {order} {index} {lane} {s[lane][i] - fin:.6f} {fin:.6f} {kernel}")
    out.append(f"{tag} done order={order} warmup={warmup} rounds={rounds} lanes={declared}")
    return "\n".join(out) + "\n"


def write(outdir, name, text):
    with open(os.path.join(outdir, name), "w") as fh:
        fh.write(text)


def session(outdir, name, shapes=("class", "budget"), offsets=None, **kw):
    """One fixture SESSION SET: for each named shape, the two logs the emitter requires. `offsets` is
    per shape and per order so a fixture can give the two orders — or the two rotations — different
    shapes, which is how the rows are shown to be read side by side rather than reconciled."""
    over = {(shape, order): kw.pop(f"override_{shape}_{order}", None)
            for shape in shapes for order in ORDERS}
    for shape in shapes:
        for order in ORDERS:
            off = (offsets or OFF)[shape][order] if offsets else OFF[shape][order]
            write(outdir, f"{name}-{shape}-{order}.log",
                  log(shape, order,
                      series(shape, order, off, kw.get("rounds", ROUNDS),
                             over[(shape, order)]),
                      **kw))


def mutate(outdir, src, dst, fn):
    with open(os.path.join(outdir, src)) as fh:
        text = fh.read()
    write(outdir, dst, fn(text))


def main():
    outdir = sys.argv[1]
    os.makedirs(outdir, exist_ok=True)

    # THE CONFORMING SESSION SET, and the only one that must raise NO flag at all: every cell fact
    # matches its rotation's own description of itself, all four anchor references are inside 1.5 %,
    # and the bridge lane reads the same median in both rotations.
    session(outdir, "good")

    # EDGE: a recovery row wobbling around zero — the sign count falls below the label's threshold,
    # so the printed label is WASH while the median is still reported to three decimals.
    over = {f"override_class_{o}": {C: flat(C, BASE[o][HOT] + OFF["class"][o][DROPIN], ROUNDS, 0.60)}
            for o in ORDERS}
    session(outdir, "recovery-wash", shapes=("class",), **over)

    # EDGE: every corrected body SLOWER than R9's drop-in — the repair made it worse. Labels are
    # LOSS and the emitter prints the whole picture, capture manifest included.
    session(outdir, "recovery-loss", offsets={
        "class": {o: dict(OFF["class"][o], **{C: 1.100, B: 1.200, CD: 1.300, BD: 1.400})
                  for o in ORDERS}}, shapes=("class",))

    # EDGE: the two term orders name DIFFERENT lowest-median corrected bodies. Both are listed in the
    # capture manifest and neither is reconciled.
    session(outdir, "best-split", shapes=("class",), offsets={
        "class": {"locality": dict(OFF["class"]["locality"]),
                  "census": dict(OFF["class"]["census"], **{C: 0.400, B: -0.500})}})

    # EDGE: an anchor lane 3 % off the campaign baseline — the ANCHOR flag's own session. The
    # rotation composition question this rung has to answer is exactly this reading.
    over = {f"override_{sh}_{o}": {CTL: flat(CTL, BASE[o][CTL] * 1.03)}
            for sh in ("class", "budget") for o in ORDERS}
    session(outdir, "anchor-offset", **over)

    # THE RE-BASE, in one fixture: a session sitting EXACTLY on the campaign baseline, every anchor,
    # both rotations, both orders. Its baseline deltas are 0.00 % so NO ANCHOR flag fires — while its
    # pre-provenance rows read as much as +2.16 % off R4-frozen and raise nothing, because the
    # historical block is context and never a flag basis. That pairing is the whole re-base.
    over = {}
    for sh in ("class", "budget"):
        for o in ORDERS:
            ctl, ctl_lb, hot = BASELINE[sh][o]
            over[f"override_{sh}_{o}"] = {
                CTL: [ctl] * ROUNDS, CTL_LB: [ctl_lb] * ROUNDS, HOT: [hot] * ROUNDS,
            }
    session(outdir, "baseline-exact", **over)

    # EDGE: the sign label's threshold, at it and one below it, on the C recovery row. The drop-in is
    # held CONSTANT so the corrected body can carry an exact count of negative paired differences.
    for name, neg in (("sign-at-threshold", 87), ("sign-below-threshold", 86)):
        over = {}
        for o in ORDERS:
            h = BASE[o][HOT] + OFF["class"][o][DROPIN]
            over[f"override_class_{o}"] = {
                DROPIN: [h] * ROUNDS,
                C: [h - 0.10] * neg + [h + 0.10] * (ROUNDS - neg),
            }
        session(outdir, name, shapes=("class",), **over)

    # EDGE: the flank reading — the incumbent's LAST full cycle drifts 0.3 ms past the scaled reading
    # while its session median stays put, which is exactly the case a session-median comparison
    # cannot see.
    over = {}
    for o in ORDERS:
        s = flat(HOT, BASE[o][HOT])
        over[f"override_class_{o}"] = {HOT: s[:-8] + [x + 0.30 for x in s[-8:]]}
    session(outdir, "flank-tripped", shapes=("class",), **over)

    # THE LOG CONTRACT, each mutant self-consistent so it raises its own observation.
    session(outdir, "wrong-warmup", shapes=("class",), warmup=12)
    # 104 is a whole number of 8-lane cycles, so only the round SHAPE reading sees it.
    session(outdir, "wrong-rounds", shapes=("class",), rounds=104)
    session(outdir, "rotation-fixed", shapes=("class",), fixed=True)
    # The trace appears in no log line; the grid is what carries it, so a session recorded at
    # `--log-trace 23` is internally consistent and only the grid reading sees it.
    session(outdir, "wrong-trace", shapes=("class",),
            patch={lane: {"grid": FACTS[lane][3] // 2} for lane in FACTS})
    # A SWAPPED BODY: the C lane declaring B's cell. Every count is unchanged and every cached lane
    # shares one plan, so only the per-lane cell check sees it.
    session(outdir, "body-swapped", shapes=("class",), patch={C: {"kernel": B_LB_K}})
    # A SWAPPED BUDGET: the same body at another budget, which is the axis that is NOT monotone in
    # registers — so it has to be named as a budget swap rather than as a body swap.
    session(outdir, "budget-swapped", shapes=("class",), patch={C: {"kernel": C_LB6_K}})
    session(outdir, "budget-swapped-inc", shapes=("budget",),
            patch={INC_FREE: {"kernel": CACHED_LB6}})
    # A lane pricing a different plan from the incumbent every row is read against.
    session(outdir, "plan-mismatch", shapes=("class",), patch={C: {"c": 29, "removals": 147}})
    # A reversal among two equal-ref sources: every count is unchanged and only the ORDERED list
    # sees it.
    swapped = ORACLE[:16]
    swapped[12], swapped[13] = swapped[13], swapped[12]
    session(outdir, "ids-reversed", shapes=("class",), patch={BD: {"ids": swapped}})
    # THE HEADER'S OWN COUNT: eight ARM lines under a `lanes=7` header.
    session(outdir, "header-lanes", shapes=("class",), lanes_field=7)

    # THE BRIDGE. `c-hot16@128` is the one cell both rotations carry, so it is the only
    # cross-session reading there is — and a build fact that moves under it means the two sessions
    # are two builds.
    session(outdir, "bridge-facts", patch={C: {"regs": 71}}, shapes=("budget",))
    session(outdir, "bridge-medians", shapes=("budget",), offsets={
        "budget": {o: dict(OFF["budget"][o], **{C: 0.900}) for o in ORDERS}})

    # THE CARVEOUT GRAMMAR. The percent is READ off these echoes, and every row contrasts cells at
    # the SAME one — so a missing, wrong, spurious or non-uniform echo is a flagged observation about
    # the configuration. The ORDER matters too, and it is the HINTED order, not the lane order.
    def head_session(name, shape="class", **kw):
        for order in ORDERS:
            write(outdir, f"{name}-{shape}-{order}.log",
                  log(shape, order, series(shape, order, OFF[shape][order]),
                      head=preamble(shape, **kw)))

    head_session("echo-missing", echoes=[(HINT, s) for s in SHAPES["class"]["hinted"][:-1]])
    head_session("echo-wrong-pct",
                 echoes=[(HINT if i else 33, s)
                         for i, s in enumerate(SHAPES["class"]["hinted"])])
    head_session("echo-extra",
                 echoes=[(HINT, s) for s in SHAPES["class"]["hinted"] + ["eval_lsb_seg_g"]])
    # THE LANE ORDER, echoed: `b` before `cd` is how the LANES run and is NOT how the harness hints
    # them. A fixture that accepted it would let a real echo-order change pass unremarked.
    head_session("echo-lane-order",
                 echoes=[(HINT, s) for s in [CACHED, REORDER_LB, C_LB_K, B_LB_K, CD_LB_K, BD_LB_K]])
    head_session("echo-duplicated",
                 echoes=[(HINT, s) for s in SHAPES["class"]["hinted"] + [CACHED]])
    head_session("symbols-missing", symbols=False)
    head_session("symbols-count-wrong", count=5)
    head_session("symbols-disagree",
                 symbols=SHAPES["class"]["hinted"][:-1] + ["eval_lsb_seg_g"])
    head_session("symbols-twice",
                 extra=[f"  carveout symbols    6 local ({', '.join(SHAPES['class']['hinted'])})"])
    # A `carveout` line that is neither grammar: the check exists so a runner whose echo literal
    # drifts is reported rather than read as an unhinted process.
    head_session("echo-malformed", extra=["  carveout hint       16 % (eval_lsb_pair)"])
    # The BUDGET rotation's own hinted set, one symbol short — its set is a different list, so a
    # fixture that only covered CLASS would not see a shape-keyed mistake.
    head_session("echo-missing-budget", shape="budget",
                 echoes=[(HINT, s) for s in SHAPES["budget"]["hinted"][:-1]])

    # ONE LANE'S REGISTER COUNT MOVING BETWEEN THE TWO ORDERS' LOGS: registers are a fact of the
    # BUILD, so two logs that disagree describe two builds.
    mutate(outdir, "good-class-locality.log", "regs-cross-order-class-locality.log",
           lambda t: t.replace(f"ARM {C} 70 ", f"ARM {C} 71 "))

    # A FOREIGN ROTATION IN THE SET, one half and both.
    mutate(outdir, "good-class-locality.log", "wrong-tag-class-locality.log",
           lambda t: t.replace(TAG, "FRONTIER-INTERIOR"))
    mutate(outdir, "good-class-census.log", "wrong-tag-class-census.log",
           lambda t: t.replace(TAG, "FRONTIER-INTERIOR"))

    mutate(outdir, "good-class-locality.log", "unknown-order-class-locality.log",
           lambda t: t.replace("locality", "reverse"))
    mutate(outdir, "good-class-locality.log", "lane-unknown-class-locality.log",
           lambda t: t.replace(C, "c-hot17@128"))
    mutate(outdir, "good-class-locality.log", "arm-without-ids-class-locality.log",
           lambda t: "\n".join(" ".join(line.split()[:-1]) if line.startswith(f"ARM {HOT} ")
                               else line for line in t.splitlines()) + "\n")
    mutate(outdir, "good-class-locality.log", "no-trailer-class-locality.log",
           lambda t: "\n".join(line for line in t.splitlines()
                               if not line.startswith(f"{TAG} done")) + "\n")
    mutate(outdir, "good-class-locality.log", "renumbered-class-locality.log",
           lambda t: re.sub(r"^SAMPLE locality (\d+) ",
                            lambda m: f"SAMPLE locality {int(m.group(1)) * 2} ", t, flags=re.M))
    mutate(outdir, "good-class-locality.log", "sample-dropped-class-locality.log",
           lambda t: "\n".join(line for line in t.splitlines()
                               if not line.startswith(f"SAMPLE locality 20 {C} ")) + "\n")

    def duplicated(t):
        out = []
        for line in t.splitlines():
            out.append(line)
            if line.startswith(f"SAMPLE locality 20 {C} "):
                out.append(line)
        return "\n".join(out) + "\n"
    mutate(outdir, "good-class-locality.log", "sample-duplicated-class-locality.log", duplicated)

    # BOTH ORDERS IN ONE LOG: one log is one process, and one process runs one term order, so the
    # carveout block cannot be attributed to one of them.
    def merged(t):
        with open(os.path.join(outdir, "good-class-census.log")) as fh:
            census = fh.read()
        return t + "".join(line for line in census.splitlines(True)
                           if not line.startswith("  carveout "))
    mutate(outdir, "good-class-locality.log", "two-orders-class-locality.log", merged)

    # ONE LANE'S SAMPLES COPIED VERBATIM ONTO ANOTHER: the bit-identical alias guard. The two ARM
    # lines still declare different cells, so nothing else can catch it.
    def aliased(t):
        donor = {}
        for line in t.splitlines():
            if line.startswith("SAMPLE locality ") and f" {HOT} " in line:
                f = line.split()
                donor[f[2]] = f[4:6]
        out = []
        for line in t.splitlines():
            if line.startswith("SAMPLE locality ") and f" {C} " in line:
                f = line.split()
                line = " ".join(f[:4] + donor[f[2]] + [f[6]])
            out.append(line)
        return "\n".join(out) + "\n"
    mutate(outdir, "good-class-locality.log", "lane-aliased-class-locality.log", aliased)

    # A lane whose SAMPLE rows name a cell its ARM line does not, in one round and in all of them.
    def kernel_forged(t, rounds):
        out = []
        for line in t.splitlines():
            if line.startswith("SAMPLE locality ") and f" {BD} " in line:
                if rounds is None or line.split()[2] in rounds:
                    line = " ".join(line.split()[:-1] + [CD_LB_K])
            out.append(line)
        return "\n".join(out) + "\n"
    mutate(outdir, "good-class-locality.log", "kernel-forged-class-locality.log",
           lambda t: kernel_forged(t, {"20"}))
    mutate(outdir, "good-class-locality.log", "body-drift-class-locality.log",
           lambda t: kernel_forged(t, None))

    # ANOTHER RUNG'S GRAMMAR: an R4 factorial log, decided under different rules.
    write(outdir, "not-r9b.log",
          "CACHE-FACTORIAL schedule order=locality lanes=11 rounds=22 warmup=2\n"
          f"ARM {CTL} 72 3 256 32768 {PAIR} 0 0 0\n"
          "CACHE-FACTORIAL done order=locality warmup=2 rounds=22 lanes=11\n")

    print(f"wrote {len(os.listdir(outdir))} fixture logs into {outdir}")


if __name__ == "__main__":
    main()
