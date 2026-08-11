#!/usr/bin/env python3
"""Generate the v3 R7 segmented-pair fixture sessions into a directory.

    python3 gpu/gkr_uniskip_bench/tools/r7_fixtures/make_fixtures.py <outdir>

Deterministic — no randomness, so a regenerated fixture is byte-identical. `check.sh`
generates into a `mktemp -d` at runtime and removes it afterwards: the fixtures are DERIVED
data, so the tracked tree carries the generator that documents them, not ~200 logs.

The grammar is the runner's: the config block, the harness's applied-carveout echo lines (one
per steered symbol), the dealt-plan `SEG` line with its `stripe=hot16` token, the frontier
`ARM` lines with their ordered admitted-id lists, one `SAMPLE` per (round, lane) in the
runner's cyclic rotation, and the `done` trailer. The lane FACTS are the real ones (C,
removals and admitted counts of the pinned arms); only the SAMPLE magnitudes are synthetic.

The dealt plan is read from the COMMITTED oracle `seg_oracle.json` — the same file the emitter
validates against — so a conforming fixture cannot drift from it and every mutant is stated as
a patch on top of it.

Every conforming session runs at the preregistered configuration: SEG-ANCHOR and SEG-SMEM at
100 rounds / 10 warmup, SEG-GMEM at 99 / 9. A per-round DRIFT term is added to every lane
alike: it cancels in the paired contrasts (that is what the rotation is for) and its median
over either round count is exactly zero, so each lane's median is its stated base.
"""

import json
import os
import sys

CTL = "control@256"
CTL_LB = "control_lb@128"
HOT = "hot16@128"
FLOOR = "seg-recompute@128"
SEGB_FLOOR = "segb-recompute@128"

PAIR = "eval_lsb_pair"
PAIR_LB = "eval_lsb_pair_128_lb"
CACHED = "eval_lsb_pair_cached_128_lb"
CV64 = "eval_lsb_seg_s_cv64"
CV100 = "eval_lsb_seg_s_cv100"
ACC = "eval_lsb_seg_s_acc"
SEG_G = "eval_lsb_seg_g"
RECOMPUTE = "eval_lsb_seg_recompute"
SEGB_G = "eval_lsb_segb_g"
SEGB_RECOMPUTE = "eval_lsb_segb_recompute"
SEGB_G_SLOTTED = "eval_lsb_segb_g_slotted"

ROTATION = {
    "SEG-ANCHOR": (CTL, HOT),
    "SEG-SMEM": (CTL, CTL_LB, HOT, FLOOR, "seg-cache0-s@128", "seg-hot16-s64@128",
                 "seg-hot16-s100@128", "seg-k24-s@128", "seg-k40-s@128",
                 "seg-hot16-acc@128"),
    "SEG-GMEM": (CTL, CTL_LB, HOT, FLOOR, "seg-cache0-g@128", "seg-hot16-g@128",
                 "seg-k24-g@128", "seg-k40-g@128", "seg-allrepeat-g@128"),
    "SEGB": (CTL, CTL_LB, HOT, SEGB_FLOOR, "segb-cache0-g@128", "segb-hot16-g@128",
             "segb-k40-g@128", "segb-hot16-g-slotted@128"),
}
ROUNDS = {"SEG-ANCHOR": (100, 10), "SEG-SMEM": (100, 10), "SEG-GMEM": (99, 9),
          "SEGB": (96, 8)}

# lane -> (regs, blocks/SM, threads, grid, kernel, C, removals, admitted). The plan facts are
# the real ones: hot16 C=28/145 removals, k24 36/161, k40 52/193, allrepeat 88/234, and the
# cache0-armed lanes (including the machinery floor) admit nothing.
FACTS = {
    CTL: (72, 3, 256, 32768, PAIR, 0, 0, 0),
    CTL_LB: (72, 7, 128, 65536, PAIR_LB, 0, 0, 0),
    HOT: (72, 7, 128, 65536, CACHED, 28, 145, 16),
    FLOOR: (72, 7, 128, 65536, RECOMPUTE, 0, 0, 0),
    "seg-cache0-s@128": (72, 7, 128, 65536, CV64, 0, 0, 0),
    "seg-hot16-s64@128": (72, 7, 128, 65536, CV64, 28, 145, 16),
    "seg-hot16-s100@128": (72, 7, 128, 65536, CV100, 28, 145, 16),
    "seg-k24-s@128": (72, 7, 128, 65536, CV100, 36, 161, 24),
    "seg-k40-s@128": (72, 7, 128, 65536, CV100, 52, 193, 40),
    "seg-hot16-acc@128": (72, 7, 128, 65536, ACC, 28, 145, 16),
    "seg-cache0-g@128": (72, 7, 128, 65536, SEG_G, 0, 0, 0),
    "seg-hot16-g@128": (72, 7, 128, 65536, SEG_G, 28, 145, 16),
    "seg-k24-g@128": (72, 7, 128, 65536, SEG_G, 36, 161, 24),
    "seg-k40-g@128": (72, 7, 128, 65536, SEG_G, 52, 193, 40),
    "seg-allrepeat-g@128": (72, 7, 128, 65536, SEG_G, 88, 234, 55),
    # The transplant lanes: four rows per block, so 4x the grid of a 16-row lane at the same
    # trace, and one published slot per warp — the 16x finalize the emitter derives.
    SEGB_FLOOR: (72, 7, 128, 262144, SEGB_RECOMPUTE, 0, 0, 0),
    "segb-cache0-g@128": (72, 7, 128, 262144, SEGB_G, 0, 0, 0),
    "segb-hot16-g@128": (72, 7, 128, 262144, SEGB_G, 28, 145, 16),
    "segb-k40-g@128": (72, 7, 128, 262144, SEGB_G, 52, 193, 40),
    "segb-hot16-g-slotted@128": (72, 7, 128, 262144, SEGB_G_SLOTTED, 28, 145, 16),
}
# The canonical admission ordering, all 55 reused sources (r5_gates.sh's transcription); a
# lane's id list is its first-K prefix.
ADMISSION = [0, 1, 2, 3, 4, 5, 48, 49, 50, 51] + list(range(6, 41)) + \
            [52, 53, 54, 55, 56, 57, 58, 41, 42, 43]

# The steered symbols and their preregistered percents. The local incumbent's percent is the
# position's, so it is filled in per log.
SEG_HINT = ((CV64, 33), (CV100, 100), (ACC, 33), (SEG_G, 16), (RECOMPUTE, 16),
            (SEGB_G, 16), (SEGB_RECOMPUTE, 16), (SEGB_G_SLOTTED, 16))

FIN_128 = 0.008192
FIN_256 = 0.006144
# The transplant reduces 16x the slots, so its finalize is a different cost and the emitter
# must never pool the two.
FIN_SEGB = 16 * FIN_128

# eval+finalize bases, ms. Plausible magnitudes off the R5/R6 anchors; the hinted incumbent
# sits ~0.09 below its unhinted frozen median.
BASE = {
    CTL: 16.624, CTL_LB: 16.100, HOT: 14.746, FLOOR: 15.900,
    "seg-cache0-s@128": 16.400, "seg-hot16-s64@128": 15.100,
    "seg-hot16-s100@128": 15.050, "seg-k24-s@128": 14.900, "seg-k40-s@128": 14.700,
    "seg-hot16-acc@128": 15.200,
    "seg-cache0-g@128": 16.300, "seg-hot16-g@128": 15.000, "seg-k24-g@128": 14.850,
    "seg-k40-g@128": 14.650, "seg-allrepeat-g@128": 15.500,
    SEGB_FLOOR: 15.500, "segb-cache0-g@128": 15.900, "segb-hot16-g@128": 14.600,
    "segb-k40-g@128": 14.400, "segb-hot16-g-slotted@128": 14.500,
}
# The census processes take the dealing-damage shift on the seg lanes, and the local lanes take
# their own census absolutes (R4's frozen anchors are per term order).
CENSUS_SHIFT = 0.060
CENSUS_LOCAL = {CTL: 16.545, CTL_LB: 16.020, HOT: 15.040}


def oracle_seg(order, path):
    with open(path) as fh:
        data = json.load(fh)
    row = next(r for r in data["orders"] if r["term_order"] == order)
    e4 = [(c - s) // 2 for c, s in zip(row["owner_components"], row["owner_stores"])]
    bf = [2 * s - c for c, s in zip(row["owner_components"], row["owner_stores"])]
    return {"list_offset": list(row["list_offset"]), "cost": list(row["predicted_cost"]),
            "e4": e4, "bf": bf, "hash": row["program_hash"], "stripe": "hot16"}


def seg_text(seg):
    j = lambda xs: ",".join(str(x) for x in xs)
    return (f"SEG list_offset={j(seg['list_offset'])} cost={j(seg['cost'])} "
            f"owners=e4:{j(seg['e4'])};bf:{j(seg['bf'])} hash={seg['hash']} "
            f"stripe={seg['stripe']}")


def drift(r):
    return 0.002 * ((r % 5) - 2)


def occupancy_rows(lanes, facts):
    """One row per distinct (symbol, dynamic slab), in lane order — the shape the harness's
    self-gate prints. Carrier S sizes its slab at `C * 256 B` floored at the reduction plane
    (2,048 fold / 6,144 acc); every other body's plane is static, and the calculator's figure
    there is a floor rather than the driver's realized partition."""
    rows, seen = [], set()
    for lane in lanes:
        symbol = facts[lane]["kernel"]
        plane = 6144 if symbol == ACC else 2048
        dynamic = max(facts[lane]["c"] * 256, plane) if symbol in (CV64, CV100, ACC) else 0
        if (symbol, dynamic) in seen:
            continue
        seen.add((symbol, dynamic))
        pin = facts[lane]["blocks_sm"]
        # A 2 KB static plane at hint 16 is where the calculator and the driver part company:
        # it models a 16.38 KB partition (5 blocks at 3.07 KB) where the driver selects
        # 32.77 KB and runs 7. Bodies with no static plane are exact.
        realized = 5 if not dynamic and symbol in (CACHED, SEG_G, RECOMPUTE) else pin
        rows.append((symbol, dynamic, realized, pin, "verified" if dynamic else "floor"))
    return rows


def bases_for(tag, order, patch=None):
    out = {lane: BASE[lane] for lane in ROTATION[tag]}
    if order == "census":
        for lane in out:
            if lane.startswith(("seg-", "segb-")):
                out[lane] += CENSUS_SHIFT
            elif lane in CENSUS_LOCAL:
                out[lane] = CENSUS_LOCAL[lane]
    if patch:
        out.update(patch)
    return out


def log(tag, order, hint, *, bases=None, rounds=None, warmup=None, echoes=None, seg="auto",
        seg_patch=None, wobble=None, arm_patch=None, lanes=None, drop=None, dup=None,
        done=True, sample_order=None, rotate=True, oracle=None, renumber=None):
    """One process. Everything a mutant needs to bend is a keyword here, so the mutation is
    visible in the scenario list rather than buried in a post-hoc text edit."""
    lanes = list(lanes if lanes is not None else ROTATION[tag])
    bases = bases if bases is not None else bases_for(tag, order)
    n = len(lanes)
    r_rounds, r_warmup = ROUNDS[tag]
    rounds = r_rounds if rounds is None else rounds
    warmup = r_warmup if warmup is None else warmup
    facts = {lane: dict(zip(
        ("regs", "blocks_sm", "threads", "grid", "kernel", "c", "removals", "admitted"),
        FACTS[lane]), ids=None) for lane in lanes}
    for lane, patch in (arm_patch or {}).items():
        facts[lane].update(patch)

    if echoes is None:
        echoes = [(CACHED, hint)] + [(sym, pct) for sym, pct in SEG_HINT
                                     if any(facts[l]["kernel"] == sym for l in lanes)]
    out = [
        "gpu_gkr_uniskip_bench config",
        "  mode                lsb-pair",
        f"  cache_arm           {tag.lower()} ({n} lanes)",
        "  block_threads       256 + 128 (both, per lane)",
        f"  term_order          {order}",
        "  carrier             per lane (see the ARM lines)",
    ]
    for symbol, pct in echoes:
        out.append(f"  carveout hint       {pct}% ({symbol})")
    # The harness's occupancy self-gate lines. The emitter has no contract on them — the
    # realized block count is gated in the binary, not in the log — so they are here to prove
    # it TOLERATES them rather than to be parsed. A conforming log carries them.
    for symbol, dynamic, realized, pin, verdict in occupancy_rows(lanes, facts):
        out.append(f"  occupancy           {realized} blocks/SM ({symbol}, {dynamic} B "
                   f"dynamic, pin {pin}, {verdict})")
    out += [
        "work",
        "  device              NVIDIA RTX PRO 6000 Blackwell Server Edition",
        f"{tag} schedule order={order} lanes={n} rounds={rounds} warmup={warmup}",
    ]
    if seg == "auto":
        seg = oracle_seg(order, oracle) if tag != "SEG-ANCHOR" else None
    if isinstance(seg, dict):
        seg = dict(seg)
        seg.update(seg_patch or {})
        out.append(seg_text(seg))
    elif isinstance(seg, str):
        out.append(seg)
    for lane in lanes:
        f = facts[lane]
        ids = f.get("ids") or (
            ",".join(str(i) for i in ADMISSION[:f["admitted"]]) if f["admitted"] else "-")
        out.append(f"ARM {lane} {f['regs']} {f['blocks_sm']} {f['threads']} {f['grid']} "
                   f"{f['kernel']} {f['c']} {f['removals']} {f['admitted']} {ids}")
    for i in range(rounds):
        r = warmup + i
        for j in range(n):
            lane = lanes[(r % n + j) % n] if rotate else lanes[j]
            if drop == (r, lane):
                continue
            metric = bases[lane] + drift(r) + (wobble(lane, r) if wobble else 0.0)
            if facts[lane]["kernel"].startswith("eval_lsb_segb"):
                fin = FIN_SEGB
            else:
                fin = FIN_256 if facts[lane]["threads"] == 256 else FIN_128
            # `renumber` moves one round's id off the consecutive run without changing how many
            # rounds carry samples — the shape a count-only check accepts.
            stamped = renumber[1] if renumber and r == renumber[0] else r
            row = (f"SAMPLE {sample_order or order} {stamped} {lane} {metric - fin:.6f} "
                   f"{fin:.6f} {facts[lane]['kernel']}")
            out.append(row)
            if dup == (r, lane):
                out.append(row)
    if done:
        out.append(f"{tag} done order={order} warmup={warmup} rounds={rounds} lanes={n}")
    return out


POSITIONS = ("reanchor-census", "reanchor-locality", "smem-locality", "smem-census",
             "gmem-locality", "gmem-census", "attr-cv64", "attr-cv100")


def specs(oracle):
    """The eight conforming processes, as `log` kwargs. The attribution processes differ from
    the locality re-anchor ONLY in the incumbent's hint and in what that hint bought."""
    return [
        dict(tag="SEG-ANCHOR", order="census", hint=16, oracle=oracle),
        dict(tag="SEG-ANCHOR", order="locality", hint=16, oracle=oracle),
        dict(tag="SEG-SMEM", order="locality", hint=16, oracle=oracle),
        dict(tag="SEG-SMEM", order="census", hint=16, oracle=oracle),
        dict(tag="SEG-GMEM", order="locality", hint=16, oracle=oracle),
        dict(tag="SEG-GMEM", order="census", hint=16, oracle=oracle),
        dict(tag="SEG-ANCHOR", order="locality", hint=32, oracle=oracle,
             bases=bases_for("SEG-ANCHOR", "locality", {HOT: 14.700})),
        dict(tag="SEG-ANCHOR", order="locality", hint=100, oracle=oracle,
             bases=bases_for("SEG-ANCHOR", "locality", {HOT: 14.810})),
    ]


SEGB_POSITIONS = ("reanchor-census", "reanchor-locality", "segb-locality", "segb-census",
                  "r7-gmem-locality", "r7-gmem-census")


def segb_specs(oracle):
    """R7b's six positional processes: the two re-anchors, the SEGB rotation at both orders,
    and R7's own gmem session (positions 5-6, optional at the emitter) — the logs that make
    the walk-floor comparison a difference of two IN-SESSION differentials."""
    return [
        dict(tag="SEG-ANCHOR", order="census", hint=16, oracle=oracle),
        dict(tag="SEG-ANCHOR", order="locality", hint=16, oracle=oracle),
        dict(tag="SEGB", order="locality", hint=16, oracle=oracle),
        dict(tag="SEGB", order="census", hint=16, oracle=oracle),
        dict(tag="SEG-GMEM", order="locality", hint=16, oracle=oracle),
        dict(tag="SEG-GMEM", order="census", hint=16, oracle=oracle),
    ]


def write(outdir, name, lines):
    with open(os.path.join(outdir, name), "w") as fh:
        fh.write("\n".join(lines) + "\n")


def session(outdir, name, oracle, patches=None, order=None):
    """One eight-log session. `patches` maps a POSITION INDEX to `log` kwargs overrides;
    `order` re-orders which spec lands in which file, for the positional mutants."""
    rows = specs(oracle)
    for i, patch in (patches or {}).items():
        rows[i] = dict(rows[i], **patch)
    if order:
        rows = [rows[i] for i in order]
    for tag, spec in zip(POSITIONS, rows):
        write(outdir, f"{name}-{tag}.log", log(**spec))


def segb_session(outdir, name, oracle, patches=None, order=None):
    """One R7b session, same contract as `session` over R7b's own positional inventory."""
    rows = segb_specs(oracle)
    for i, patch in (patches or {}).items():
        rows[i] = dict(rows[i], **patch)
    if order:
        rows = [rows[i] for i in order]
    for tag, spec in zip(SEGB_POSITIONS, rows):
        write(outdir, f"{name}-{tag}.log", log(**spec))


def main():
    if len(sys.argv) != 2:
        sys.exit(f"usage: {sys.argv[0]} <outdir>")
    outdir = sys.argv[1]
    os.makedirs(outdir, exist_ok=True)
    here = os.path.dirname(os.path.abspath(__file__))
    oracle = os.path.join(here, "seg_oracle.json")

    # 1. THE CONFORMING SESSION. Every table's shape is proved on this one.
    session(outdir, "good", oracle)

    # 1b. The sign-stability count, pinned from both sides. seg-k40-s beats hot16 by 0.046 ms in
    #     most rounds and loses by 0.154 in the wobbled ones, so the median stays -0.046 either
    #     way and only the on-sign count moves: 90/100 is at the reported ceil(0.9 N) threshold,
    #     89/100 is below it. A fixture set whose lanes are all 100/100 would not notice the
    #     literal moving at all.
    def flip(rs):
        return lambda lane, r: 0.200 if lane == "seg-k40-s@128" and r in rs else 0.0

    session(outdir, "sign-at-threshold", oracle,
            {2: dict(wobble=flip(set(range(10, 20))))})
    session(outdir, "sign-below-threshold", oracle,
            {2: dict(wobble=flip(set(range(10, 21))))})

    # 1c. The NON-FATAL bands and the mechanical triggers, each fired on its own:
    #     control@256 3 % off its frozen median (the only like-for-like re-anchor lane), the
    #     bridge flank between the two rotations, and the Step 7 first-cycle/last-cycle drift.
    shift = 0.03 * BASE[CTL]
    session(outdir, "anchor-out-of-band", oracle,
            {1: dict(bases=bases_for("SEG-ANCHOR", "locality", {CTL: BASE[CTL] + shift}))})
    session(outdir, "bridge-flank-unstable", oracle,
            {4: dict(bases=bases_for("SEG-GMEM", "locality", {CTL: BASE[CTL] + 0.200,
                                                              HOT: BASE[HOT] + 0.200}))})
    # A monotone ramp on one anchor: its first and last full-cycle block medians are 0.2 ms
    # apart, which is the repeat trigger and nothing else (the paired contrasts are unmoved).
    session(outdir, "repeat-trigger-fired", oracle,
            {2: dict(wobble=lambda lane, r: 0.002 * (r - 10))})

    # 2. THE APPLIED CARVEOUT, per symbol. The percent IS the configuration under test, so a
    #    wrong, missing or spurious echo is a different arm — one row per symbol.
    gmem_echo = [(CACHED, 16), (SEG_G, 16), (RECOMPUTE, 16)]
    for name, pos, echo in (
            ("echo-cv64-wrong", 2, [(CACHED, 16), (CV64, 16), (CV100, 100), (ACC, 33),
                                    (RECOMPUTE, 16)]),
            ("echo-cv100-wrong", 2, [(CACHED, 16), (CV64, 33), (CV100, 33), (ACC, 33),
                                     (RECOMPUTE, 16)]),
            ("echo-acc-wrong", 2, [(CACHED, 16), (CV64, 33), (CV100, 100), (ACC, 100),
                                   (RECOMPUTE, 16)]),
            ("echo-recompute-wrong", 4, [(CACHED, 16), (SEG_G, 16), (RECOMPUTE, 32)]),
            ("echo-g-wrong", 4, [(CACHED, 16), (SEG_G, 32), (RECOMPUTE, 16)]),
            ("echo-incumbent-wrong", 2, [(CACHED, 32), (CV64, 33), (CV100, 100), (ACC, 33),
                                         (RECOMPUTE, 16)]),
            ("echo-cv100-missing", 2, [(CACHED, 16), (CV64, 33), (ACC, 33),
                                       (RECOMPUTE, 16)]),
            ("echo-incumbent-missing", 4, [(SEG_G, 16), (RECOMPUTE, 16)]),
            ("echo-spurious-seg", 1, [(CACHED, 16), (SEG_G, 16)]),
            ("echo-attr-not-32", 6, [(CACHED, 16)]),
            ("echo-attr-not-100", 7, [(CACHED, 32)]),
    ):
        session(outdir, name, oracle, {pos: dict(echoes=echo)})
    session(outdir, "echo-malformed", oracle,
            {2: dict(echoes=[(CACHED, 16), (CV64, 33), (CV100, 100), (ACC, 33),
                             (RECOMPUTE, 16)])})
    path = os.path.join(outdir, "echo-malformed-smem-locality.log")
    kept = [("  carveout hint 33% (eval_lsb_seg_s_cv64)"
             if ln == f"  carveout hint       33% ({CV64})" else ln)
            for ln in open(path).read().splitlines()]
    write(outdir, "echo-malformed-smem-locality.log", kept)
    # A second echo for one symbol: the carveout is set once, before any launch.
    session(outdir, "echo-doubled", oracle,
            {4: dict(echoes=gmem_echo + [(SEG_G, 16)])})
    # Unused-symbol echo on a rotation that has no such lane.
    session(outdir, "echo-unused-symbol", oracle,
            {4: dict(echoes=gmem_echo + [(CV100, 100)])})

    # 3. THE DEALT PLAN. Absent, forbidden, malformed, or drifted from the committed oracle in
    #    any one field — including a drift both rotation logs of one order AGREE on, which is
    #    exactly the case cross-log agreement alone would pass.
    session(outdir, "seg-missing", oracle, {2: dict(seg=None)})
    session(outdir, "seg-on-anchor", oracle,
            {1: dict(seg=oracle_seg("locality", oracle))})
    session(outdir, "seg-no-stripe-token", oracle,
            {2: dict(seg=seg_text(oracle_seg("locality", oracle)).rsplit(" stripe=", 1)[0])})
    session(outdir, "seg-wrong-stripe", oracle,
            {2: dict(seg_patch={"stripe": "k40"})})
    session(outdir, "seg-hash-drift", oracle,
            {2: dict(seg_patch={"hash": "dead3ceb1e5b0a17"})})
    both = {"hash": "dead3ceb1e5b0a17"}
    session(outdir, "seg-hash-forged-consistently", oracle,
            {2: dict(seg_patch=both), 4: dict(seg_patch=both)})
    off_atom = oracle_seg("locality", oracle)["list_offset"]
    session(outdir, "seg-offsets-off-atom", oracle,
            {2: dict(seg_patch={"list_offset": [off_atom[0], off_atom[1] + 1] +
                                off_atom[2:]})})
    session(outdir, "seg-cost-drift", oracle,
            {2: dict(seg_patch={"cost": [999] + oracle_seg("locality", oracle)["cost"][1:]})})
    session(outdir, "seg-owners-drift", oracle,
            {2: dict(seg_patch={"e4": [2, 0, 1, 1]})})
    session(outdir, "seg-malformed", oracle,
            {2: dict(seg="SEG list_offset=0,46,89,132 cost=759,713,772,744 owners=e4:1,1,1,1;"
                         "bf:3,3,3,3 hash=02dbf4b0cd52aae9 stripe=hot16")})
    # The census log carrying the LOCALITY plan: each log is validated against its own order.
    session(outdir, "seg-order-swapped", oracle,
            {3: dict(seg=oracle_seg("locality", oracle))})

    # 4. THE POSITIONAL PINS. Each of these is a well-formed log in the wrong slot, which is
    #    what makes the eight-log contract positional in the first place.
    session(outdir, "pos-smem-in-gmem-slot", oracle, order=[0, 1, 2, 3, 2, 5, 6, 7])
    session(outdir, "pos-orders-swapped", oracle, order=[0, 1, 3, 2, 4, 5, 6, 7])
    session(outdir, "pos-attr-swapped", oracle, order=[0, 1, 2, 3, 4, 5, 7, 6])
    session(outdir, "pos-anchor-in-headline", oracle, order=[0, 1, 1, 3, 4, 5, 6, 7])

    # 5. THE ROUND PINS. The reported threshold is keyed to the round count, and the warmup is
    #    a whole number of rotations.
    session(outdir, "rounds-not-100", oracle, {2: dict(rounds=50)})
    session(outdir, "rounds-not-99", oracle, {4: dict(rounds=90)})
    session(outdir, "warmup-not-10", oracle, {2: dict(warmup=5)})

    # 6. THE ROTATION. A lane that keeps a slot carries that slot's clock state into its
    #    median, which is exactly what the pairing exists to remove.
    session(outdir, "rotation-fixed", oracle, {4: dict(rotate=False)})

    # 7. Mixed and truncated logs.
    session(outdir, "order-forged-in-samples", oracle,
            {2: dict(sample_order="census")})
    session(outdir, "no-done-trailer", oracle, {4: dict(done=False)})
    # Round 15 stamped as 210: still 100 rounds carrying samples, but no longer the consecutive
    # run the runner numbers, which is how a renumbered or spliced log reads.
    session(outdir, "round-renumbered", oracle, {2: dict(renumber=(15, 210))})
    session(outdir, "sample-dropped", oracle, {2: dict(drop=(15, "seg-k24-s@128"))})
    session(outdir, "sample-duplicated", oracle, {2: dict(dup=(15, "seg-k24-s@128"))})

    # 8. THE LANE SET AND THE LANE FACTS.
    session(outdir, "lane-missing", oracle,
            {2: dict(lanes=[l for l in ROTATION["SEG-SMEM"] if l != "seg-k40-s@128"])})
    session(outdir, "lane-symbol-forged", oracle,
            {2: dict(arm_patch={"seg-hot16-s64@128": {"kernel": SEG_G}})})
    session(outdir, "lane-facts-drift", oracle,
            {4: dict(arm_patch={HOT: {"c": 36}})})
    session(outdir, "lane-ids-short", oracle,
            {2: dict(arm_patch={"seg-k40-s@128": {"ids": "0,1,2,3"}})})
    # One lane's data under two labels — R3's aliasing shape, which reads as a clean +0.000.
    session(outdir, "lane-aliased", oracle,
            {4: dict(bases=bases_for("SEG-GMEM", "locality",
                                     {"seg-k24-g@128": BASE["seg-hot16-g@128"]}))})

    # 9. A log from another rung entirely (the R6 probe grammar), so the emitter cannot be
    #    pointed at another rung's session and summarize it under R7's rules.
    write(outdir, "not-r7.log", [
        "  carveout hint       16% (eval_lsb_pair_cached_128_lb)",
        "CARVEOUT-PROBE schedule order=locality lanes=5 rounds=100 warmup=10 "
        "carveout-hint=16",
        f"ARM {HOT} 72 7 128 65536 {CACHED} 28 145 16 0,1,2,3,4,5,48,49,50,51,6,7,8,9,10,11",
        f"SAMPLE locality 10 {HOT} 14.828000 0.008192 {CACHED}",
        "CARVEOUT-PROBE done order=locality warmup=10 rounds=100 lanes=5",
    ])

    # 9b. R7b's SEGB session, and the mutants of its own contract: the positional pin (an R7
    #     rotation in the SEGB slot), the dealt plan a transplant rotation must carry, the
    #     round pin, the per-symbol carveout of the slotted body, the lane's symbol, and a
    #     supplied R7 log whose shared lanes come from another build.
    segb_session(outdir, "segb", oracle)
    segb_session(outdir, "segb-wrong-tag", oracle, order=[0, 1, 4, 3, 4, 5])
    segb_session(outdir, "segb-seg-missing", oracle, {2: dict(seg=None)})
    segb_session(outdir, "segb-rounds-not-96", oracle, {2: dict(rounds=100)})
    segb_session(outdir, "segb-echo-slotted-wrong", oracle,
                 {2: dict(echoes=[(CACHED, 16), (SEGB_G, 16), (SEGB_RECOMPUTE, 16),
                                  (SEGB_G_SLOTTED, 32)])})
    segb_session(outdir, "segb-lane-symbol-forged", oracle,
                 {2: dict(arm_patch={"segb-hot16-g-slotted@128": {"kernel": SEGB_G}})})
    segb_session(outdir, "segb-r7-other-build", oracle,
                 {4: dict(arm_patch={HOT: {"c": 36}})})

    # 10. A DIFFERENT ORACLE. The committed file's own contract is pinned field by field, so a
    #     redirected oracle that documents another hash algorithm, another reference stripe or
    #     another segment count is not the one these rules are registered against. The verbatim
    #     COPY is here too: it is accepted, and the emitted record has to say out loud that the
    #     oracle was redirected (a matching forged oracle + log pair is what the committed-file
    #     rule exists to prevent, so a redirect must never be invisible).
    def variant(name, patch):
        with open(oracle) as fh:
            data = json.load(fh)
        patch(data)
        with open(os.path.join(outdir, name), "w") as fh:
            json.dump(data, fh)

    variant("oracle-copy.json", lambda d: None)
    variant("oracle-wrong-algo.json", lambda d: d.update(program_hash_algo="sha256"))
    variant("oracle-wrong-stripe.json", lambda d: d.update(owner_arm="k40"))
    variant("oracle-wrong-seg-k.json", lambda d: d.update(seg_k=3))
    variant("oracle-no-locality.json", lambda d: d.update(
        orders=[r for r in d["orders"] if r["term_order"] != "locality"]))


if __name__ == "__main__":
    main()
