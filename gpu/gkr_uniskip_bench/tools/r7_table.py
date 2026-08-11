#!/usr/bin/env python3
"""Emit the v3 R7 segmented-pair (seg-K4) decision from one session's EIGHT logs.

R7 NOTE. This script is THE SINGLE AUTHORITY for every derived figure of the rung — the
per-lane medians, the paired contrasts and their sign-stability counts, the machinery
decomposition, the capture slopes, the S-vs-G carrier contrast, the carveout attribution, the
re-anchor comparison and the Step 7 repeat trigger. Nothing decision-bearing is computed by
hand or in the record (Task 8 quotes this output verbatim; the R1 lesson).

R7 PREREGISTERS NO CLOSURE THRESHOLD (spec, RR ruling): every arm is a datapoint about where
the optimum might be. The sign-stability counts are therefore REPORTED against ceil(0.9 N),
never turned into a win/loss verdict here, and no row selects a winner.

Everything decision-bearing is read from IN-LOG metadata — the tag, the term order, the hint
echoes, the round count, the lane plans, the dealt-plan identity. A FILENAME NEVER DECIDES
ANYTHING: the eight logs are POSITIONAL and each position pins the tag, the term order and
the incumbent's carveout hint it must carry, so a mis-ordered set is rejected rather than
summarized under the wrong pairing:

    1 reanchor-census    SEG-ANCHOR census    hint 16
    2 reanchor-locality  SEG-ANCHOR locality  hint 16
    3 smem-locality      SEG-SMEM   locality  hint 16   (headline)
    4 smem-census        SEG-SMEM   census    hint 16   (dealing damage; NEVER pooled)
    5 gmem-locality      SEG-GMEM   locality  hint 16
    6 gmem-census        SEG-GMEM   census    hint 16   (dealing damage; NEVER pooled)
    7 attr-cv64          SEG-ANCHOR locality  hint 32
    8 attr-cv100         SEG-ANCHOR locality  hint 100

The dealt plan is validated against the COMMITTED oracle `r7_fixtures/seg_oracle.json`, which
Task 2 emits from the host dealer and which is independent of the timed binary: the SEG line's
offsets, per-list costs, owner census, program hash and reference-stripe token must EQUAL the
oracle for the log's own term order. Cross-log agreement alone is NOT accepted — a
consistently forged plan would pass it. A SEG-ANCHOR log carrying a SEG line is a mislabelled
log and is rejected: the anchor rotation deals nothing.

Contrasts inside one rotation are PAIRED per round (the runner executes every lane once per
round in a cyclic rotation, so a round's lanes share that round's clock state). Contrasts
ACROSS the two rotations cannot be paired at all, so they ride the anchors both rotations
carry — `control@256` and the hinted `hot16@128` — exactly as R4/R5 bridged their sessions.
The metric is `eval + finalize`, R5's bar currency: the 128 lanes run twice the grid, so
finalize is not the same work on the two block sizes and the cross-size anchor cannot be
compared on `eval` alone.

The lane SET is pinned per rotation (label AND symbol — the S-vs-G contrast is a claim about
which body a lane ran), and so are the rounds/warmup per set and the hint per symbol. The lane
FACTS — registers, blocks/SM, threads, grid, C, removals, admitted ids — are DATA, read off the
`ARM` lines the runner fills from each lane's own plan. No C, removal count or kernel-name
constant is written here beyond that inventory.

R7b (the SEGB transplant) rides the same machinery under its OWN positional inventory, which
the emitter selects from the LOGS' tag — never from a flag or a filename. R7's eight-log
contract is untouched by it: a set carrying no `SEGB` schedule line is summarized exactly as
before, byte for byte.

    1 reanchor-census    SEG-ANCHOR census    hint 16
    2 reanchor-locality  SEG-ANCHOR locality  hint 16
    3 segb-locality      SEGB       locality  hint 16   (headline)
    4 segb-census        SEGB       census    hint 16   (dealing damage; NEVER pooled)
    5 r7-gmem-locality   SEG-GMEM   locality  hint 16   (optional, R7's own session)
    6 r7-gmem-census     SEG-GMEM   census    hint 16   (optional, R7's own session)

Positions 5 and 6 are the R7 rotation's logs, and they are what makes the R7-vs-R7b walk-floor
comparison legal: it is the difference of two IN-SESSION differentials (`segb-recompute −
control_lb` here against `seg-recompute − control_lb` there), per term order, never a raw
cross-session median. Supply them or don't; with them the comparison is emitted, without them
only this session's half is. R7b's lane grids are pinned to `--log-trace 24` on top of that:
the trace size is printed in no decision-bearing line, so a four-log set recorded at another
one is self-consistent and no cross-log gate can see it.

Usage:
    python3 gpu/gkr_uniskip_bench/tools/r7_table.py L1 L2 L3 L4 L5 L6 L7 L8
    python3 gpu/gkr_uniskip_bench/tools/r7_table.py S1 S2 S3 S4 [S5 S6]
    python3 gpu/gkr_uniskip_bench/tools/r7_table.py --seg-line <census|locality>

The last form prints the SEG line the committed oracle implies and exits — `r7_gates.sh`
compares the runner's line against it, so the plan identity has ONE source of truth.
"""

import json
import os
import re
import sys
from collections import defaultdict
from statistics import median

TAGS = ("SEG-ANCHOR", "SEG-SMEM", "SEG-GMEM", "SEGB")
TAG_RE = "|".join(TAGS)
SCHED = re.compile(
    rf"^({TAG_RE}) schedule order=(\S+) lanes=(\d+) rounds=(\d+) warmup=(\d+)"
    r"(?: carveout-hint=(default|\d+))?$"
)
DONE = re.compile(rf"^({TAG_RE}) done order=(\S+) warmup=(\d+) rounds=(\d+) lanes=(\d+)$")
ARM = re.compile(r"^ARM (\S+) (\d+) (\d+) (\d+) (\d+) (\S+) (\d+) (\d+) (\d+) (\S+)$")
SAMPLE = re.compile(r"^SAMPLE (\S+) (\d+) (\S+) ([\d.]+) ([\d.]+) (\S+)$")
# The harness's APPLIED-hint echo, matched on the RAW line (its indentation is part of the
# runner's literal). The schedule line states what was REQUESTED — and for the seg symbols it
# states nothing at all; these lines are printed after `cudaFuncSetAttribute` actually ran, so
# they are what pins a process's carveout state, per symbol.
ECHO = re.compile(r"^  carveout hint       (\d+)% \(([a-z0-9_]+)\)$")
ECHO_ANY = "carveout hint"
# The dealt-plan identity line. `stripe=hot16` is a LITERAL: the owner census printed is
# always the hot16 REFERENCE stripe (the arm the committed oracle pins), never the run's own
# prologue striping — the token exists so the census cannot be misread as the latter.
SEG = re.compile(
    r"^SEG list_offset=(\d+(?:,\d+){4}) cost=(\d+(?:,\d+){3}) "
    r"owners=e4:(\d+(?:,\d+){3});bf:(\d+(?:,\d+){3}) hash=([0-9a-f]{16}) stripe=(\S+)$"
)

LOCAL_INCUMBENT = "eval_lsb_pair_cached_128_lb"
CTL = "control@256"
CTL_LB = "control_lb@128"
HOT = "hot16@128"
FLOOR = "seg-recompute@128"

# R7b's transplant lanes and bodies.
SEGB_FLOOR = "segb-recompute@128"
SEGB_CACHE0 = "segb-cache0-g@128"
SEGB_HOT = "segb-hot16-g@128"
SEGB_K40 = "segb-k40-g@128"
SEGB_SLOTTED = "segb-hot16-g-slotted@128"
SEGB_G = "eval_lsb_segb_g"
SEGB_RECOMPUTE = "eval_lsb_segb_recompute"
SEGB_G_SLOTTED = "eval_lsb_segb_g_slotted"
# A6: the ARM grammar carries no slot field, so the finalize slot count is DERIVED from the
# lane's carrier (its symbol) and its block count — a transplant block is four rows and
# publishes one slot per warp, every other body publishes one slot per block.
SEGB_PARTIALS_PER_BLOCK = 4

# THE TRACE PIN, R7b's own. Every other gate here is RELATIVE — logs are checked against each
# other and against the committed plan oracle — and the trace size appears in no log line at
# all, so a whole session recorded at another `--log-trace` is internally consistent. The
# six-log form still catches it (R7's supplied logs share three lanes, and the lane-plan
# identity gate compares their grids), but the four-log form has nothing to compare against.
# These are the grids R7b's arms are preregistered at, one per lane of the SEGB rotation: the
# trace's row count over each body's row tile, which is a fact of the build and the trace and
# of nothing else. Lanes outside this table ride the identity gate against the ones in it.
SEGB_TRACE = 24
SEGB_TRACE_GRID = {
    CTL: 32768,
    CTL_LB: 65536,
    HOT: 65536,
    SEGB_FLOOR: 262144,
    SEGB_CACHE0: 262144,
    SEGB_HOT: 262144,
    SEGB_K40: 262144,
    SEGB_SLOTTED: 262144,
}

# THE PINNED ROTATIONS — label and symbol, in execution order. A log carrying a different lane
# set is a different experiment and is rejected rather than partially summarized; a lane
# carrying a different SYMBOL is a claim this rung's carrier contrast is made OF, so it is
# pinned as well.
ROTATION = {
    "SEG-ANCHOR": (
        (CTL, "eval_lsb_pair"),
        (HOT, LOCAL_INCUMBENT),
    ),
    "SEG-SMEM": (
        (CTL, "eval_lsb_pair"),
        (CTL_LB, "eval_lsb_pair_128_lb"),
        (HOT, LOCAL_INCUMBENT),
        (FLOOR, "eval_lsb_seg_recompute"),
        ("seg-cache0-s@128", "eval_lsb_seg_s_cv64"),
        ("seg-hot16-s64@128", "eval_lsb_seg_s_cv64"),
        ("seg-hot16-s100@128", "eval_lsb_seg_s_cv100"),
        ("seg-k24-s@128", "eval_lsb_seg_s_cv100"),
        ("seg-k40-s@128", "eval_lsb_seg_s_cv100"),
        ("seg-hot16-acc@128", "eval_lsb_seg_s_acc"),
    ),
    "SEG-GMEM": (
        (CTL, "eval_lsb_pair"),
        (CTL_LB, "eval_lsb_pair_128_lb"),
        (HOT, LOCAL_INCUMBENT),
        (FLOOR, "eval_lsb_seg_recompute"),
        ("seg-cache0-g@128", "eval_lsb_seg_g"),
        ("seg-hot16-g@128", "eval_lsb_seg_g"),
        ("seg-k24-g@128", "eval_lsb_seg_g"),
        ("seg-k40-g@128", "eval_lsb_seg_g"),
        ("seg-allrepeat-g@128", "eval_lsb_seg_g"),
    ),
    "SEGB": (
        (CTL, "eval_lsb_pair"),
        (CTL_LB, "eval_lsb_pair_128_lb"),
        (HOT, LOCAL_INCUMBENT),
        (SEGB_FLOOR, SEGB_RECOMPUTE),
        (SEGB_CACHE0, SEGB_G),
        (SEGB_HOT, SEGB_G),
        (SEGB_K40, SEGB_G),
        (SEGB_SLOTTED, SEGB_G_SLOTTED),
    ),
}

# The preregistered round counts per set (spec R7; the warmup is a whole number of rotations
# in every case). The signed threshold is keyed to the round count, so this is a pin, not a
# reading.
ROUNDS = {"SEG-ANCHOR": (100, 10), "SEG-SMEM": (100, 10), "SEG-GMEM": (99, 9),
          "SEGB": (96, 8)}

# The carveout each symbol is set to before any launch — the percent IS the carrier's
# configuration under test. The percent is NOT portable across the shared-memory kind: the
# static-shared incumbent reaches 65.54 KB at 24..40, while the DYNAMIC-shared carrier-S
# bodies only cross it at 33 (32 realizes 32.77 KB and 4 blocks/SM — R7's first G0 aborted
# on exactly that). Tiers here: 33 -> 65.54 KB, 100 -> 102.40 KB, 16 -> 32.77 KB. `cv64` and
# `cv100` are ONE body under two symbols precisely because the attribute is per-function and
# sticky.
SYMBOL_HINT = {
    "eval_lsb_seg_s_cv64": 33,
    "eval_lsb_seg_s_cv100": 100,
    "eval_lsb_seg_s_acc": 33,
    "eval_lsb_seg_g": 16,
    "eval_lsb_seg_recompute": 16,
    # The transplant bodies hold no dynamic shared memory, and the slotted one is EQUALIZED
    # to carrier G's realized CONFIGURATION on purpose: its SHARED:8 would otherwise move the
    # L1/shared partition under the `slotted − segb-hot16-g` row (A9b). Those static bytes
    # also put it on a different hint ladder (R7b G0: 2 -> 32.77 KB on the slotted symbol, 16
    # -> 32.77 KB on the zero-shared ones, 16 -> 102.40 KB on the slotted), so the equalized
    # percents are UNEQUAL and 16 on all three would be the confound, not the control.
    SEGB_G: 16,
    SEGB_RECOMPUTE: 16,
    SEGB_G_SLOTTED: 2,
}

# position -> (name, tag, term order, the LOCAL incumbent's hint). The incumbent's percent is
# the only one that varies by position: it is 16 everywhere except on the two attribution
# processes, which are the same two-lane rotation differing ONLY in that hint.
POSITIONS = (
    ("reanchor-census", "SEG-ANCHOR", "census", 16),
    ("reanchor-locality", "SEG-ANCHOR", "locality", 16),
    ("smem-locality", "SEG-SMEM", "locality", 16),
    ("smem-census", "SEG-SMEM", "census", 16),
    ("gmem-locality", "SEG-GMEM", "locality", 16),
    ("gmem-census", "SEG-GMEM", "census", 16),
    ("attr-cv64", "SEG-ANCHOR", "locality", 32),
    ("attr-cv100", "SEG-ANCHOR", "locality", 100),
)
REANCHOR, HEADLINE, ATTR = 1, 2, (1, 6, 7)

# R7b's own positional inventory. The first four are required; positions 5 and 6 are R7's
# gmem logs, which turn the walk-floor comparison into a difference of two IN-SESSION
# differentials (A4) instead of a raw cross-session subtraction.
SEGB_POSITIONS = (
    ("reanchor-census", "SEG-ANCHOR", "census", 16),
    ("reanchor-locality", "SEG-ANCHOR", "locality", 16),
    ("segb-locality", "SEGB", "locality", 16),
    ("segb-census", "SEGB", "census", 16),
    ("r7-gmem-locality", "SEG-GMEM", "locality", 16),
    ("r7-gmem-census", "SEG-GMEM", "census", 16),
)
SEGB_HEADLINE = 2
SEGB_COUNTS = (4, 6)
COUNT_WORDS = {4: "four", 6: "six", 8: "eight"}

# The committed dealer oracle. Overridable for the fixture suite ONLY — the override cannot
# weaken anything, since a redirected oracle that does not match the logs rejects them.
ORACLE_ENV = "R7_SEG_ORACLE"
ORACLE_DEFAULT = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                              "r7_fixtures", "seg_oracle.json")
ORACLE_ALGO = "fnv1a64"
ORACLE_STRIPE = "hot16"
ORACLE_SEG_K = 4

# The machinery decomposition, per rotation: (minuend, subtrahend, what it isolates). Each row
# prints both sides' symbols, so a row that crosses two bodies says so in the table.
DECOMPOSE = {
    "SEG-SMEM": (
        ("seg-cache0-s@128", FLOOR, "publish machinery at zero capture"),
        ("seg-hot16-s64@128", "seg-cache0-s@128", "capture at hot16, 64 KiB request"),
        ("seg-hot16-s100@128", "seg-cache0-s@128", "capture at hot16, 100 KiB request"),
        ("seg-hot16-acc@128", "seg-hot16-s64@128", "accumulator-first reduction A/B"),
    ),
    "SEG-GMEM": (
        ("seg-cache0-g@128", FLOOR, "publish machinery at zero capture"),
        ("seg-hot16-g@128", "seg-cache0-g@128", "capture at hot16"),
    ),
}

# The capture slope, per rotation: (capture lane, matched hot16 lane of the SAME symbol). The
# divisor is the removals DELTA off the two ARM lines — never a literal here.
SLOPES = {
    "SEG-SMEM": (
        ("seg-k24-s@128", "seg-hot16-s100@128"),
        ("seg-k40-s@128", "seg-hot16-s100@128"),
    ),
    "SEG-GMEM": (
        ("seg-k24-g@128", "seg-hot16-g@128"),
        ("seg-k40-g@128", "seg-hot16-g@128"),
        ("seg-allrepeat-g@128", "seg-hot16-g@128"),
    ),
}

# The S-vs-G carrier contrast, at MATCHED capture: (label, S lane, G lane).
MATCHED = (
    ("machinery floor", FLOOR, FLOOR),
    ("cache0", "seg-cache0-s@128", "seg-cache0-g@128"),
    ("hot16", "seg-hot16-s64@128", "seg-hot16-g@128"),
    ("hot16, 100 KiB request", "seg-hot16-s100@128", "seg-hot16-g@128"),
    ("k24", "seg-k24-s@128", "seg-k24-g@128"),
    ("k40", "seg-k40-s@128", "seg-k40-g@128"),
)
# The two lanes both rotations carry. Every cross-rotation figure rides them, never raw.
BRIDGES = (CTL, HOT)

# R7b's decision rows, in reading order: (minuend, subtrahend, what it isolates, per-removal).
# The last flag prints the paired median over the removals DELTA off the two ARM lines, so the
# slope carries no divisor of its own here either.
SEGB_DECISIONS = (
    (SEGB_CACHE0, SEGB_FLOOR,
     "the empty-plan / barrier intercept — C = 0, so no slab traffic (A5)", False),
    (SEGB_HOT, SEGB_CACHE0, "capture at hot16", False),
    (SEGB_HOT, HOT, "THE VERDICT — the transplant against the hinted incumbent", False),
    (SEGB_K40, SEGB_HOT, "the capture slope, re-tested on the transplant", True),
    (SEGB_FLOOR, CTL_LB, "the walk floor — the transplant body against the uncached control",
     False),
    (SEGB_SLOTTED, SEGB_HOT,
     "the slotted-slab footprint / L2 row — one admitted set on two region maps (A9)", False),
)

# A4: the walk floor is reported in BOTH currencies. `eval` alone is the body floor, and
# `eval + finalize` is what a transplant would actually cost — the transplant lanes reduce
# 16x the slots, so the two are different claims and are never pooled.
CURRENCIES = (("body floor", "ev", "eval only"),
              ("transplant floor", "tot", "eval + finalize"))
# The floor lane of each rung, against the SAME uncached 128-thread control.
WALK_FLOORS = (("R7b", "SEGB", SEGB_FLOOR), ("R7", "SEG-GMEM", FLOOR))

# R4's frozen in-rotation anchors, by term order: (control@256, hot16@128) eval+finalize
# medians. Same constants as r4_table.py / r6_probe_table.py — R7 inherits them and does not
# edit them. The hot16 row is INFORMATIONAL here: R7's hot16 lane carries the R6 carveout
# hint, which the frozen anchor did not.
ANCHORS = {"census": (16.545, 15.129), "locality": (16.624, 14.836)}
SANITY_TOL = 0.02
# The Step 7 repeat trigger and the bridge flank, both the R6 form: block medians of an anchor
# lane's first and last full rotation cycle must agree within this, else the session is
# repeated soaked / the bridged figure carries a shift its anchor also saw.
FLANK_MS = 0.05


def threshold(rounds):
    """ceil(0.9 * rounds) as an integer, so the literal is exact at both session shapes:
    90/100 for the anchor and smem rotations, 90/99 for gmem."""
    return (9 * rounds + 9) // 10


def die(message):
    sys.exit(message)


def oracle_path():
    return os.environ.get(ORACLE_ENV, ORACLE_DEFAULT)


def oracle():
    """The committed dealer oracle, with its own contract pinned: a file that documents a
    different hash algorithm, segment count or reference stripe is not the oracle these rules
    are registered against."""
    path = oracle_path()
    try:
        with open(path) as fh:
            data = json.load(fh)
    except OSError as e:
        die(f"the committed dealer oracle is unreadable at {path}: {e} — the SEG line has "
            f"nothing to be validated against, and cross-log agreement alone is not accepted")
    except ValueError as e:
        die(f"the dealer oracle at {path} is not valid JSON: {e}")
    if data.get("program_hash_algo") != ORACLE_ALGO:
        die(f"{path}: program_hash_algo is {data.get('program_hash_algo')!r}, this emitter is "
            f"registered against {ORACLE_ALGO!r} (fnv1a64 over little-endian `<4H` record "
            f"bytes, 16 lowercase hex)")
    if data.get("owner_arm") != ORACLE_STRIPE:
        die(f"{path}: owner_arm is {data.get('owner_arm')!r}, the SEG line's owner census is "
            f"the {ORACLE_STRIPE} reference stripe")
    if data.get("seg_k") != ORACLE_SEG_K:
        die(f"{path}: seg_k is {data.get('seg_k')!r}, this rung is K = {ORACLE_SEG_K}")
    orders = {}
    for row in data.get("orders", []):
        offsets = row["list_offset"]
        cost = row["predicted_cost"]
        comp = row["owner_components"]
        stores = row["owner_stores"]
        if len(offsets) != ORACLE_SEG_K + 1 or len(cost) != ORACLE_SEG_K:
            die(f"{path}: the {row['term_order']} block carries {len(offsets)} offsets and "
                f"{len(cost)} costs, K = {ORACLE_SEG_K} needs {ORACLE_SEG_K + 1} and "
                f"{ORACLE_SEG_K}")
        # The oracle states the stripe as chain COMPONENTS and STORES per warp (E4 = 4
        # components / 2 stores, BF = 1 / 1), which the runner prints as the E4 and BF entry
        # counts. The map is invertible, so the comparison is exact in either currency.
        e4, bf = [], []
        for c, s in zip(comp, stores):
            if (c - s) % 2 or 2 * s - c < 0 or (c - s) // 2 < 0:
                die(f"{path}: owner_components {c} / owner_stores {s} are not a "
                    f"(4 E4 + BF, 2 E4 + BF) pair — the oracle's stripe is unreadable")
            e4.append((c - s) // 2)
            bf.append(2 * s - c)
        orders[row["term_order"]] = {
            "offsets": list(offsets), "cost": list(cost), "e4": e4, "bf": bf,
            "hash": row["program_hash"], "path": path,
        }
    if not orders:
        die(f"{path}: the oracle carries no term-order blocks")
    return orders


def seg_line_of(o):
    """The SEG line an oracle block implies, in the runner's exact grammar."""
    j = lambda xs: ",".join(str(x) for x in xs)
    return (f"SEG list_offset={j(o['offsets'])} cost={j(o['cost'])} "
            f"owners=e4:{j(o['e4'])};bf:{j(o['bf'])} hash={o['hash']} "
            f"stripe={ORACLE_STRIPE}")


def parse_ints(text):
    return [int(x) for x in text.split(",")]


def load(path, index, oracles, positions=POSITIONS):
    """One process, at its PINNED position. Every gate is fail-closed: a violation exits
    non-zero with the reason, never a partially summarized log."""
    name, want_tag, want_order, want_hint = positions[index]
    where = f"{path} (position {index + 1}, {name})"
    sched = done = seg = None
    echoes = {}
    arms = {}
    rounds = defaultdict(dict)
    for n, raw in enumerate(open(path), 1):
        raw = raw.rstrip("\n")
        line = raw.strip()
        m = ECHO.match(raw)
        if m:
            pct, symbol = int(m.group(1)), m.group(2)
            if symbol in echoes:
                die(f"{where}:{n}: a second applied-hint echo for `{symbol}` — one log is one "
                    f"process and each symbol's carveout is set once, before any launch")
            echoes[symbol] = pct
            continue
        if line.startswith(ECHO_ANY):
            die(f"{where}:{n}: `{line}` is not the harness's applied-hint echo line — the "
                f"literal is `  carveout hint       <pct>% (<symbol>)`, and this gate "
                f"corroborates the pinned hint per symbol against what the process applied")
        m = SEG.match(line)
        if m:
            if seg is not None:
                die(f"{where}:{n}: a second `SEG` line — one log is one process, and one "
                    f"process deals one program")
            seg = {
                "offsets": parse_ints(m.group(1)), "cost": parse_ints(m.group(2)),
                "e4": parse_ints(m.group(3)), "bf": parse_ints(m.group(4)),
                "hash": m.group(5), "stripe": m.group(6), "line": line, "n": n,
            }
            continue
        if line.startswith("SEG "):
            die(f"{where}:{n}: malformed `SEG` line — the grammar is `SEG "
                f"list_offset=o0,o1,o2,o3,o4 cost=c0,c1,c2,c3 owners=e4:a,b,c,d;bf:e,f,g,h "
                f"hash=<16 hex> stripe=hot16`, and the trailing stripe token is required: the "
                f"owner census is the reference stripe, not this run's own prologue")
        m = SCHED.match(line)
        if m:
            if sched is not None:
                die(f"{where}:{n}: a second schedule line — one log is one process; emit the "
                    f"eight processes as eight logs")
            sched = {"tag": m.group(1), "order": m.group(2), "lanes": int(m.group(3)),
                     "rounds": int(m.group(4)), "warmup": int(m.group(5)),
                     "hint": m.group(6)}
            continue
        if any(line.startswith(f"{tag} schedule") for tag in TAGS):
            die(f"{where}:{n}: malformed schedule line — the R7 grammar is `<TAG> schedule "
                f"order=<o> lanes=<n> rounds=<r> warmup=<w>`, and the tag is read from HERE, "
                f"never from the filename")
        m = DONE.match(line)
        if m:
            if done is not None:
                die(f"{where}:{n}: a second `done` trailer — the log mixes runs")
            done = {"tag": m.group(1), "order": m.group(2), "warmup": int(m.group(3)),
                    "rounds": int(m.group(4)), "lanes": int(m.group(5))}
            continue
        m = ARM.match(line)
        if m:
            if sched is None:
                die(f"{where}:{n}: `ARM {m.group(1)}` before the schedule line — the lane "
                    f"facts cannot be bound to a tag or a term order")
            lane = m.group(1)
            if lane in arms:
                die(f"{where}:{n}: duplicate `ARM {lane}`")
            ids = m.group(10)
            arms[lane] = {
                "regs": int(m.group(2)), "blocks_sm": int(m.group(3)),
                "threads": int(m.group(4)), "grid": int(m.group(5)), "kernel": m.group(6),
                "c": int(m.group(7)), "removals": int(m.group(8)),
                "admitted": int(m.group(9)),
                "ids": [] if ids == "-" else [int(i) for i in ids.split(",")],
            }
            continue
        if line.startswith("ARM "):
            die(f"{where}:{n}: malformed `ARM` line — the R7 rotations emit the frontier "
                f"grammar, which carries the ordered admitted-id list (`-` when the lane "
                f"admits nothing)")
        m = SAMPLE.match(line)
        if m:
            order, rnd, lane, ev, fin, kernel = m.groups()
            if sched is None:
                die(f"{where}:{n}: SAMPLE row before the schedule line")
            if order != sched["order"]:
                die(f"{where}:{n}: sample declares order={order} inside the "
                    f"order={sched['order']} section — mixed log")
            if lane in rounds[int(rnd)]:
                die(f"{where}:{n}: duplicate sample for round={rnd} lane={lane} — the log "
                    f"mixes runs; emit one process at a time")
            rounds[int(rnd)][lane] = (float(ev), float(fin), kernel)
            continue
        if line.startswith("SAMPLE "):
            die(f"{where}:{n}: malformed `SAMPLE` line")

    if sched is None:
        die(f"{where}: no R7 schedule line — this is not a {want_tag} log")
    if done is None:
        die(f"{where}: no `{sched['tag']} done` trailer — the run did not finish, or the log "
            f"is truncated")
    if (done["tag"], done["order"], done["rounds"], done["warmup"], done["lanes"]) != (
            sched["tag"], sched["order"], sched["rounds"], sched["warmup"], sched["lanes"]):
        die(f"{where}: the schedule line declares {sched['tag']} order={sched['order']} "
            f"rounds={sched['rounds']} warmup={sched['warmup']} lanes={sched['lanes']} but "
            f"the trailer declares {done['tag']} order={done['order']} "
            f"rounds={done['rounds']} warmup={done['warmup']} lanes={done['lanes']} — the "
            f"log mixes two runs")

    # THE POSITIONAL PIN. Each position is one preregistered process; a log outside it has no
    # rule to be decided under, and accepting a near-miss is exactly what positional
    # preregistration exists to prevent.
    if sched["tag"] != want_tag or sched["order"] != want_order:
        die(f"{where}: this position is preregistered as {want_tag} at "
            f"`--term-order {want_order}`, the log declares {sched['tag']} at "
            f"order={sched['order']} — the {COUNT_WORDS[len(positions)]} logs are positional, "
            f"so a mis-ordered set would be summarized under the wrong pairing")
    want_rounds, want_warmup = ROUNDS[want_tag]
    if (sched["rounds"], sched["warmup"]) != (want_rounds, want_warmup):
        die(f"{where}: {want_tag} is preregistered at {want_rounds} rounds / {want_warmup} "
            f"warmup, the log declares rounds={sched['rounds']} warmup={sched['warmup']} — "
            f"the sign-stability threshold is keyed to the round count")
    # The schedule line carries no `carveout-hint=` suffix on an R7 rotation (that suffix is
    # the R6 probe's). It is accepted if a future runner adds one, and then it must agree with
    # the position; the hint state itself is proven by the echo lines below either way.
    if sched["hint"] is not None:
        got = "default" if sched["hint"] == "default" else int(sched["hint"])
        if got != want_hint:
            die(f"{where}: the schedule line declares carveout-hint={sched['hint']} but this "
                f"position is preregistered at hint {want_hint} on `{LOCAL_INCUMBENT}`")

    inventory = ROTATION[want_tag]
    want_lanes = [lane for lane, _ in inventory]
    if set(arms) != set(want_lanes):
        missing = sorted(set(want_lanes) - set(arms))
        extra = sorted(set(arms) - set(want_lanes))
        die(f"{where}: lane set is not the {want_tag} rotation — missing {missing}, "
            f"unexpected {extra}")
    if len(arms) != sched["lanes"]:
        die(f"{where}: {len(arms)} ARM lines but the schedule declares "
            f"lanes={sched['lanes']} — the log is truncated or mixes builds")
    for lane, symbol in inventory:
        if arms[lane]["kernel"] != symbol:
            die(f"{where}: lane {lane} declares `{arms[lane]['kernel']}`, the {want_tag} "
                f"rotation runs it on `{symbol}` — the carrier contrast is a claim about "
                f"which body each lane ran")
    for lane, f in arms.items():
        if len(f["ids"]) != f["admitted"]:
            die(f"{where}: lane {lane} declares {f['admitted']} admitted sources but lists "
                f"{len(f['ids'])} ids")

    # THE APPLIED CARVEOUT, per symbol. The set of symbols a log must echo is DERIVED from the
    # lanes it declares — one echo per steered symbol the rotation uses, and nothing else. An
    # unsteered body (the uncached controls) must carry no echo at all.
    want_echoes = {}
    for lane, symbol in inventory:
        if symbol in SYMBOL_HINT:
            want_echoes[symbol] = SYMBOL_HINT[symbol]
        elif symbol == LOCAL_INCUMBENT:
            want_echoes[symbol] = want_hint
    if echoes != want_echoes:
        die(f"{where}: the applied-carveout echoes are "
            f"{dict(sorted(echoes.items()))}, this position's lanes use exactly "
            f"{dict(sorted(want_echoes.items()))} — the percent IS the configuration under "
            f"test, so a wrong, missing or spurious echo is a different arm")

    # THE DEALT PLAN. Required on a rotation that deals one, forbidden on the anchor rotation,
    # and validated field by field against the committed oracle for the log's OWN term order.
    deals = want_tag != "SEG-ANCHOR"
    if not deals:
        if seg is not None:
            die(f"{where}:{seg['n']}: a {want_tag} log carries a `SEG` line — the anchor "
                f"rotation uses local kernels only and deals no program, so this is a "
                f"mislabelled log")
    elif seg is None:
        die(f"{where}: no `SEG` line — a {want_tag} rotation deals a program and prints its "
            f"identity, and the dealt plan is what the timings are about")
    else:
        want = oracles.get(sched["order"])
        if want is None:
            die(f"{where}: the committed oracle carries no `{sched['order']}` block, so this "
                f"log's dealt plan has nothing to be validated against")
        if seg["stripe"] != ORACLE_STRIPE:
            die(f"{where}:{seg['n']}: the SEG line names stripe={seg['stripe']}, the owner "
                f"census is always the `{ORACLE_STRIPE}` reference stripe the oracle pins")
        for field, label in (("offsets", "list offsets"), ("cost", "predicted costs"),
                             ("e4", "E4 owner census"), ("bf", "BF owner census")):
            if seg[field] != want[field]:
                die(f"{where}:{seg['n']}: the SEG line's {label} are {seg[field]}, the "
                    f"committed oracle deals {want[field]} for `{sched['order']}` — the "
                    f"dealt plan is not the one Task 2 pinned")
        if seg["hash"] != want["hash"]:
            die(f"{where}:{seg['n']}: the SEG line's program hash is {seg['hash']}, the "
                f"committed oracle's `{sched['order']}` program hashes to {want['hash']} — "
                f"agreement between logs is not accepted in its place, since a consistently "
                f"forged plan would pass that")

    n_rounds, warmup = sched["rounds"], sched["warmup"]
    if len(rounds) != n_rounds:
        die(f"{where}: {len(rounds)} rounds carry samples, the schedule declares "
            f"rounds={n_rounds} — truncated log")
    # ROUND IDS. The runner numbers timed rounds `warmup .. warmup + rounds - 1`, so the ids
    # are a consecutive run with a known anchor; counting alone accepts gaps and a renumbered
    # log.
    want_ids = list(range(warmup, warmup + n_rounds))
    if sorted(rounds) != want_ids:
        got = sorted(rounds)
        die(f"{where}: round ids are {got[:4]}…{got[-1]}, expected the consecutive run "
            f"{want_ids[0]}…{want_ids[-1]} (warmup {warmup}, rounds {n_rounds}) — gaps, "
            f"duplicates or a renumbered log, none of which is a paired rotation")
    for r in want_ids:
        if set(rounds[r]) != set(want_lanes):
            die(f"{where}: round {r} carries {sorted(rounds[r])}, expected the "
                f"{len(want_lanes)} {want_tag} lanes {sorted(want_lanes)} — incomplete "
                f"rounds are not droppable, the contrasts are paired")
        for lane, (_, _, kernel) in rounds[r].items():
            if kernel != arms[lane]["kernel"]:
                die(f"{where}: round {r} lane {lane} ran `{kernel}` but its ARM line declares "
                    f"`{arms[lane]['kernel']}` — the log describes a kernel the run did not "
                    f"use")
    # ROTATION BALANCE. Samples arrive in execution order, so a lane's position inside a round
    # IS its rotation slot; a lane that keeps a slot carries that slot's clock state into its
    # median, which is exactly what the pairing exists to remove.
    n = len(want_lanes)
    if n_rounds % n != 0:
        die(f"{where}: {n_rounds} rounds over {n} lanes is not balanced — every lane must "
            f"start equally often")
    per = n_rounds // n
    slots = defaultdict(int)
    for r in want_ids:
        for slot, lane in enumerate(rounds[r]):
            slots[(lane, slot)] += 1
    for lane in want_lanes:
        for slot in range(n):
            if slots[(lane, slot)] != per:
                die(f"{where}: lane {lane} runs at rotation position {slot} in "
                    f"{slots[(lane, slot)]} rounds, expected {per} — the rotation is not "
                    f"balanced")
    # ALIASING GUARD. Two lanes that declare different plans cannot produce bit-identical
    # per-round samples — that is one lane's data under two labels, and it reads as a clean
    # +0.000 rather than as a bug.
    for i, a in enumerate(want_lanes):
        for b in want_lanes[i + 1:]:
            if all(rounds[r][a][:2] == rounds[r][b][:2] for r in want_ids):
                die(f"{where}: lanes {a} and {b} carry BIT-IDENTICAL samples in every round — "
                    f"the log aliases one lane's data onto another")

    ev = {a: [rounds[r][a][0] for r in want_ids] for a in want_lanes}
    fin = {a: [rounds[r][a][1] for r in want_ids] for a in want_lanes}
    tot = {a: [x + y for x, y in zip(ev[a], fin[a])] for a in want_lanes}
    return {
        "path": path, "name": name, "tag": want_tag, "order": want_order,
        "hint": want_hint, "arms": arms, "lanes": want_lanes, "keys": want_ids,
        "rounds": n_rounds, "warmup": warmup, "seg": seg,
        "ev": ev, "fin": fin, "tot": tot,
        "med": {a: median(tot[a]) for a in want_lanes},
        "med_ev": {a: median(ev[a]) for a in want_lanes},
        "med_fin": {a: median(fin[a]) for a in want_lanes},
    }


def session(paths, positions=POSITIONS, counts=None, grid_pin=None):
    """The session's processes plus the cross-log gates: one experiment, one dealt plan per
    term order, one build."""
    counts = counts or (len(positions),)
    if len(paths) not in counts:
        die(f"r7_table expects exactly {' or '.join(str(c) for c in counts)} logs in session "
            f"order ({' '.join(p[0] for p in positions)}); got {len(paths)} — every pairing "
            f"here is POSITIONAL, so a short or long set has no defined positions")
    oracles = oracle()
    procs = [load(p, i, oracles, positions) for i, p in enumerate(paths)]
    # THE TRACE PIN, before the relative gates: a session recorded at another `--log-trace` is
    # self-consistent, so it passes every one of them.
    for p in procs:
        for lane, facts in p["arms"].items():
            want = (grid_pin or {}).get(lane)
            if want is not None and facts["grid"] != want:
                die(f"{p['path']} ({p['name']}): lane {lane} declares grid={facts['grid']}, "
                    f"and this rung's arms are preregistered at `--log-trace {SEGB_TRACE}`, "
                    f"where that lane launches {want} blocks — the trace size is printed in "
                    f"no decision-bearing line, so a session recorded at another one would "
                    f"otherwise be summarized as if it were this one")
    # LANE-PLAN IDENTITY across logs. The hint is host-only and the deal is capture-blind, so a
    # lane that appears in two processes must declare the same plan in both; this is where a
    # set assembled from two builds, two censuses or two trace sizes is caught.
    seen = {}
    for p in procs:
        for lane, facts in p["arms"].items():
            first = seen.setdefault(lane, (p, facts))
            if first[1] != facts:
                die(f"{p['path']} ({p['name']}): lane {lane} declares a different plan than "
                    f"{first[0]['path']} ({first[0]['name']}) — every lane fact (kernel, "
                    f"occupancy, grid, C, removals, admitted ids) is a property of the "
                    f"program and the build, not of the process")
    # DEALT-PLAN IDENTITY across logs of one term order. Each was already checked against the
    # committed oracle, so this can only fail if two logs of one order disagree — i.e. two
    # different programs were timed.
    by_order = defaultdict(list)
    for p in procs:
        if p["seg"] is not None:
            by_order[p["order"]].append(p)
    for order, group in by_order.items():
        for p in group[1:]:
            if p["seg"]["line"] != group[0]["seg"]["line"]:
                die(f"{p['path']} ({p['name']}): its SEG line differs from "
                    f"{group[0]['path']} ({group[0]['name']}) at the same term order — two "
                    f"processes timed two different dealt programs")
    return procs, oracles


def paired(p, a, b, key="tot"):
    """The paired per-round contrast `a - b` inside ONE process, with its sign-stability
    count. `key` is the currency: `tot` = eval+finalize (the bar's), `ev` = eval alone.
    Reported, never turned into a verdict (R7 preregisters none)."""
    d = [x - y for x, y in zip(p[key][a], p[key][b])]
    neg = sum(1 for x in d if x < 0)
    pos = sum(1 for x in d if x > 0)
    return {"med": median(d), "neg": neg, "pos": pos, "n": len(d),
            "on": max(neg, pos), "thr": threshold(len(d)),
            "sign": "neg" if median(d) < 0 else ("pos" if median(d) > 0 else "flat")}


def stability(c):
    """The sign-stability cell: the on-sign count in the median's own direction against
    ceil(0.9 N)."""
    on = c["neg"] if c["sign"] == "neg" else c["pos"]
    return f"{on}/{c['n']} {c['sign']} ({'≥' if on >= c['thr'] else '<'} {c['thr']})"


def cycles(p, lane):
    """An anchor lane's block medians over the FIRST and LAST full rotation cycle — the R6
    form of the Step 7 repeat trigger. Single first/last samples are noise."""
    n = len(p["lanes"])
    keys = p["keys"]
    first = [p["tot"][lane][i] for i in range(n)]
    last = [p["tot"][lane][i] for i in range(len(keys) - n, len(keys))]
    return median(first), median(last)


def inventory_table(procs, noun="eight"):
    print(f"### Session inventory — {noun} positional processes\n")
    print("| # | position | tag | order | rounds | warmup | incumbent hint | log |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- |")
    for i, p in enumerate(procs):
        print(f"| {i + 1} | {p['name']} | {p['tag']} | `{p['order']}` | {p['rounds']} | "
              f"{p['warmup']} | {p['hint']}% | `{p['path']}` |")


def plan_table(procs, oracles):
    print("\n### Dealt plan identity — validated against the committed Task 2 oracle\n")
    # The printed path is what makes the override safe to have: the committed-oracle rule exists
    # so a forged plan cannot be validated against a matching forged oracle, and a redirect makes
    # that pair constructible — so a redirect has to be VISIBLE in the emitted record.
    if oracle_path() != ORACLE_DEFAULT:
        print(f"> **NON-DEFAULT ORACLE** — `{ORACLE_ENV}` redirected the dealer oracle away "
              f"from the committed file. A record quoting this output is only valid if the "
              f"path below is `gpu/gkr_uniskip_bench/tools/r7_fixtures/seg_oracle.json`.\n")
    print(f"Oracle: `{next(iter(oracles.values()))['path']}` ({ORACLE_ALGO} over "
          f"little-endian record bytes). The owner census is the `{ORACLE_STRIPE}` REFERENCE "
          f"stripe, which the dealer pins arm-independently — it is NOT what any one run's "
          f"prologue striped, which is what the `stripe=` token says out loud.\n")
    print("| order | carried by | list offsets | predicted cost | owners e4 | owners bf | "
          "program hash |")
    print("| --- | --- | --- | --- | --- | --- | --- |")
    for order in sorted(oracles):
        o = oracles[order]
        carried = [p["name"] for p in procs if p["seg"] is not None and p["order"] == order]
        j = lambda xs: ",".join(str(x) for x in xs)
        print(f"| `{order}` | {', '.join(carried) if carried else '—'} | {j(o['offsets'])} | "
              f"{j(o['cost'])} | {j(o['e4'])} | {j(o['bf'])} | `{o['hash']}` |")
    anchors = [p["name"] for p in procs if p["seg"] is None]
    print(f"\nSEG-ANCHOR processes carry no dealt plan and no SEG line, as required: "
          f"{', '.join(anchors)}.")


def facts_table(procs):
    print("\n### Lane facts — from the `ARM` lines, identical across every process that "
          "carries the lane\n")
    print("| rotation | lane | kernel | regs | blocks/SM | threads | grid | C | removals | "
          "admitted |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    for tag in TAGS:
        p = next((q for q in procs if q["tag"] == tag), None)
        if p is None:
            continue
        for lane in p["lanes"]:
            f = p["arms"][lane]
            print(f"| {tag} | `{lane}` | `{f['kernel']}` | {f['regs']} | {f['blocks_sm']} | "
                  f"{f['threads']} | {f['grid']} | {f['c']} | {f['removals']} | "
                  f"{f['admitted']} |")


def medians_table(procs):
    print("\n### Per-lane medians — `eval`, `finalize`, `eval + finalize`, ms\n")
    print("| position | lane | eval | finalize | eval+finalize |")
    print("| --- | --- | --- | --- | --- |")
    for p in procs:
        for lane in p["lanes"]:
            print(f"| {p['name']} | `{lane}` | {p['med_ev'][lane]:.3f} | "
                  f"{p['med_fin'][lane]:.3f} | **{p['med'][lane]:.3f}** |")


def delta_tables(procs):
    print(f"\n### Paired deltas vs the incumbent `{HOT}` — per round, on `eval + finalize`\n")
    print(f"The incumbent carries the R6 carveout hint in every one of these processes "
          f"(best-vs-best, RR ruling). Sign-stability is the count of rounds on the median's "
          f"own side against ceil(0.9 N); R7 preregisters NO closure threshold, so it is "
          f"REPORTED and no row here selects a winner.\n")
    print("| position | lane | C | removals | median Δ (ms) | sign-stability |")
    print("| --- | --- | --- | --- | --- | --- |")
    for p in procs:
        if p["tag"] == "SEG-ANCHOR":
            continue
        for lane in p["lanes"]:
            if lane == HOT or not lane.startswith("seg-"):
                continue
            c = paired(p, lane, HOT)
            f = p["arms"][lane]
            print(f"| {p['name']} | `{lane}` | {f['c']} | {f['removals']} | "
                  f"**{c['med']:+.3f}** | {stability(c)} |")

    print(f"\n### Paired deltas vs the carrier's own `seg-cache0` — the same carrier at zero "
          f"capture\n")
    print("| position | lane | base | median Δ (ms) | sign-stability |")
    print("| --- | --- | --- | --- | --- |")
    for p in procs:
        if p["tag"] == "SEG-ANCHOR":
            continue
        base = next(l for l in p["lanes"] if l.startswith("seg-cache0-"))
        for lane in p["lanes"]:
            if lane == base or not lane.startswith("seg-") or lane == FLOOR:
                continue
            c = paired(p, lane, base)
            print(f"| {p['name']} | `{lane}` | `{base}` | **{c['med']:+.3f}** | "
                  f"{stability(c)} |")


def decompose_table(procs):
    print("\n### Machinery decomposition — paired, inside one process\n")
    print("| position | contrast | symbols | isolates | median Δ (ms) | sign-stability |")
    print("| --- | --- | --- | --- | --- | --- |")
    for p in procs:
        for hi, lo, what in DECOMPOSE.get(p["tag"], ()):
            if hi not in p["arms"] or lo not in p["arms"]:
                continue
            c = paired(p, hi, lo)
            sym = f"`{p['arms'][hi]['kernel']}` − `{p['arms'][lo]['kernel']}`"
            print(f"| {p['name']} | `{hi}` − `{lo}` | {sym} | {what} | "
                  f"**{c['med']:+.3f}** | {stability(c)} |")


def slope_table(procs):
    print("\n### Capture slope — paired, matched symbol, per removal\n")
    print("The divisor is the removals DELTA read off the two `ARM` lines, so the slope "
          "carries no literal of its own.\n")
    print("| position | contrast | Δ removals | median Δ (ms) | µs per removal | "
          "sign-stability |")
    print("| --- | --- | --- | --- | --- | --- |")
    for p in procs:
        for hi, lo in SLOPES.get(p["tag"], ()):
            if hi not in p["arms"] or lo not in p["arms"]:
                continue
            dr = p["arms"][hi]["removals"] - p["arms"][lo]["removals"]
            c = paired(p, hi, lo)
            per = f"{1000.0 * c['med'] / dr:+.2f}" if dr else "n/a"
            print(f"| {p['name']} | `{hi}` − `{lo}` | {dr} | **{c['med']:+.3f}** | {per} | "
                  f"{stability(c)} |")


def carrier_table(procs):
    print("\n### Carrier A/B — S vs G at matched capture, BRIDGED over the shared anchors\n")
    print(f"The two rotations are separate processes, so nothing here is paired per round: "
          f"each figure rides a lane BOTH rotations carry (`{CTL}` and the hinted `{HOT}`), "
          f"the R4/R5 cross-session anchor method. δ = (S − A_S) − (G − A_G); a negative δ "
          f"favours carrier S. The flank is |A_S − A_G|: past {FLANK_MS:.2f} ms the bridge "
          f"carries a session shift its own anchor also saw, and that row is `unstable`.\n")
    for order in ("locality", "census"):
        s = next((p for p in procs if p["tag"] == "SEG-SMEM" and p["order"] == order), None)
        g = next((p for p in procs if p["tag"] == "SEG-GMEM" and p["order"] == order), None)
        if s is None or g is None:
            continue
        note = ("headline" if order == "locality"
                else "dealing-damage diagnostic — NEVER pooled with the locality row")
        print(f"\n**`{order}`** ({note}): `{s['name']}` vs `{g['name']}`\n")
        print("| capture | S lane | G lane | anchor | flank (ms) | stable | S med | G med | "
              "δ (ms) |")
        print("| --- | --- | --- | --- | --- | --- | --- | --- | --- |")
        for label, ls, lg in MATCHED:
            if ls not in s["arms"] or lg not in g["arms"]:
                continue
            for a in BRIDGES:
                flank = abs(s["med"][a] - g["med"][a])
                d = (s["med"][ls] - s["med"][a]) - (g["med"][lg] - g["med"][a])
                print(f"| {label} | `{ls}` | `{lg}` | `{a}` | {flank:.3f} | "
                      f"**{'stable' if flank <= FLANK_MS else 'unstable'}** | "
                      f"{s['med'][ls]:.3f} | {g['med'][lg]:.3f} | **{d:+.3f}** |")


def attribution_table(procs):
    print("\n### Attribution — what the incumbent's carveout hint alone does\n")
    print(f"The same two-lane SEG-ANCHOR rotation at three hints, so the contrast is the "
          f"paired per-round `({HOT} − {CTL})` INSIDE each process — drift-immune — and the "
          f"attribution is the difference of those contrasts across processes. `{CTL}` is a "
          f"different symbol and is never hinted.\n")
    print("| position | hint | median (hot16 − control@256) | sign-stability | Δ vs "
          "reanchor-locality |")
    print("| --- | --- | --- | --- | --- |")
    base = None
    for i in ATTR:
        p = procs[i]
        c = paired(p, HOT, CTL)
        if base is None:
            base = c["med"]
            rel = "—"
        else:
            rel = f"**{c['med'] - base:+.3f}**"
        print(f"| {p['name']} | {p['hint']}% | **{c['med']:+.3f}** | {stability(c)} | {rel} |")


def reanchor_table(procs):
    print("\n### Re-anchor vs R4's frozen in-rotation medians (±2 %, NON-FATAL)\n")
    print(f"Scopes the absolutes; it does not invalidate any paired contrast. `{HOT}` here "
          f"carries the R6 carveout hint the frozen anchor did not, so its row is "
          f"INFORMATIONAL (the hint was priced at roughly −0.09 ms on locality) — only "
          f"`{CTL}`, never hinted in any rung, is a like-for-like anchor.\n")
    print("| position | lane | this session | R4 frozen | delta | verdict |")
    print("| --- | --- | --- | --- | --- | --- |")
    out = False
    for i in (0, REANCHOR):
        p = procs[i]
        for lane, target in zip((CTL, HOT), ANCHORS[p["order"]]):
            got = p["med"][lane]
            rel = (got - target) / target
            ok = abs(rel) <= SANITY_TOL
            out = out or (not ok and lane == CTL)
            print(f"| {p['name']} | `{lane}` | {got:.3f} | {target:.3f} | "
                  f"{100.0 * rel:+.2f} % | **{'IN' if ok else 'OUT'}** |")
    if out:
        print(f"\n> **ANCHOR OUT OF BAND — absolutes are session-scoped**\n")
        print(f"`{CTL}` is more than ±2 % off its frozen median, so the raw millisecond "
              f"figures above read as this session's, not as cross-session absolutes. The "
              f"paired contrasts stand.")


def flank_table(procs):
    print("\n### Step 7 repeat trigger — anchor drift across the session\n")
    print(f"Per anchor lane, the block median of its observations in the FIRST full rotation "
          f"cycle against the LAST full cycle; they must agree within {FLANK_MS:.2f} ms or "
          f"that session is repeated soaked (the R6 form — single first/last samples are "
          f"noise). Rotation-vs-standalone deltas are NOT a trigger.\n")
    print("| position | lane | first cycle | last cycle | abs Δ (ms) | verdict |")
    print("| --- | --- | --- | --- | --- | --- |")
    fired = []
    for p in procs:
        for lane in (CTL, CTL_LB, HOT):
            if lane not in p["arms"]:
                continue
            first, last = cycles(p, lane)
            gap = abs(first - last)
            ok = gap <= FLANK_MS
            fired += [] if ok else [f"{p['name']}/{lane}"]
            print(f"| {p['name']} | `{lane}` | {first:.3f} | {last:.3f} | {gap:.3f} | "
                  f"**{'held' if ok else 'TRIPPED'}** |")
    if fired:
        print(f"\n⇒ **REPEAT TRIGGER FIRED** — {', '.join(fired)} drifted past "
              f"{FLANK_MS:.2f} ms across the session; those sessions are re-run soaked "
              f"before their rows are read as measurements (plan Step 7).")
    else:
        print(f"\n⇒ no repeat trigger: every anchor lane held within {FLANK_MS:.2f} ms "
              f"across its session (plan Step 7).")


def partials_per_block(kernel):
    """A6. The slot count a lane's finalize reduces, derived from the body it names."""
    return SEGB_PARTIALS_PER_BLOCK if kernel.startswith("eval_lsb_segb") else 1


def segb_facts_table(procs):
    print("\n### Lane facts — from the `ARM` lines, with the finalize slots DERIVED\n")
    print(f"`partials/block` and `partial slots` are not in the log: the ARM grammar is "
          f"R7's, unchanged, and the emitter derives them from the body each lane names and "
          f"its own grid ({SEGB_PARTIALS_PER_BLOCK} slots per transplant block, one per warp; "
          f"one per block everywhere else). That is the {SEGB_PARTIALS_PER_BLOCK}x grid AND "
          f"the 16x slot count the transplant's finalize pays for.\n")
    print("| rotation | lane | kernel | regs | blocks/SM | threads | grid | partials/block | "
          "partial slots | C | removals | admitted |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    for tag in TAGS:
        p = next((q for q in procs if q["tag"] == tag), None)
        if p is None:
            continue
        for lane in p["lanes"]:
            f = p["arms"][lane]
            per = partials_per_block(f["kernel"])
            print(f"| {tag} | `{lane}` | `{f['kernel']}` | {f['regs']} | {f['blocks_sm']} | "
                  f"{f['threads']} | {f['grid']} | {per} | {f['grid'] * per} | {f['c']} | "
                  f"{f['removals']} | {f['admitted']} |")


def segb_decision_table(procs):
    print("\n### The R7b decision rows — paired per round, inside one process\n")
    print(f"Every row is a paired per-round contrast on `eval + finalize`, so nothing here is "
          f"bridged. The `segb-census` rows are the dealing-damage diagnostic — NEVER pooled "
          f"with the locality rows. Sign-stability is the count of rounds on the median's own "
          f"side against ceil(0.9 N); R7b inherits R7's ruling and preregisters NO closure "
          f"threshold, so no row selects a winner.\n")
    print("| position | contrast | symbols | isolates | median Δ (ms) | per removal | "
          "sign-stability |")
    print("| --- | --- | --- | --- | --- | --- | --- |")
    for p in procs:
        if p["tag"] != "SEGB":
            continue
        for hi, lo, what, slope in SEGB_DECISIONS:
            if hi not in p["arms"] or lo not in p["arms"]:
                continue
            c = paired(p, hi, lo)
            sym = f"`{p['arms'][hi]['kernel']}` − `{p['arms'][lo]['kernel']}`"
            dr = p["arms"][hi]["removals"] - p["arms"][lo]["removals"]
            per = f"{1000.0 * c['med'] / dr:+.2f} µs ({dr} removals)" if slope and dr else "—"
            print(f"| {p['name']} | `{hi}` − `{lo}` | {sym} | {what} | **{c['med']:+.3f}** | "
                  f"{per} | {stability(c)} |")


def segb_walk_floor_table(procs):
    print("\n### The walk floor — reported BOTH ways (A4)\n")
    print(f"The floor lane runs the segmented body with an EMPTY plan, so floor − `{CTL_LB}` "
          f"is what the walk itself costs over the uncached control. It is reported in both "
          f"currencies because the transplant's finalize reduces "
          f"{SEGB_PARTIALS_PER_BLOCK} slots per block over {SEGB_PARTIALS_PER_BLOCK}x the "
          f"blocks — 16x the slots of a 16-row lane at the same trace: `eval` alone is the "
          f"body floor, `eval + finalize` is what a transplant would actually pay. Each row "
          f"is PAIRED inside its own session.\n")
    print("| rung | position | currency | contrast | median Δ (ms) | sign-stability |")
    print("| --- | --- | --- | --- | --- | --- |")
    rows = {}
    for rung, tag, floor in WALK_FLOORS:
        for p in procs:
            if p["tag"] != tag or floor not in p["arms"] or CTL_LB not in p["arms"]:
                continue
            for label, key, currency in CURRENCIES:
                c = paired(p, floor, CTL_LB, key)
                rows[(rung, p["order"], key)] = c["med"]
                print(f"| {rung} | {p['name']} | {label} ({currency}) | `{floor}` − "
                      f"`{CTL_LB}` | **{c['med']:+.3f}** | {stability(c)} |")
    print(f"\n**R7 vs R7b** — the difference of the two IN-SESSION differentials above, per "
          f"term order (A4). Raw cross-session medians are never subtracted here: the two "
          f"rungs' sessions are different processes, and only each session's own floor-minus-"
          f"control differential is comparable across them. A negative figure is walk overhead "
          f"the transplant REMOVED.\n")
    print("| order | currency | R7b Δ | R7 Δ | R7b − R7 |")
    print("| --- | --- | --- | --- | --- |")
    for order in ("locality", "census"):
        for label, key, currency in CURRENCIES:
            b, r = rows.get(("R7b", order, key)), rows.get(("R7", order, key))
            if b is None:
                continue
            rel = "— (no R7 log at this position)" if r is None else f"**{b - r:+.3f}**"
            print(f"| `{order}` | {label} ({currency}) | {b:+.3f} | "
                  f"{'—' if r is None else f'{r:+.3f}'} | {rel} |")


def segb_report(procs, oracles):
    head = procs[SEGB_HEADLINE]
    n_r7 = sum(1 for p in procs if p["tag"] == "SEG-GMEM")
    print("## v3 R7b — the direct transplant (segb)\n")
    print(f"{len(procs)} positional processes: the two SEG-ANCHOR re-anchors, the SEGB "
          f"rotation at both term orders, and R7's own gmem session where it is supplied "
          f"({'present' if n_r7 else 'ABSENT — the R7-vs-R7b row is not emitted'}). "
          f"{head['rounds']} paired rounds x {len(head['lanes'])} lanes in the headline "
          f"rotation, warmup {head['warmup']}. Every figure below is EMITTED, the metric is "
          f"`eval + finalize` per round unless a row names another currency, and each "
          f"process's tag, term order, dealt plan and per-symbol carveout are read from the "
          f"log itself — never from a filename.\n")
    print("R7b inherits R7's ruling and preregisters no closure threshold: the tables are "
          "datapoints about the transplant's shape, and nothing here declares a winner.\n")
    inventory_table(procs, COUNT_WORDS[len(procs)])
    plan_table(procs, oracles)
    segb_facts_table(procs)
    medians_table(procs)
    segb_decision_table(procs)
    segb_walk_floor_table(procs)
    reanchor_table(procs)
    flank_table(procs)


def is_segb_session(paths):
    """The mode is read from the LOGS, like everything else decision-bearing here: a set
    carrying a `SEGB` schedule line is R7b's session and is summarized under R7b's positional
    inventory. An unreadable file is left to `load`, which reports it in place."""
    for path in paths:
        try:
            with open(path) as fh:
                for line in fh:
                    if line.startswith("SEGB schedule "):
                        return True
        except OSError:
            continue
    return False


def main():
    argv = sys.argv[1:]
    if argv[:1] in (["-h"], ["--help"]):
        print(__doc__)
        return
    if argv[:1] == ["--seg-line"]:
        if len(argv) != 2:
            die("usage: r7_table.py --seg-line <census|locality>")
        oracles = oracle()
        if argv[1] not in oracles:
            die(f"the committed oracle carries no `{argv[1]}` block; it deals "
                f"{sorted(oracles)}")
        print(seg_line_of(oracles[argv[1]]))
        return
    if is_segb_session(argv):
        segb_report(*session(argv, SEGB_POSITIONS, SEGB_COUNTS, SEGB_TRACE_GRID))
        return
    procs, oracles = session(argv)
    head = procs[HEADLINE]
    print("## v3 R7 — the segmented pair (seg-K4)\n")
    print(f"Eight positional processes: two SEG-ANCHOR re-anchors, the SEG-SMEM and SEG-GMEM "
          f"rotations at both term orders, and the two carveout-attribution processes. "
          f"{head['rounds']} paired rounds x {len(head['lanes'])} lanes in the headline "
          f"rotation, warmup {head['warmup']}. Every figure below is EMITTED: this script is "
          f"the single authority for the rung's derived numbers, the metric is "
          f"`eval + finalize` per round, and each process's tag, term order, dealt plan and "
          f"per-symbol carveout are read from the log itself — never from a filename.\n")
    print("R7 preregisters no closure threshold (spec, RR ruling): the tables are datapoints "
          "about where the optimum lies, and the record must let a reader tell an "
          "implementation defect from a refuted idea. Nothing here declares a winner.\n")
    inventory_table(procs)
    plan_table(procs, oracles)
    facts_table(procs)
    medians_table(procs)
    delta_tables(procs)
    decompose_table(procs)
    slope_table(procs)
    carrier_table(procs)
    attribution_table(procs)
    reanchor_table(procs)
    flank_table(procs)


if __name__ == "__main__":
    main()
