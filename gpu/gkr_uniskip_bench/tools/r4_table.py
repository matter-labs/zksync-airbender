#!/usr/bin/env python3
"""Emit the v3 R4 factorial table from a `--cache-factorial` run log, the v3 R5
admission-frontier tables from `--frontier-factorial` / `--frontier-extension` logs, the
v3 R8 admission-interior tables from a `--frontier-interior` session pair, the v3 R9
gate-first-reorder tables from a `--reorder-factorial` session pair, and the v3 R9b
corrected-grouped-path tables from a `--r9b-class` and/or `--r9b-budget` session pair.

R5 NOTE. For a frontier log this script is THE SINGLE AUTHORITY for every derived
decision — the three named curves, the signed per-lane statuses, C*, the extension
trigger, the broad-knee verdict, first losers, right-censoring, the headline selector,
the sanity verdict, the R4 bridges and the ncu capture manifest. Nothing decision-bearing
is computed by hand or in the record; each decision line names the preregistered rule
(spec `.agents/specs/2026-08-10-gkr-uniskip-v3-r5-hotk-frontier-design.md` 2.3) it
implements. The mode is chosen by the LOG's own schedule keyword, never by a flag, so an
R4 log and a frontier log cannot be summarized under each other's rules.

Everything is PAIRED per round: the runner executes all eleven lanes inside one round, in a
cyclic rotation, so a round's lanes share whatever clock state that round had. Taking the
contrast round-by-round and then summarizing removes the ~1 %/session drift that would
otherwise swamp effects of this size.

The lane SET is pinned here (`EXPECTED_LANES`) as an integrity gate: a log carrying a
different rotation is a different experiment, and it is rejected rather than partially
summarized. Every per-lane FACT is data-driven from the log's `ARM` lines, which the runner
emits from Rust — registers, blocks/SM, block size, grid, kernel, C, removals, admitted-set
size. No occupancy number, kernel name or removal count is written here; R3's emitter held
all three, and the spec called that out as the thing to fix.

`eval` and `finalize` are summarized SEPARATELY. The 128 lanes run twice the grid, so
finalize reduces twice the partials; summing the two stages would fold a real block-size
effect into the arm comparison.

Every contrast NAMES its baseline. At 128 the cache-vs-control baseline is `control_lb@128`,
the bounded no-cache body, because the cached 128 lanes are bounded too — comparing them to
the unbounded `control@128` would put the launch bound's own cost inside the cache result.

Removals per lane ride the log's `ARM` line, which Rust fills from the arm's own planned
`CacheCounts` — this script holds no oracle constant, so a census change cannot silently
invalidate a slope (and the runner rejects the census knobs anyway).

R8 NOTE. The interior sweep gets a DEDICATED decision path (plan amendment A2), not a flag
threaded through the R5 one: it measures ONE contiguous admission axis and is decided by
adjacent steps and cumulative contrasts under one signed rule, never by R5's curves, C\\*,
extension trigger, broad knee or both-orders headline selector.

R9 NOTE. The reorder rung gets its own path for the same reason, one step further: it holds the
PLAN fixed and moves the BODY, so the plan-keyed identities the other paths gate on (the aliasing
key, the admission axis) cannot express it — three of its lanes share one plan by construction,
and the kernel is the only field that separates them. It also REPORTS rather than adjudicates
(RR's call for this rung): it prints the whole picture — every row under both term orders, the
anchor lanes against every reference this repo holds, the flank readings, the build facts — and
issues no verdict. It errors only where a number cannot be computed; every policy observation is a
FLAG at the top of the output. The R4/R5/R8 paths keep their own preregistered gates untouched.

R9b NOTE. R9b repairs the implementation R9 measured and re-measures it on TWO axes, which run as
two rotations under ONE tag (`R9B`) — so it gets its own path again, and that path identifies a
session by its LANE LABEL SET and its count, never by the tag. It is also the only rung whose log
set can carry TWO sessions (four logs), which is how the bridge lane's two medians are printed side
by side, so it is routed BEFORE the shared parser: that parser keys a section by (tag, order) and
would read the pair as one mixed run. Reporting-only, on the same terms as R9.

THE ANCHOR RE-BASE lives on that path too (RR, 2026-08-13). The campaign's anchor reference is now the
R9b session — three anchors, both rotations, with the DEVICE IDENTITY every earlier reference lacked —
and it is the only thing the `ANCHOR` flag keys to. The four historical references are kept as a
separate PRE-PROVENANCE block: printed, labelled `machine identity: unrecorded`, and never a flag
basis, because they disagree with each other by more than the reporting threshold. The R4/R5/R8/R9
paths are NOT re-pointed — their archived logs are what they are, and their byte-identity is
load-bearing; future rungs inherit the new model by building on the R9B path.

Usage:
    python3 gpu/gkr_uniskip_bench/tools/r4_table.py /tmp/cache.log [--order locality]
    python3 gpu/gkr_uniskip_bench/tools/r4_table.py primary.log [extension.log ...]
    python3 gpu/gkr_uniskip_bench/tools/r4_table.py interior-locality.log interior-census.log
    python3 gpu/gkr_uniskip_bench/tools/r4_table.py reorder-locality.log reorder-census.log
    python3 gpu/gkr_uniskip_bench/tools/r4_table.py r9b-class-{locality,census}.log \\
                                                    r9b-budget-{locality,census}.log
"""

import argparse
import os
import re
import sys
from collections import defaultdict
from statistics import median

SAMPLE = re.compile(r"^SAMPLE (\S+) (\d+) (\S+) ([\d.]+) ([\d.]+) (\S+)$")
ARM = re.compile(r"^ARM (\S+) (\d+) (\d+) (\d+) (\d+) (\S+) (\d+) (\d+) (\d+)$")
# The frontier ARM line is the R4 one PLUS the ordered admitted-id list: counts alone
# cannot detect a reversal among equal-ref, equal-class sources, so the LIST is what the
# oracle gate reads. `-` is the empty prefix (control, cache0).
ARM_IDS = re.compile(r"^ARM (\S+) (\d+) (\d+) (\d+) (\d+) (\S+) (\d+) (\d+) (\d+) (\S+)$")
R4 = "CACHE-FACTORIAL"
SCHED = re.compile(r"^(\S+) schedule order=(\S+) lanes=(\d+) rounds=(\d+) warmup=(\d+)$")
DONE = re.compile(r"^(\S+) done order=(\S+) warmup=(\d+) rounds=(\d+) lanes=(\d+)$")
# The harness's APPLIED-carveout block, matched on the RAW line — its indentation is part of the
# runner's literal. The per-symbol echoes are printed after `cudaFuncSetAttribute` actually ran,
# and the set line states the whole hinted SET, so a missing symbol is distinguishable from an
# unhinted one. Collected for every log; the R9 path is the one that gates them.
ECHO = re.compile(r"^  carveout hint       (\d+)% \(([a-z0-9_]+)\)$")
ECHO_SET = re.compile(r"^  carveout symbols    (\d+) local \(([a-z0-9_]+(?:, [a-z0-9_]+)*)\)$")
ECHO_ANY = "carveout "

# The eleven lanes the primary rotation must carry. A log with a different set is a
# different experiment and is rejected rather than partially summarized.
EXPECTED_LANES = {
    "control@256", "cache0@256", "hot4@256", "hot16@256", "allrepeat@256",
    "control@128", "control_lb@128", "cache0@128", "hot4@128", "hot16@128", "allrepeat@128",
}

# --- v3 R5 frontier ---------------------------------------------------------------
#
# One row per rotation: the pinned lane set, the PREREGISTERED round count, and the
# preregistered signed threshold that goes with it (spec 2.3 — literals 90/100 and
# 94/104, never a ratio recomputed from the log).
FRONTIER = {
    "FRONTIER-FACTORIAL": {
        "lanes": {"k24@128", "k32@128", "k40@128", "k45@128", "k46@128", "k48@128",
                  "hot16@128", "cache0@128", "control_lb@128", "control@256"},
        "rounds": 100,
        "threshold": 90,
        "what": "primary",
    },
    "FRONTIER-EXTENSION": {
        "lanes": {"k48@128", "k49@128", "k50@128", "k51@128",
                  "hot16@128", "cache0@128", "control_lb@128", "control@256"},
        "rounds": 104,
        "threshold": 94,
        "what": "extension",
    },
}

# The controller-derived admission ordering, all 55 entries, from
# `.agents/sdd/2026-08-10-v3-r5/oracle-derivation.txt` (identical under both term orders).
# Every lane's admitted-id list must be its first-K prefix, IN THIS ORDER. This is the one
# oracle literal the emitter carries: an identity, not a count or a timing.
ORACLE_ORDER = (
    [0, 1, 2, 3, 4, 5] + [48, 49, 50, 51] + list(range(6, 41))
    + [52, 53, 54, 55, 56, 57, 58] + [41, 42, 43]
)

# The K a named lane claims. Cross-checked against the length of its admitted-id list, so a
# mislabelled lane is caught as well as a reordered one.
LANE_K = {"hot16@128": 16, "cache0@128": 0, "control_lb@128": 0, "control@256": 0}
LANE_K.update({f"k{k}@128": k for k in (24, 32, 40, 45, 46, 48, 49, 50, 51)})

# R4's frozen in-rotation anchors, by order: (control@256, hot16@128) eval+finalize medians
# (spec 2.3 sanity anchoring), and R2c, the v3 R2 shipping baseline the bridges ride on.
ANCHORS = {"census": (16.545, 15.129), "locality": (16.624, 14.836)}
R2C = {"census": 16.453, "locality": 16.283}
BAR = 14.61
SANITY_TOL = 0.02
KNEE_MS = 0.10

# --- v3 R8 interior ---------------------------------------------------------------
#
# The interior rung sweeps the seven admission points R5 never sampled, between the R5
# optimum (hot16 = K16, C = 28) and R5's first loser (k24, C = 36), on the same frozen cached
# body. Its lane set, round shape and signed threshold are PREREGISTERED literals: the
# threshold is ceil(0.9 x 96) = 87 (plan amendment A1), so a log at another round count has
# no rule to be judged against.
R8 = "FRONTIER-INTERIOR"

# The K axis in admission order: the incumbent, the seven interior points, and R5's boundary
# lane, which rides along so hot16 -> ... -> k24 is paired IN SESSION rather than across one.
INTERIOR_AXIS = ["hot16@128"] + [f"k{k}@128" for k in range(17, 25)]
# The lanes that admit nothing. `hot16@128` is an anchor as well as the axis bottom, so the
# anchor list below is not a partition of the rotation.
INTERIOR_BASES = ["cache0@128", "control_lb@128", "control@256"]
INTERIOR_ANCHORS = ("control@256", "control_lb@128", "cache0@128", "hot16@128")
INTERIOR = {
    "lanes": set(INTERIOR_AXIS) | set(INTERIOR_BASES),
    "rounds": 96,
    "warmup": 12,
    "threshold": 87,
}

# THE TRACE PIN (amendment A5). The trace size appears in no log line, but the grid does: at
# `--log-trace 24` it is the trace's row count over each lane's row tile, a fact of the build
# and the trace and of nothing else. A whole session recorded at another trace is internally
# consistent, so this pin is the only thing that can see it.
INTERIOR_TRACE = 24
INTERIOR_GRID = {"control@256": 32768}
INTERIOR_GRID.update({lane: 65536 for lane in INTERIOR_AXIS + ["cache0@128",
                                                              "control_lb@128"]})

# The interior lanes' K, alongside R5's above: a lane whose label and plan disagree is caught
# in both paths by the same identity.
LANE_K.update({f"k{k}@128": k for k in range(17, 24)})

# The R5 PRIMARY session's own `eval + finalize` medians per order, from that rung's emitter
# output (`.agents/sdd/2026-08-10-v3-r5/task3-frontier.md`), as (control@256, hot16@128).
# REPORT-ONLY context (amendment A6) — the HARD band stays the R4-frozen `ANCHORS` above.
R5_SESSION = {"census": (16.666, 15.120), "locality": (16.567, 14.717)}

# The flank rule (amendment A6), computed here rather than by hand: block medians of an anchor
# lane's FIRST and LAST full cycle against max(0.05 ms, 0.5 % of that lane's session median).
FLANK_MS = 0.05
FLANK_REL = 0.005

VERDICT = {"win": "WIN", "lose": "LOSS", "wash": "WASH"}

# --- v3 R9 gate-first reorder -----------------------------------------------------
#
# The reorder rung contrasts BODIES at one plan, not admission points: three cached lanes carry
# hot16's identical plan on three bodies, so every R5/R8 identity that keys on the plan alone
# (the aliasing guard, the admitted-prefix census, the one-BF-per-step axis) would either reject
# the rotation or fail to see a swapped body. Hence its own lane pins, its own observations and its
# own rows, and the R5/R8 paths are left byte-identical.
#
# REPORTING, NOT ADJUDICATION (RR, this rung): the emitter prints the WHOLE PICTURE and decides
# nothing. It errors only where it cannot compute a meaningful number — a log it cannot parse, a
# missing order, missing rounds, an unknown lane, rounds that do not form complete cycles. Every
# POLICY observation — trace, round shape, carveout tier, anchor offset, flank movement, body
# identity, plan identity, admission order, aliasing, build facts — is a FLAG printed at the top of
# the output, never a rejection and never a control-flow branch. WIN / LOSS / WASH are LABELS.
R9 = "REORDER"
R9_CTL, R9_CTL_LB = "control@256", "control_lb@128"
R9_INCUMBENT, R9_BOUNDED = "hot16@128", "reorder-hot16@128"
R9_FLOOR, R9_FREE = "reorder-cache0@128", "reorder-hot16-free@128"
# The rotation in execution order (`REORDER` in `src/coset_cache.rs`).
REORDER_LANES = [R9_CTL, R9_CTL_LB, R9_INCUMBENT, R9_BOUNDED, R9_FLOOR, R9_FREE]
REORDER = {"lanes": set(REORDER_LANES), "rounds": 96, "warmup": 6, "threshold": 87}

# THE TRACE PIN, R8's verbatim: the trace size appears in no log line, but the grid does — at
# `--log-trace 24` it is the trace's row count over each lane's row tile.
REORDER_TRACE = 24
REORDER_GRID = {lane: (32768 if lane == R9_CTL else 65536) for lane in REORDER_LANES}
# THE BODY PIN. The three cached lanes declare ONE plan — same C, same removals, same admitted
# prefix — so the kernel is the only thing that says which body a lane ran, and the rung is a
# body contrast. Nothing else in the log can see a lane launched on the wrong body.
REORDER_BODY = {
    R9_CTL: "eval_lsb_pair",
    R9_CTL_LB: "eval_lsb_pair_128_lb",
    R9_INCUMBENT: "eval_lsb_pair_cached_128_lb",
    R9_BOUNDED: "eval_lsb_pair_cached_reorder_128_lb",
    R9_FLOOR: "eval_lsb_pair_cached_reorder_128_lb",
    R9_FREE: "eval_lsb_pair_cached_reorder_128",
}
# The K a lane claims, as elsewhere: a mislabelled lane is caught as well as a reordered prefix.
REORDER_K = {R9_CTL: 0, R9_CTL_LB: 0, R9_FLOOR: 0,
             R9_INCUMBENT: 16, R9_BOUNDED: 16, R9_FREE: 16}
# The three lanes that declare ONE plan on three bodies — the rung's premise, reported per session.
REORDER_ONE_PLAN = (R9_INCUMBENT, R9_BOUNDED, R9_FREE)
# The two anchor lanes the reference comparison is read on.
REORDER_ANCHOR_LANES = (R9_CTL, R9_INCUMBENT)

# EVERY anchor reference this repo holds, each with the LANE COUNT of the rotation that produced it.
# Absolute medians are rotation-composition dependent — a thinner rotation interleaves fewer heavy
# lanes, so a lane sees less L2/DRAM/clock interference between its rounds — and this rung runs SIX
# lanes against references from ten to twelve. The emitter prints all of them side by side, labelled,
# and judges none: whether an offset is composition or machine is RR's call on the whole table. The
# lane count IS the instrument here, so each one is derived from its own rotation's `lanes=` field
# rather than from any prior note:
#   R4 frozen  = 11, `CACHE-FACTORIAL schedule … lanes=11` (`.agents/sdd/2026-08-09-v3-r4/`
#                session logs) and `EXPECTED_LANES` above, which this file enforces at 11.
#   R5 session = 10, `FRONTIER-FACTORIAL schedule … lanes=10` in
#                `.agents/sdd/2026-08-10-v3-r5/task3-primary-{locality,census}.log`, and
#                `FRONTIER["FRONTIER-FACTORIAL"]["lanes"]` above, which holds 10 lanes. (The
#                medians themselves are that rung's emitter output, cited at `R5_SESSION`.)
#   R8 session = 12, `FRONTIER-INTERIOR schedule … lanes=12` in
#                `.agents/sdd/2026-08-12-v3-r8/interior-{locality,census}.log`, and `INTERIOR`
#                above, which holds 12 lanes.
# `R8_SESSION`'s medians are this file's own `interior_emit` output over those two archived logs
# (`control@256` and `hot16@128`, median `eval+fin`). `.agents/**` is gitignored, so those logs are
# archived-but-untracked: `r9_fixtures/check.sh` pins both values verbatim, and that pin is what
# protects them in a clean checkout where the logs cannot be re-read.
R8_SESSION = {"locality": (16.738, 14.812), "census": (16.866, 15.334)}
REORDER_REFERENCES = (
    ("R4 frozen", 11, ANCHORS),
    ("R5 session", 10, R5_SESSION),
    ("R8 session", 12, R8_SESSION),
)
# A delta this large against a reference is FLAGGED — a reporting duty, so an offset cannot pass
# unremarked, and never a gate.
R9_OFFSET_TELL = 0.015
# The flank sentinels: the three INCUMBENT-body lanes. A body under test is not its own drift
# sentinel, so the reorder lanes are excluded by construction.
REORDER_FLANK_LANES = (R9_CTL, R9_CTL_LB, R9_INCUMBENT)

# The hinted LOCAL symbols, in the order the harness echoes them (`LaneKernel::HINTED`). The percent
# is READ off the log's own echoes and printed — the emitter carries no expected tier, so a re-pin
# needs no emitter change. What it reports is the UNIFORMITY the rung's premise wants (amendment
# A3): all three bodies contrasted at ONE L1 configuration.
REORDER_HINTED = ["eval_lsb_pair_cached_128_lb", "eval_lsb_pair_cached_reorder_128_lb",
                  "eval_lsb_pair_cached_reorder_128"]

# The decision rows, in order, each naming its baseline and what it isolates. Row 1 is the rung's
# headline contrast; the emitter prints it and does not grade it.
REORDER_ROWS = [
    (R9_BOUNDED, R9_INCUMBENT,
     "THE headline row — the gate-first body at the incumbent's plan, bound and L1 configuration"),
    (R9_FREE, R9_INCUMBENT, "the envelope verdict — the unbounded gate-first body vs the "
                            "incumbent"),
    (R9_FREE, R9_BOUNDED, "the pure envelope delta — occupancy + twiddle remat BUNDLED: the "
                          "unbounded body collapses the remat AND gains a block, and this row "
                          "cannot separate them"),
    (R9_FLOOR, R9_CTL_LB, "the reordered machinery floor — the frame, the walk, no removals"),
    (R9_BOUNDED, R9_FLOOR, "capture under the reorder (amendment A7) — removals alone on the "
                           "gate-first body"),
]
# The ncu capture set: a FIXED three lanes of interest, always printed under both orders, so no
# timing outcome and no selection rule decides it.
REORDER_CAPTURE = [(R9_INCUMBENT, "incumbent"), (R9_BOUNDED, "bounded-reorder"),
                   (R9_FREE, "unbounded-reorder")]

# --- v3 R9b the corrected grouped path, over a register-budget grid ---------------
#
# R9b repairs the implementation R9 measured (the grouped-term path duplicated its coefficient
# DECODE) and re-measures it. It runs TWO rotations under ONE tag, because it is one rung on two
# axes: a CLASS axis (four corrected body shapes at a fixed register budget) and a BUDGET axis
# (body C and the INCUMBENT, each at three budgets). Both print `R9B schedule … lanes=8`, so
# **THE TAG CANNOT TELL THEM APART** — this path identifies a session by its LANE LABEL SET and
# its count, and by nothing else. Two sessions may be emitted in one invocation (four logs); that
# is how the bridge lane's two medians are printed side by side.
#
# THE BUDGET AXIS IS NOT MONOTONE IN REGISTERS. `(128, 6)` is the MAXIMUM-register cell, not "no
# bound": the incumbent runs 72 → 80 → 75 and C runs 70 → 75 → 64 across `(128,7)` → `(128,6)` →
# unbounded (Task 1 §3). Nothing below reads the budget's declaration order as a register ordering;
# every register line is read off the log's own ARM lines and printed as read.
#
# REPORTING, NOT ADJUDICATION (RR's amendment A10, campaign-wide): the path prints the whole
# picture and decides nothing. It errors only where no meaningful number can be computed — a log it
# cannot parse, a missing term order, missing / renumbered / incomplete rounds, an unknown lane. Every
# POLICY observation is a FLAG in a block printed FIRST, above every table. WIN / LOSS / WASH are
# LABELS that drive no control flow.
R9B = "R9B"
R9B_CTL, R9B_CTL_LB, R9B_INC = "control@256", "control_lb@128", "hot16@128"
R9B_DROPIN = "reorder-hot16@128"
R9B_C, R9B_B, R9B_CD, R9B_BD = "c-hot16@128", "b-hot16@128", "cd-hot16@128", "bd-hot16@128"
R9B_INC_LB6, R9B_INC_FREE = "hot16-lb6@128", "hot16-free@128"
R9B_C_LB6, R9B_C_FREE = "c-hot16-lb6@128", "c-hot16-free@128"

# The three budget spellings, in the order Task 1 built them. NOT a register ordering (see above).
R9B_LB, R9B_LB6, R9B_UNB = "(128,7)", "(128,6)", "unbounded"

# THE CELL PIN: lane -> (body, budget, kernel). With several bodies AND several budgets on ONE plan,
# the kernel symbol is the only field in the log that says which cell ran — the counts are identical
# by construction. The body and the budget are the kernel's decomposition, printed as columns, and a
# kernel that names another cell is reported as a body swap or a budget swap accordingly.
R9B_CELL = {
    R9B_CTL: ("incumbent", "n/a", "eval_lsb_pair"),
    R9B_CTL_LB: ("incumbent", R9B_LB, "eval_lsb_pair_128_lb"),
    R9B_INC: ("incumbent", R9B_LB, "eval_lsb_pair_cached_128_lb"),
    R9B_INC_LB6: ("incumbent", R9B_LB6, "eval_lsb_pair_cached_128_lb6"),
    R9B_INC_FREE: ("incumbent", R9B_UNB, "eval_lsb_pair_cached_128"),
    R9B_DROPIN: ("R9-drop-in", R9B_LB, "eval_lsb_pair_cached_reorder_128_lb"),
    R9B_C: ("C", R9B_LB, "eval_lsb_pair_cached_reorder_c_128_lb"),
    R9B_C_LB6: ("C", R9B_LB6, "eval_lsb_pair_cached_reorder_c_128_lb6"),
    R9B_C_FREE: ("C", R9B_UNB, "eval_lsb_pair_cached_reorder_c_128"),
    R9B_B: ("B", R9B_LB, "eval_lsb_pair_cached_reorder_b_128_lb"),
    R9B_CD: ("C+D", R9B_LB, "eval_lsb_pair_cached_reorder_cd_128_lb"),
    R9B_BD: ("B+D", R9B_LB, "eval_lsb_pair_cached_reorder_bd_128_lb"),
}
# The reverse map, so an observed kernel can be named as a CELL rather than as a string: that is
# what separates "this lane ran another body" from "this lane ran the same body at another budget".
R9B_BY_KERNEL = {k: (lane, b, g) for lane, (b, g, k) in R9B_CELL.items()}

R9B_CLASS_LANES = [R9B_CTL, R9B_CTL_LB, R9B_INC, R9B_DROPIN, R9B_C, R9B_B, R9B_CD, R9B_BD]
R9B_BUDGET_LANES = [R9B_CTL, R9B_CTL_LB, R9B_INC, R9B_INC_LB6, R9B_INC_FREE,
                    R9B_C, R9B_C_LB6, R9B_C_FREE]

R9B_ROUNDS, R9B_WARMUP, R9B_THRESHOLD = 96, 8, 87
# THE TRACE PIN, R8's and R9's verbatim: the trace size appears in no log line, but the grid does —
# at `--log-trace 24` it is the trace's row count over each lane's row tile.
R9B_TRACE = 24
R9B_GRID = {lane: (32768 if lane == R9B_CTL else 65536) for lane in R9B_CELL}
# The K a lane claims, cross-checked against its admitted-id list: every cached cell of both
# rotations sits at hot16's admitted set, and the two controls admit nothing.
R9B_K = {lane: (0 if lane in (R9B_CTL, R9B_CTL_LB) else 16) for lane in R9B_CELL}

# The CLASS rows. Four corrected bodies against the incumbent, the same four against R9's drop-in
# (the RECOVERY set — the rung's headline), and the drop-in against the incumbent, which
# re-measures R9's +5.43 % inside this session rather than across two.
R9B_CLASS_ROWS = [
    (R9B_C, R9B_INC, "C against the incumbent, at its plan, bound and L1 configuration"),
    (R9B_B, R9B_INC, "B against the incumbent"),
    (R9B_CD, R9B_INC, "C+D against the incumbent"),
    (R9B_BD, R9B_INC, "B+D against the incumbent"),
    (R9B_C, R9B_DROPIN, "THE RECOVERY ROW, C — what the decode repair gives back against the "
                        "implementation R9 measured"),
    (R9B_B, R9B_DROPIN, "THE RECOVERY ROW, B"),
    (R9B_CD, R9B_DROPIN, "THE RECOVERY ROW, C+D"),
    (R9B_BD, R9B_DROPIN, "THE RECOVERY ROW, B+D"),
    (R9B_DROPIN, R9B_INC, "R9's drop-in re-measured INSIDE this session — the +5.43 % reference "
                          "point, on this rotation and this machine"),
]
# The BUDGET rows. The two separator rows carry the labels the rung pins them with: Task 1 found the
# bank-3 twiddle rematerialization collapsing at `(128, 6)` for every reordered body and never for
# the incumbent, which is what lets the pair be separated at all — the thing R9's record says it
# could not do.
R9B_BUDGET_ROWS = [
    (R9B_INC_LB6, R9B_INC, "the budget axis on an UNMODIFIED body (RR's question) — the incumbent "
                           "at (128, 6), the grid's maximum-register cell"),
    (R9B_INC_FREE, R9B_INC, "the budget axis on an UNMODIFIED body (RR's question) — the incumbent "
                            "unbounded, the arm R9's record left as static arithmetic (A8)"),
    (R9B_C, R9B_INC, "C at the fixed bound against the incumbent — also the BRIDGE lane, the one "
                     "cell both sessions carry"),
    (R9B_C_LB6, R9B_C, "the remat collapse at constant block tier"),
    (R9B_C_FREE, R9B_C_LB6, "the extra block at constant collapse"),
    (R9B_C_FREE, R9B_INC, "C unbounded against the incumbent — the whole budget move on the "
                          "corrected body, bundled"),
]

# The hinted LOCAL symbols per rotation, IN THE ORDER THE HARNESS ECHOES THEM (`LaneKernel::HINTED`).
# That order is the HINTED table's, NOT the lane order: the CLASS rotation echoes `cd` BEFORE `b`
# while its lanes run `c, b, cd, bd` (Task 2 concern 3). The percent is READ off the log's echoes and
# printed; this path carries no expected tier, so a re-pin needs no emitter change.
R9B_CLASS_HINTED = ["eval_lsb_pair_cached_128_lb", "eval_lsb_pair_cached_reorder_128_lb",
                    "eval_lsb_pair_cached_reorder_c_128_lb",
                    "eval_lsb_pair_cached_reorder_cd_128_lb",
                    "eval_lsb_pair_cached_reorder_b_128_lb",
                    "eval_lsb_pair_cached_reorder_bd_128_lb"]
R9B_BUDGET_HINTED = ["eval_lsb_pair_cached_128_lb", "eval_lsb_pair_cached_128_lb6",
                     "eval_lsb_pair_cached_128", "eval_lsb_pair_cached_reorder_c_128_lb",
                     "eval_lsb_pair_cached_reorder_c_128_lb6",
                     "eval_lsb_pair_cached_reorder_c_128"]

# The two session shapes. `lanes` is what identifies one — the label SET and its count — and
# everything else is that session's own row set, hinted set and prose.
R9B_SHAPES = {
    "CLASS": {
        "lanes": R9B_CLASS_LANES,
        "rows": R9B_CLASS_ROWS,
        "hinted": R9B_CLASS_HINTED,
        "flag": "--r9b-class",
        "what": "The class axis — four corrected body shapes at ONE register budget, beside the "
                "incumbent and R9's drop-in",
    },
    "BUDGET": {
        "lanes": R9B_BUDGET_LANES,
        "rows": R9B_BUDGET_ROWS,
        "hinted": R9B_BUDGET_HINTED,
        "flag": "--r9b-budget",
        "what": "The budget axis — body C and the INCUMBENT, each at all three register budgets, "
                "fully paired in one rotation",
    },
}
# The cached lanes of each shape declare ONE plan: same C, same removals, the same ordered admitted
# prefix, the same block size. That premise is what makes every row a CELL contrast; it is reported,
# never enforced.
R9B_ONE_PLAN = {name: [l for l in s["lanes"] if l not in (R9B_CTL, R9B_CTL_LB)]
                for name, s in R9B_SHAPES.items()}

# THE BRIDGE. `c-hot16@128` runs in BOTH rotations, so its two medians are the session-
# comparability reading — and the only one available, because a paired contrast is valid only
# inside a session.
R9B_BRIDGE = R9B_C

# --- THE RE-BASE (RR, 2026-08-13: "rebase") ---------------------------------------
#
# WHAT THIS IS. The campaign's anchor reference, re-based on the v3 R9b session, and the FIRST
# reference in this campaign that records the machine it was measured on. Every earlier reference
# recorded device STATE (clocks, power, temperature) and never device IDENTITY, so none of them can be
# shown to have come from this GPU — which is why they could disagree by 2.8 % on one lane and leave a
# 0.22 %-wide window in which a session could clear all of them at once (R9b Task 3 concern 2; it
# fired in Task 4 exactly as predicted, on census, in both session sets).
#
# WHOSE BASELINE IT IS. **This is the baseline R10 and later are read against, not R9b's own.** A
# session cannot be its own reference without circularity, so R9b's rows also keep the historical set
# beside it as CONTEXT. Future rungs inherit the model by building on this path.
#
# BOTH ROTATIONS, KEYED BY ROTATION, WITH THE SPREAD KEPT. CLASS and BUDGET both carry 8 lanes and
# still differ — locality `control@256` 16.725 v 16.778, `hot16@128` 14.793 v 14.823 (≈0.3 %). That is
# composition INSIDE a fixed lane count, a fact a future rung needs, so neither rotation is averaged
# away nor dropped; the emitter compares a session to its OWN rotation's row and prints the other
# rotation's beside it as the spread.
#
# PROVENANCE. Medians are the PRIMARY session set's, from this file's own R9B output over
# `.agents/sdd/2026-08-13-v3-r9b/r9b-{class,budget}-{locality,census}.log` (`median eval+fin`); the
# repeat set is in that rung's Task 4 report §6.1 if a mid-point is ever wanted. `.agents/**` is
# gitignored, so `r9b_fixtures/check.sh` pins every value verbatim — that pin is what protects them in
# a clean checkout where the logs cannot be re-read.
R9B_ANCHOR_LANES = (R9B_CTL, R9B_CTL_LB, R9B_INC)
# DEVICE IDENTITY, a REQUIRED field of the reference and the whole point of the re-base. Constant
# across all 71 identity readings of the measuring rung (8 session pre-sidecars + 8 post + 8 soak
# marks, 20 G0 capture rows, 24 Full Picture capture rows, the chain's start and end, the freeze
# record), with no other compute process resident at any point. `r7_gates.sh`'s `identity` cell reads
# the uuid below straight out of this file and compares it to the live device, so the pairing of
# numbers to machine cannot silently come apart again.
R9B_BASELINE_DEVICE = {
    "name": "NVIDIA RTX PRO 6000 Blackwell Server Edition",
    "uuid": "GPU-cbaba4fd-068d-d035-1c18-1d9c16f1648b",
    "serial": "1794525048975",
    "driver": "610.57.04",
    "vbios": "98.02.8D.00.08",
    "power cap": "600.00 W",
    "MIG mode": "Disabled",
    "compute mode": "Default",
    "ncu": "2026.2.1.0 (build 38283040)",
    "CUDA": "13.3, V13.3.73",
}
# The run shape the medians were taken at. A future session that differs here is comparing across
# shapes, which is what this line exists to make visible.
R9B_BASELINE_RUN = ("8 lanes, 96 paired rounds / 8 warmup, `--log-trace 24`, carveout 16 % uniform, "
                    "one process per (rotation, order), 80 s discarded soak each, binary sha256 "
                    "`881594043a89`")
# (control@256, control_lb@128, hot16@128) median eval+fin, ms — a THREE-anchor reference.
R9B_BASELINE = {
    "CLASS": {"locality": (16.725, 16.455, 14.793), "census": (16.903, 16.620, 15.352)},
    "BUDGET": {"locality": (16.778, 16.493, 14.823), "census": (16.893, 16.607, 15.347)},
}
# THE FLANK STATUS AT CAPTURE, per baseline session, so a future rung choosing a single canonical pair
# can see it here instead of re-reading the report: the CLASS/census session is the one that moved
# under itself, and BUDGET/census is the flank-clean census reference.
R9B_BASELINE_FLANK = {
    ("CLASS", "locality"): "clean (0.004–0.015 ms drift)",
    ("CLASS", "census"): "**FLANK: 0.088–0.099 ms drift, past its 0.077–0.085 ms readings**",
    ("BUDGET", "locality"): "clean (0.010–0.055 ms drift)",
    ("BUDGET", "census"): "clean (0.011–0.023 ms drift) — the flank-clean census reference",
}
# THE PRE-PROVENANCE BLOCK: every reference the campaign held before the re-base. Reported as context
# and NEVER a flag basis — none of them records the machine it was measured on, and they disagree with
# each other by more than the reporting threshold, so a flag keyed to them would report their mutual
# disagreement rather than the session. The R9 medians are this file's own `reorder_emit` output over
# the archived `.agents/sdd/2026-08-12-v3-r9/reorder-{locality,census}.log`, whose
# `REORDER schedule … lanes=6` field is where the 6 comes from; R4/R5/R8 trace to `ANCHORS`,
# `R5_SESSION` and `R8_SESSION` above. They carry two anchors, not three.
R9_SESSION = {"locality": (16.725, 14.794), "census": (17.011, 15.458)}
R9B_PRE_PROVENANCE = REORDER_REFERENCES + (("R9 session", 6, R9_SESSION),)
R9B_PRE_PROVENANCE_LANES = (R9B_CTL, R9B_INC)
R9B_UNRECORDED = "machine identity: unrecorded"

# THE RETENTION RULE (RR, 2026-08-13), encoded here so a future rung does not have to re-decide it:
#
#   * The PRE-PROVENANCE block is FROZEN AT ITS CURRENT FOUR. Identity capture is mandatory from R9b
#     onward — `tools/gpu_identity.sh` is where a session driver takes telemetry from, and
#     `r7_gates.sh`'s `identity` reading prints the live machine beside the committed one every run —
#     so a FIFTH reference with no recorded machine cannot come into existence. Nothing is ever
#     appended to this block; the guard below is what says so out loud.
#
#   * BASELINES keep TWO LIVE: the current one and the immediately previous one, both in the table.
#     The `ANCHOR` flag keys to the CURRENT one (`R9B_BASELINES[0]`); the previous one is printed
#     beside it as the campaign's own step. When a third arrives, the oldest moves into the ARCHIVED
#     BASELINES comment below — kept for the record, out of the table, and out of the flag.
#
# Newest first. Each entry is (label, {rotation: {order: (ctl, ctl_lb, hot16)}}).
R9B_BASELINES = [("R9b session, 2026-08-13", R9B_BASELINE)]
# ARCHIVED BASELINES, retired from the table by the rule above and kept for the record:
#   (none — R9b is the first baseline this campaign has held. R4/R5/R8/R9 are not baselines; they are
#   the four pre-provenance references, which is a different thing: none of them records a machine.)
assert len(R9B_PRE_PROVENANCE) == 4, (
    "the pre-provenance block is frozen at four (RR 2026-08-13): identity capture is mandatory now, "
    "so a fifth reference without a recorded machine cannot exist. A new reference is a BASELINE — "
    "put it at the head of R9B_BASELINES.")
assert len(R9B_BASELINES) <= 2, (
    "baselines keep two live, the current and the immediately previous one (RR 2026-08-13); move the "
    "oldest into the ARCHIVED BASELINES comment above.")
# The flank sentinels: the three INCUMBENT-body anchor lanes at the incumbent's own budget, which
# both rotations carry. A cell under test — body or budget — is not its own drift sentinel, so every
# grid lane is excluded by construction, the incumbent's two extra budgets included.
R9B_FLANK_LANES = (R9B_CTL, R9B_CTL_LB, R9B_INC)

# THE G0 MANIFEST (amendment A7): every TIMED cell gets its own capture, one launch each, because
# profiling only a chosen few leaves the rest of the register curve resting on static REG lines —
# the exact error R9 documented. Ten cells: the incumbent and the nine the two rotations put on a
# lane beside it.
R9B_G0 = [R9B_INC, R9B_DROPIN, R9B_C, R9B_B, R9B_CD, R9B_BD,
          R9B_INC_LB6, R9B_INC_FREE, R9B_C_LB6, R9B_C_FREE]
R9B_G0_READS = ("allocated-registers", "register-limit", "shared-limit", "warps-limit",
                "blocks-limit", "blocks-per-sm", "achieved-occupancy")
# THE FULL-PICTURE manifest: five FIXED lanes plus ONE conditional slot, the CLASS session's
# lowest-median corrected body. The slot is a capture-set choice and nothing else; it is named as
# PENDING when the CLASS session is not in this invocation.
R9B_FULL = [(R9B_INC, "incumbent"), (R9B_DROPIN, "r9-dropin"),
            (R9B_C_LB6, "c-at-128-6"), (R9B_C_FREE, "c-unbounded"),
            (R9B_INC_FREE, "incumbent-unbounded")]
R9B_FULL_CANDIDATES = (R9B_C, R9B_B, R9B_CD, R9B_BD)

# Every rotation keyword this emitter knows. A schedule or trailer line is bound to a section
# only for these, so a foreign grammar cannot be summarized under one of these rules.
KNOWN = {R4} | set(FRONTIER) | {R8, R9, R9B}


def parse(paths, where):
    runs = defaultdict(lambda: defaultdict(dict))
    arms, done, sched = defaultdict(dict), {}, {}
    # Per-FILE facts: the carveout block a process printed, and the sections it declares. One log
    # is one process, so these are properties of the file rather than of a section — the echoes
    # precede every schedule line.
    files = {}
    for path in paths:
        section = None
        env = files.setdefault(path, {"echoes": [], "symbols": [], "loose": [], "sections": set()})
        for n, raw in enumerate(open(path), 1):
            raw = raw.rstrip("\n")
            line = raw.strip()
            m = ECHO.match(raw)
            if m:
                env["echoes"].append((int(m.group(1)), m.group(2)))
                continue
            m = ECHO_SET.match(raw)
            if m:
                env["symbols"].append((int(m.group(1)), m.group(2).split(", ")))
                continue
            if line.startswith(ECHO_ANY):
                env["loose"].append((n, line))
                continue
            m = SCHED.match(line)
            if m and m.group(1) in KNOWN:
                key = (m.group(1), m.group(2))
                env["sections"].add(key)
                if key in sched:
                    sys.exit(f"{path}:{n}: order={m.group(2)} starts twice — the log mixes runs")
                section = key
                sched[key] = (int(m.group(3)), int(m.group(4)), int(m.group(5)))
                continue
            m = ARM_IDS.match(line) or ARM.match(line)
            if m:
                if section is None:
                    sys.exit(f"{path}:{n}: `ARM {m.group(1)}` before any schedule line — the "
                             f"lane facts cannot be bound to a term order")
                if m.group(1) in arms[section]:
                    sys.exit(f"{path}:{n}: duplicate `ARM {m.group(1)}` for order={section[1]}")
                ids = m.group(10) if m.lastindex == 10 else None
                if (ids is None) != (section[0] == R4):
                    sys.exit(f"{path}:{n}: `ARM {m.group(1)}` carries "
                             f"{'an' if ids is not None else 'no'} admitted-id list under "
                             f"{section[0]} — the two grammars are not interchangeable")
                arms[section][m.group(1)] = {
                    "regs": int(m.group(2)), "blocks_sm": int(m.group(3)),
                    "threads": int(m.group(4)), "grid": int(m.group(5)), "kernel": m.group(6),
                    "c": int(m.group(7)), "removals": int(m.group(8)),
                    "admitted": int(m.group(9)),
                    "ids": [] if ids in (None, "-") else [int(i) for i in ids.split(",")],
                }
                continue
            m = SAMPLE.match(line)
            if m:
                order, rnd, lane, ev, fin, kernel = m.groups()
                if section is not None and order != section[1]:
                    sys.exit(f"{path}:{n}: sample declares order={order} inside the "
                             f"{section[0]} order={section[1]} section — mixed log")
                # Bucketed per ROTATION, so the primary and the extension may legitimately
                # reuse a round id. A row ahead of every schedule line is parked under the
                # `None` tag and collides with the section that later claims its order, so
                # a duplicate is still caught wherever in the file it sits.
                skey = (section[0] if section else None, order)
                bucket = runs[skey][int(rnd)]
                stray = runs.get((None, order), {}).get(int(rnd), {}) if section else {}
                if lane in bucket or lane in stray:
                    sys.exit(f"{path}:{n}: duplicate sample for order={order} round={rnd} "
                             f"lane={lane} — the log mixes runs; emit one session at a time")
                bucket[lane] = (float(ev), float(fin), kernel)
                continue
            m = DONE.match(line)
            if m and m.group(1) in KNOWN:
                key = (m.group(1), m.group(2))
                env["sections"].add(key)
                if key in done:
                    sys.exit(f"{path}:{n}: order={m.group(2)} completes twice — mixed log")
                done[key] = (int(m.group(3)), int(m.group(4)), int(m.group(5)))
    # Adopt the rows that preceded every schedule line into the rotation that declared
    # their order. An order no rotation declared is an error rather than an orphan bucket
    # nothing ever summarizes.
    declared = defaultdict(set)
    for tag, order in set(sched) | set(done):
        declared[order].add(tag)
    for key in [k for k in runs if k[0] is None]:
        order = key[1]
        here = declared.get(order, set())
        if len(here) != 1:
            sys.exit(f"{where}: SAMPLE rows for order={order} precede every schedule line "
                     f"and {len(here)} rotations declare that order — they cannot be bound "
                     f"to one")
        tag = next(iter(here))
        for rnd, bucket in runs.pop(key).items():
            runs[(tag, order)][rnd].update(bucket)
    return runs, arms, done, sched, files


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
    if not rounds:
        sys.exit(f"{order}: the log declares this order ({sched[1]} rounds x {sched[0]} lanes) "
                 f"but carries no SAMPLE rows — a declared order is emitted or it is an "
                 f"error, never silently skipped")
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
    if (sched[1], sched[2]) != (trailer[1], trailer[0]):
        sys.exit(f"{order}: the schedule line declares rounds={sched[1]} warmup={sched[2]} "
                 f"but the trailer declares rounds={trailer[1]} warmup={trailer[0]} — the "
                 f"log mixes two runs, or the header does not describe what ran")
    # ROUND IDS. The runner numbers timed rounds `warmup .. warmup + rounds - 1`, so the ids
    # are a consecutive run with a known anchor. Counting rounds alone accepts gaps,
    # duplicates and a renumbered log (0, 11, 22, … passes `rounds % lanes == 0`).
    want_ids = list(range(trailer[0], trailer[0] + trailer[1]))
    if sorted(rounds) != want_ids:
        got = sorted(rounds)
        sys.exit(f"{order}: round ids are {got[:4]}…{got[-1]}, expected the consecutive run "
                 f"{want_ids[0]}…{want_ids[-1]} (warmup {trailer[0]}, rounds {trailer[1]}) — "
                 f"gaps, duplicates or a renumbered log, none of which is a paired rotation")
    # ROTATION BALANCE. Samples arrive in execution order, so a lane's position inside a
    # round IS its rotation slot. Every lane must take every slot equally often — that is
    # what makes the contrast paired; a lane that keeps a slot carries that slot's clock
    # state into its median. `rounds % lanes == 0` only counts rounds.
    per = len(rounds) // len(lanes)
    slots = defaultdict(int)
    for r in sorted(rounds):
        for slot, lane in enumerate(rounds[r]):
            slots[(lane, slot)] += 1
    for lane in lanes:
        for slot in range(len(lanes)):
            if slots[(lane, slot)] != per:
                sys.exit(f"{order}: lane {lane} runs at rotation position {slot} in "
                         f"{slots[(lane, slot)]} rounds, expected {per} — the rotation is "
                         f"not balanced, so a lane keeps a position and its median carries "
                         f"that position's clock state")
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
        # The denominator is the median of the per-round SUM, not the sum of the two stage
        # medians: the median is not additive, and the numerator is already a per-round sum.
        base = median(rounds[r][b][EV] + rounds[r][b][FIN] for r in keys)
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


# --- v3 R5 frontier emitter -------------------------------------------------------


def signed(diffs, threshold):
    """The preregistered signed rule (spec 2.3): A *wins over* B iff the median of the
    paired per-round contrasts is negative AND at least `threshold` of them are negative;
    *loses* is the mirror; anything else is a *wash*. The threshold is a literal keyed to
    the rotation's preregistered round count, never a ratio recomputed from the log."""
    med = median(diffs)
    neg = sum(1 for x in diffs if x < 0)
    pos = sum(1 for x in diffs if x > 0)
    if med < 0 and neg >= threshold:
        return "win", med, neg
    if med > 0 and pos >= threshold:
        return "lose", med, pos
    return "wash", med, max(neg, pos)


def session(key, rounds, arms, trailer, sched):
    """Every R4 integrity gate, then the two R5 ones (preregistered round count, ordered
    admitted-id prefix), then the per-lane paired series. Fail-closed throughout: a gate
    that cannot be evaluated is an error, never a skipped section."""
    tag, order = key
    spec = FRONTIER[tag]
    # The ±2 % sanity anchors and the R2c bridge base are preregistered per TERM ORDER; an
    # order nobody preregistered has neither, so it is a stated rejection rather than a
    # KeyError two hundred lines later.
    if order not in ANCHORS or order not in R2C:
        sys.exit(f"{tag}/{order}: unknown term order — the sanity anchors and the R2c "
                 f"bridge base are preregistered for {sorted(ANCHORS)} only, so a "
                 f"`{order}` section cannot be decided")
    if not arms:
        sys.exit(f"{tag}/{order}: no ARM lines for this order — old-format or truncated log")
    if trailer is None:
        sys.exit(f"{tag}/{order}: no `{tag} done order={order} …` trailer — the run did not "
                 f"finish, or the log is truncated")
    if sched is None:
        sys.exit(f"{tag}/{order}: ARM or SAMPLE rows with no `{tag} schedule` line")
    if not rounds:
        sys.exit(f"{tag}/{order}: the log declares this order ({sched[1]} rounds x {sched[0]} "
                 f"lanes) but carries no SAMPLE rows — a declared order is emitted or it is "
                 f"an error, never silently skipped")
    lanes = list(arms)
    if set(lanes) != spec["lanes"]:
        missing = sorted(spec["lanes"] - set(lanes))
        extra = sorted(set(lanes) - spec["lanes"])
        sys.exit(f"{tag}/{order}: lane set is not the {spec['what']} frontier rotation — "
                 f"missing {missing}, unexpected {extra}")
    if len(lanes) != trailer[2] or len(lanes) != sched[0]:
        sys.exit(f"{tag}/{order}: {len(lanes)} ARM lines but the trailer declares "
                 f"{trailer[2]} lanes — the log is truncated or mixes builds")
    for r in sorted(rounds):
        if set(rounds[r]) != set(lanes):
            sys.exit(f"{tag}/{order}: round {r} carries {sorted(rounds[r])}, expected "
                     f"{lanes} — incomplete rounds are not droppable, the contrasts are "
                     f"paired")
        for lane, (_, _, kernel) in rounds[r].items():
            if kernel != arms[lane]["kernel"]:
                sys.exit(f"{tag}/{order}: round {r} lane {lane} ran `{kernel}` but its ARM "
                         f"line declares `{arms[lane]['kernel']}` — the log describes a "
                         f"kernel the run did not use")
    if len(rounds) % len(lanes) != 0:
        sys.exit(f"{tag}/{order}: {len(rounds)} rounds over {len(lanes)} lanes is not "
                 f"balanced — every lane must start equally often")
    if len(rounds) != trailer[1]:
        sys.exit(f"{tag}/{order}: {len(rounds)} rounds in the log, trailer claims rounds="
                 f"{trailer[1]} — truncated log")
    if (sched[1], sched[2]) != (trailer[1], trailer[0]):
        sys.exit(f"{tag}/{order}: the schedule line declares rounds={sched[1]} "
                 f"warmup={sched[2]} but the trailer declares rounds={trailer[1]} "
                 f"warmup={trailer[0]} — the log mixes two runs, or the header does not "
                 f"describe what ran")
    # THE PREREGISTERED ROUND COUNT. The signed thresholds are literals (90/100, 94/104),
    # so a log at any other count has no threshold to be judged against — deriving one
    # from the log would be exactly the post-hoc choice preregistration exists to prevent.
    if len(rounds) != spec["rounds"]:
        sys.exit(f"{tag}/{order}: {len(rounds)} timed rounds, but the {spec['what']} "
                 f"frontier is preregistered at {spec['rounds']} with the signed threshold "
                 f"{spec['threshold']}/{spec['rounds']} — no other round count has a "
                 f"preregistered threshold, so this log cannot be decided")
    want_ids = list(range(trailer[0], trailer[0] + trailer[1]))
    if sorted(rounds) != want_ids:
        got = sorted(rounds)
        sys.exit(f"{tag}/{order}: round ids are {got[:4]}…{got[-1]}, expected the "
                 f"consecutive run {want_ids[0]}…{want_ids[-1]} (warmup {trailer[0]}, "
                 f"rounds {trailer[1]}) — gaps, duplicates or a renumbered log, none of "
                 f"which is a paired rotation")
    per = len(rounds) // len(lanes)
    slots = defaultdict(int)
    for r in sorted(rounds):
        for slot, lane in enumerate(rounds[r]):
            slots[(lane, slot)] += 1
    for lane in lanes:
        for slot in range(len(lanes)):
            if slots[(lane, slot)] != per:
                sys.exit(f"{tag}/{order}: lane {lane} runs at rotation position {slot} in "
                         f"{slots[(lane, slot)]} rounds, expected {per} — the rotation is "
                         f"not balanced, so a lane keeps a position and its median carries "
                         f"that position's clock state")
    keys = sorted(rounds)
    # ADMITTED-ID GATE. Ordered, against the controller-derived oracle prefix. Counts are
    # blind to a reversal among equal-ref, equal-class sources; only the LIST sees it.
    for lane in lanes:
        f = arms[lane]
        ids, k = f["ids"], f["admitted"]
        if len(ids) != k:
            sys.exit(f"{tag}/{order}: lane {lane} declares {k} admitted sources but lists "
                     f"{len(ids)} ids")
        if LANE_K[lane] != k:
            sys.exit(f"{tag}/{order}: lane {lane} admits {k} sources but its name claims "
                     f"K = {LANE_K[lane]} — the label and the plan disagree")
        want = ORACLE_ORDER[:k]
        if ids != want:
            at = next(i for i, (g, w) in enumerate(zip(ids, want)) if g != w)
            sys.exit(f"{tag}/{order}: lane {lane} admits source {ids[at]} at admission "
                     f"position {at}, the oracle ordering has {want[at]} — the admitted "
                     f"prefix is not the canonical one (counts cannot see this)")
    # ALIASING GUARD, R4's verbatim: two lanes that declare different plans cannot produce
    # bit-identical per-round samples, and two lanes with one plan are one experiment.
    for i, a in enumerate(lanes):
        for b in lanes[i + 1:]:
            if arms[a]["ids"] == arms[b]["ids"] and arms[a]["threads"] == arms[b]["threads"] \
               and arms[a]["removals"]:
                sys.exit(f"{tag}/{order}: lanes {a} and {b} declare the SAME plan at the "
                         f"same block size — one experiment under two labels")
            if all(rounds[r][a][:2] == rounds[r][b][:2] for r in keys):
                sys.exit(f"{tag}/{order}: lanes {a} and {b} carry BIT-IDENTICAL samples in "
                         f"every round — the log aliases one lane's data onto another")
    # eval + finalize per round IS the decision quantity (spec 2.3: the bar is on the
    # eval+finalize median, and finalize is the stage the block sizes differ on).
    tot = {a: [rounds[r][a][0] + rounds[r][a][1] for r in keys] for a in lanes}
    return {
        "tag": tag, "order": order, "spec": spec, "lanes": lanes, "arms": arms,
        "rounds": rounds, "keys": keys, "tot": tot,
        "med": {a: median(tot[a]) for a in lanes},
        "med_ev": {a: median(rounds[r][a][0] for r in keys) for a in lanes},
        "med_fin": {a: median(rounds[r][a][1] for r in keys) for a in lanes},
    }


def paired(s, a, b):
    """The paired per-round contrast `a - b` on eval+finalize, with its signed verdict."""
    d = [x - y for x, y in zip(s["tot"][a], s["tot"][b])]
    verdict, med, on = signed(d, s["spec"]["threshold"])
    lo, hi = iqr(d)
    return {"med": med, "lo": lo, "hi": hi, "on": on, "n": len(d), "verdict": verdict}


def canonical(s):
    """The canonical prefix points of one session, in C order. `cache0` and the controls
    admit nothing, so they are baselines rather than points on the frontier."""
    return sorted((a for a in s["lanes"] if s["arms"][a]["admitted"] > 0),
                  key=lambda a: s["arms"][a]["c"])


def curve(s, base, title, rule, per_removal=None):
    print(f"\n**{title}** — baseline `{base}`, paired per round on `eval + finalize`. "
          f"{rule}\n")
    head = "| lane | C | removals | median (ms) | IQR | on-sign | signed verdict |"
    rule_row = "| --- | --- | --- | --- | --- | --- | --- |"
    if per_removal:
        head += f" {per_removal} |"
        rule_row += " --- |"
    print(head)
    print(rule_row)
    for lane in canonical(s):
        if lane == base:
            continue
        f, c = s["arms"][lane], paired(s, lane, base)
        row = (f"| `{lane}` | {f['c']} | {f['removals']} | **{c['med']:+.3f}** | "
               f"{c['lo']:+.3f} … {c['hi']:+.3f} | {c['on']}/{c['n']} | **{c['verdict']}** |")
        if per_removal:
            # Removals come off the ARM lines, which Rust fills from the lane's own planned
            # counts — this script holds no removal constant of its own.
            denom = f["removals"] - s["arms"][base]["removals"]
            row += f" {1000.0 * c['med'] / denom:+.2f} |" if denom else " n/a |"
        print(row)


def frontier(orders, tags, runs, arms, done, sched, where):
    sessions = {}
    for tag in tags:
        for order in orders:
            key = (tag, order)
            if key not in sched and key not in runs:
                continue
            sessions[key] = session(key, runs[key], arms.get(key, {}), done.get(key),
                                    sched.get(key))
    if not sessions:
        sys.exit(f"{where}: no frontier section survived the order filter")

    print("## v3 R5 — admission-frontier curves\n")
    print("Every figure below is EMITTED, not transcribed: this script is the single "
          "authority for the derived decisions, and each decision line names the "
          "preregistered rule (spec 2.3) it implements. Contrasts are paired per round on "
          "`eval + finalize` — the bar quantity — and curves are NEVER pooled across term "
          "orders.\n")

    for key in sorted(sessions, key=lambda k: (k[0] != "FRONTIER-FACTORIAL",
                                               k[1] != "locality", k[1])):
        emit_session(sessions[key])

    decide(sessions, orders)


def emit_session(s):
    tag, order, spec = s["tag"], s["order"], s["spec"]
    print(f"\n### `{tag}` — `--term-order {order}`, {len(s['keys'])} paired rounds, "
          f"{len(s['lanes'])} lanes\n")
    print("| lane | kernel | regs | blocks/SM | threads | grid | C | removals | admitted | "
          "median `eval` | median `finalize` | median `eval+fin` |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    for a in s["lanes"]:
        f = s["arms"][a]
        print(f"| `{a}` | `{f['kernel']}` | {f['regs']} | {f['blocks_sm']} | {f['threads']} | "
              f"{f['grid']} | {f['c']} | {f['removals']} | {f['admitted']} | "
              f"{s['med_ev'][a]:.3f} | {s['med_fin'][a]:.3f} | **{s['med'][a]:.3f}** |")
    print(f"\nAdmitted-id lists gated ORDERED against the controller oracle "
          f"(`expected-counts-r5.md` / `oracle-derivation.txt`), all {len(s['lanes'])} "
          f"lanes. Signed rule at this rotation: "
          f"{spec['threshold']}/{spec['rounds']} (spec 2.3, preregistered literal).")

    curve(s, "control_lb@128", "Curve 1 — total-net vs `control_lb@128`",
          "The bound-matched baseline; this is the curve C\\* is read off (spec 2.3).")
    curve(s, "hot16@128", "Curve 2 — marginal vs `hot16@128`",
          "The incumbent. Per-removal column divides by the INCREMENTAL removals over "
          "hot16, from the ARM lines.", per_removal="µs / incremental removal")
    curve(s, "cache0@128", "Curve 3 — machinery-corrected refund vs `cache0@128`",
          "cache0 pays the frame, the walk and the lookup and removes nothing, so this "
          "curve is the removals alone. Per-removal column divides by the lane's own "
          "removals.", per_removal="µs / removal")

    # C* — spec 2.3: the most negative median vs control_lb@128 among lanes that WIN over
    # control_lb@128 under the signed rule.
    winners = [(paired(s, a, "control_lb@128"), a) for a in canonical(s)]
    winners = [(c, a) for c, a in winners if c["verdict"] == "win"]
    if winners:
        best = min(winners, key=lambda t: t[0]["med"])
        print(f"\n**Session optimum ({order}, {tag})** = `{best[1]}` at C = "
              f"{s['arms'][best[1]]['c']} units, {best[0]['med']:+.3f} ms vs "
              f"`control_lb@128` ({best[0]['on']}/{best[0]['n']} on-sign) — the spec 2.3 "
              f"rule applied WITHIN this rotation; C\\* for the order is taken over the "
              f"union of the rotations below.")
    else:
        print(f"\n**Session optimum ({order}, {tag})** = none — no canonical lane wins "
              f"over `control_lb@128` under the signed rule (spec 2.3).")

    # Sanity anchors — spec 2.3. The emitter states in/out; the abort/repeat/paired-only
    # rule is the measurement task's to execute.
    print(f"\n**Sanity anchors ({order})** — spec 2.3, +/-2 % of R4's frozen in-rotation "
          f"medians. The verdict below is the deterministic rule's INPUT; executing "
          f"abort -> one repeat -> PAIRED RESULTS ONLY is the measurement task's.\n")
    print("| anchor | this session | R4 frozen | delta | verdict |")
    print("| --- | --- | --- | --- | --- |")
    s["sanity"] = True
    for lane, target in zip(("control@256", "hot16@128"), ANCHORS[order]):
        got = s["med"][lane]
        rel = (got - target) / target
        ok = abs(rel) <= SANITY_TOL
        s["sanity"] = s["sanity"] and ok
        print(f"| `{lane}` | {got:.3f} | {target:.3f} | {100.0 * rel:+.2f} % | "
              f"**{'IN' if ok else 'OUT'}** |")


def union(sessions, order):
    """Every canonical lane measured in `order`, in C order, each bound to the session that
    measured it. A lane in both sessions is taken from the PRIMARY rotation (deterministic
    rule, stated in the emitted line): cross-session lanes are only ever compared through
    the anchors both rotations carry, never raw."""
    picked = {}
    for tag in ("FRONTIER-FACTORIAL", "FRONTIER-EXTENSION"):
        s = sessions.get((tag, order))
        if s is None:
            continue
        for lane in canonical(s):
            picked.setdefault(lane, s)
    return sorted(picked.items(), key=lambda kv: kv[1]["arms"][kv[0]]["c"])


def winner_of(sessions, order):
    """One computation of an order's frontier shape, shared by the emitted table and the
    ncu manifest: the union lanes in C order, their net contrasts vs `control_lb@128`, and
    the winner (spec 2.3 — most negative median among the lanes that WIN over the
    bound-matched control), or `None` when nothing wins."""
    lanes = union(sessions, order)
    nets = {lane: paired(s, lane, "control_lb@128") for lane, s in lanes}
    won = [(lane, s) for lane, s in lanes if nets[lane]["verdict"] == "win"]
    if not won:
        return lanes, nets, None, None
    winner, wsession = min(won, key=lambda t: nets[t[0]]["med"])
    return lanes, nets, winner, wsession


def first_loser_of(lanes, winner, wsession):
    """spec 2.5: the smallest-C lane ABOVE the winner that LOSES to it in that order.
    Returns `(hit, unpairable)`; the signed rule is paired, so a lane that shares no
    rotation with the winner is reported rather than guessed at."""
    unpairable = []
    for lane, s in lanes:
        if s["arms"][lane]["c"] <= wsession["arms"][winner]["c"]:
            continue
        if winner not in s["arms"]:
            unpairable.append(lane)
            continue
        if paired(s, lane, winner)["verdict"] == "lose":
            return (lane, s), unpairable
    return None, unpairable


def neighbours_of(order_list, lane, extension):
    """spec 2.5: a lane's available canonical prefix neighbours — one below, one above. The
    TOP endpoint has no lane above, so it takes its single neighbour plus the extension's
    first lane when the extension ran; the BOTTOM endpoint simply has one neighbour."""
    if lane not in order_list:
        return []
    i = order_list.index(lane)
    out = [order_list[i - 1]] if i > 0 else []
    if i + 1 < len(order_list):
        out.append(order_list[i + 1])
    elif extension and extension != lane:
        out.append(extension)
    return out


def where_measured(sessions, order, lane):
    """The rotation a lane's raw median is read from, PRIMARY first — the same rule the
    union table states, so the bar verdict and the bridges cannot drift from the curves."""
    for tag in ("FRONTIER-FACTORIAL", "FRONTIER-EXTENSION"):
        s = sessions.get((tag, order))
        if s is not None and lane in s["arms"]:
            return s
    return None


def decide(sessions, orders):
    orders = [o for o in orders if any(k[1] == o for k in sessions)]
    primary = {o: sessions.get(("FRONTIER-FACTORIAL", o)) for o in orders}
    extension_ran = any(k[0] == "FRONTIER-EXTENSION" for k in sessions)
    # Every rule below that says "either order" or "BOTH orders" needs both present. One
    # order in is a valid input, but it must be SAID, not silently collapsed.
    both_orders = len(orders) >= 2

    print("\n### Preregistered decisions\n")
    if not both_orders:
        print(f"> **SINGLE ORDER.** This log set carries `{orders[0]}` only (one order's "
              f"logs, or `--order` narrowed it). The per-order sections below stand; the "
              f"cross-order rules — the extension trigger's *either order*, the headline "
              f"selector's *BOTH orders*, the bar verdict and the bridges — are flagged "
              f"where they are not evaluable.\n")

    # EXTENSION TRIGGER — spec 2.3: triggers iff k48 WINS over k46 (signed) in either
    # order. A wash does NOT trigger.
    lines = []
    triggered = False
    for o in orders:
        s = primary[o]
        if s is None or "k46@128" not in s["arms"]:
            lines.append(f"- `{o}`: not evaluable — no primary rotation carrying k46 and k48.")
            continue
        c = paired(s, "k48@128", "k46@128")
        triggered = triggered or c["verdict"] == "win"
        lines.append(f"- `{o}`: k48 − k46 = {c['med']:+.3f} ms ({c['on']}/{c['n']} on-sign) "
                     f"⇒ **{c['verdict']}**")
    print("**Extension trigger** (spec 2.3: triggers iff k48 *wins over* k46 under the "
          "signed rule in EITHER order; a wash does not trigger):\n")
    print("\n".join(lines))
    print(f"\n⇒ extension **{'TRIGGERED' if triggered else 'NOT triggered'}**; the "
          f"extension rotation {'IS' if extension_ran else 'is NOT'} present in this log "
          f"set."
          + ("" if both_orders else
             f" **Evaluated over `{orders[0]}` ALONE** — spec 2.3's *either order* spans "
             f"both, so a NOT-triggered verdict here is provisional until the other "
             f"order's log is included."))

    # PER-ORDER FRONTIER SHAPE: winner, broad knee, first loser, right-censoring.
    broad_any = False
    for o in orders:
        lanes, nets, winner, wsession = winner_of(sessions, o)
        if not lanes:
            continue
        print(f"\n**Frontier shape — `{o}`** (union of the rotations, in C order; a lane "
              f"present in both sessions is taken from the primary rotation, and every "
              f"cross-session comparison rides the shared `control_lb@128` anchor):\n")
        print("| lane | session | C | net vs `control_lb@128` | signed verdict |")
        print("| --- | --- | --- | --- | --- |")
        for lane, s in lanes:
            print(f"| `{lane}` | {s['tag']} | {s['arms'][lane]['c']} | "
                  f"{nets[lane]['med']:+.3f} | {nets[lane]['verdict']} |")
        if winner is None:
            # spec 4's OTHER edge: nothing in the sweep beats the bound-matched control, so
            # the knee sits BELOW C = 36 rather than past the top lane. Right-censoring is
            # the opposite outcome and must not be reported here.
            print(f"\n- winner: **none** — no canonical lane wins over `control_lb@128` "
                  f"in `{o}` (spec 2.3).")
            print(f"- the knee is BELOW this sweep for `{o}`: the rung answers with "
                  f"**hot16 already ≈ optimal** (spec 4, a valid and recordable outcome). "
                  f"This is NOT right-censoring, which is the opposite edge.")
            continue
        print(f"\n- winner (C\\*): **`{winner}`** at C = {wsession['arms'][winner]['c']}, "
              f"{nets[winner]['med']:+.3f} ms vs `control_lb@128` — spec 2.3.")
        # BROAD KNEE — spec 2.3: >= 3 CONSECUTIVE canonical lanes within 0.10 ms of the
        # per-order optimum, in EITHER order. Measured in the net-vs-control_lb currency,
        # which is what makes the seam-spanning comparison legitimate.
        best = nets[winner]["med"]
        near = [abs(nets[lane]["med"] - best) <= KNEE_MS for lane, _ in lanes]
        run = best_run = 0
        for flag in near:
            run = run + 1 if flag else 0
            best_run = max(best_run, run)
        broad = best_run >= 3
        broad_any = broad_any or broad
        print(f"- broad knee in `{o}`: **{'yes' if broad else 'no'}** — longest run of "
              f"consecutive canonical lanes within {KNEE_MS:.2f} ms of the optimum is "
              f"{best_run} (spec 2.3 needs >= 3).")
        hit, unpairable = first_loser_of(lanes, winner, wsession)
        if hit:
            lane, s = hit
            c = paired(s, lane, winner)
            print(f"- first loser in `{o}`: **`{lane}`** (C = {s['arms'][lane]['c']}), "
                  f"{c['med']:+.3f} ms vs the winner, {c['on']}/{c['n']} on-sign — spec 2.5.")
        else:
            edge = lanes[-1][0]
            print(f"- first loser in `{o}`: **none** — no canonical lane above the winner "
                  f"loses to it under the signed rule.")
            print(f"- the frontier is reported **RIGHT-CENSORED at {edge}** for `{o}` and "
                  f"NO located-knee claim is made (spec 4); the follow-up decision "
                  f"(extend further vs. move to the D rung) is left to RR.")
        if unpairable:
            print(f"- not decidable across the session seam in `{o}`: "
                  f"{', '.join(f'`{x}`' for x in unpairable)} — those lanes do not share a "
                  f"rotation with the winner, and the signed rule is paired.")
    print(f"\n**Broad-knee verdict (either order, spec 2.3)**: "
          f"**{'BROAD' if broad_any else 'not broad'}** — this gates the preregistered "
          f"reuse-distance follow-up, which is NOT part of this rung.")

    # HEADLINE SELECTOR — spec 2.3, verbatim: eligible = wins over hot16@128 under BOTH
    # orders; select the maximum WORST-order improvement; ties break toward smaller C.
    #
    # BOTH orders is a REQUIREMENT of the rule, not a convenience: with one order present
    # the eligibility test degenerates to a single-order win and would silently promote a
    # lane the rule never qualified. One order in, no candidate out — and with no candidate
    # there is nothing for the bar verdict or the bridges to be about.
    print("\n**Headline selector** (spec 2.3: eligible = lanes that win over `hot16@128` "
          "under BOTH orders; select the maximum WORST-order improvement; ties break "
          "toward smaller C). Selection runs on the FULL-PRECISION medians, so two rows "
          "that print equal need not be tied:\n")
    marginal = defaultdict(dict)
    for o in orders:
        for lane, s in union(sessions, o):
            if lane == "hot16@128":
                continue
            marginal[lane][o] = (paired(s, lane, "hot16@128"), s)
    eligible = [lane for lane, per in marginal.items()
                if len(per) == len(orders)
                and all(c["verdict"] == "win" for c, _ in per.values())]
    print("| lane | C | " + " | ".join(f"vs hot16 (`{o}`)" for o in orders)
          + " | worst order | eligible |")
    print("| --- | --- | " + " | ".join("---" for _ in orders) + " | --- | --- |")
    for lane in sorted(marginal, key=lambda x: next(iter(marginal[x].values()))[1]["arms"][x]["c"]):
        per = marginal[lane]
        c_units = next(iter(per.values()))[1]["arms"][lane]["c"]
        cells = []
        for o in orders:
            if o in per:
                c, _ = per[o]
                cells.append(f"{c['med']:+.3f} ({c['verdict']})")
            else:
                cells.append("n/a")
        worst = max((per[o][0]["med"] for o in orders if o in per), default=float("nan"))
        print(f"| `{lane}` | {c_units} | " + " | ".join(cells)
              + f" | {worst:+.4f} | {'yes' if lane in eligible else 'no'} |")
    if not both_orders:
        headline = None
        print(f"\n⇒ **SINGLE ORDER — the both-order eligibility rule is not evaluable; no "
              f"headline, no bar verdict** (spec 2.3). This log set carries only "
              f"`{orders[0]}`, and eligibility requires a win over `hot16@128` under BOTH "
              f"orders; the `eligible` column above is a single-order win, NOT the rule. "
              f"Re-run the emitter over both orders' logs, without `--order`, to decide. "
              f"The R4 bridges are omitted with it — they corroborate a selected candidate.")
    elif eligible:
        headline = min(eligible, key=lambda lane: (
            max(marginal[lane][o][0]["med"] for o in orders),
            next(iter(marginal[lane].values()))[1]["arms"][lane]["c"]))
        worst = max(marginal[headline][o][0]["med"] for o in orders)
        print(f"\n⇒ **headline candidate = `{headline}`**, worst-order improvement over "
              f"`hot16@128` = {worst:+.3f} ms.")
    else:
        headline = "hot16@128"
        print("\n⇒ eligible set is EMPTY ⇒ **hot16 remains the frontier optimum** (spec "
              "2.3 — a valid outcome).")

    if headline is not None:
        # BAR — spec 2.3: the selected K's eval+finalize median under 14.61 ms in BOTH
        # orders, this session, raw.
        print(f"\n**Bar verdict** (spec 2.3: the selected lane's raw `eval+finalize` "
              f"median below {BAR} ms in BOTH orders, this session):\n")
        print("| order | lane | raw median | vs bar |")
        print("| --- | --- | --- | --- |")
        raw_ok = True
        for o in orders:
            s = where_measured(sessions, o, headline)
            if s is None:
                print(f"| `{o}` | `{headline}` | n/a | not measured |")
                raw_ok = False
                continue
            got = s["med"][headline]
            ok = got < BAR
            raw_ok = raw_ok and ok
            print(f"| `{o}` | `{headline}` | {got:.3f} | **{'under' if ok else 'over'}** |")
        print(f"\n⇒ bar **{'MET' if raw_ok else 'NOT met'}** raw. Sanity anchors "
              f"{'all IN' if all(s['sanity'] for s in sessions.values()) else 'NOT all in'} "
              f"±2 % — a session with an OUT anchor reports PAIRED RESULTS ONLY and this "
              f"raw claim does not stand (spec 2.3).")

        # R4 BRIDGES — unconditional, both forms, both bases.
        print(f"\n**R4 dual bridges for `{headline}`** (unconditional corroboration; "
              f"additive = R2c + (medW − medBase), ratio = R2c × medW / medBase, "
              f"R2c = 16.453 census / 16.283 locality):\n")
        print("| order | base | medW | medBase | additive | ratio |")
        print("| --- | --- | --- | --- | --- | --- |")
        for o in orders:
            s = where_measured(sessions, o, headline)
            if s is None:
                continue
            for base in ("control@256", "control_lb@128"):
                w, b = s["med"][headline], s["med"][base]
                print(f"| `{o}` | `{base}` | {w:.3f} | {b:.3f} | {R2C[o] + (w - b):.3f} | "
                      f"{R2C[o] * w / b:.3f} |")

    # NCU MANIFEST — machine-readable, deduplicated; consumed as authoritative.
    roles = defaultdict(set)
    orders_of = defaultdict(set)
    # "the extension's first lane" (spec 2.5) = its lowest-C canonical lane that the
    # primary rotation does not already carry; k48 rides along as the paired seam anchor.
    in_primary = {lane for k in sessions if k[0] == "FRONTIER-FACTORIAL"
                  for lane in canonical(sessions[k])}
    extension = next((lane for k in sorted(sessions) if k[0] == "FRONTIER-EXTENSION"
                      for lane in canonical(sessions[k]) if lane not in in_primary), None)
    for o in orders:
        lanes, nets, winner, wsession = winner_of(sessions, o)
        if not lanes:
            continue
        order_list = [lane for lane, _ in lanes]
        for lane in order_list:
            orders_of[lane].add(o)
        # spec 2.5 expands neighbours around EACH of "these lanes" — the order's winner AND
        # the selected headline candidate, which can be a third lane different from both
        # orders' winners. Expanding around the winners alone drops the headline's own
        # neighbours from the capture set.
        for lane in ([winner] if winner else []) + ([headline] if headline else []):
            if lane not in order_list:
                continue
            for near in neighbours_of(order_list, lane, extension):
                roles[near].add("neighbor")
        if winner is None:
            continue
        roles[winner].add("winner")
        hit, _ = first_loser_of(lanes, winner, wsession)
        if hit:
            roles[hit[0]].add("first-loser")
    if headline is not None:
        roles[headline].add("headline")
    print("\n### ncu capture manifest\n")
    print("Deduplicated union of the per-order winners, the headline candidate, the "
          "canonical neighbours of BOTH, and the per-order first losers, each under both "
          "term orders (spec 2.5). Task 4 consumes this block as AUTHORITATIVE and does "
          "not reconstruct it.\n")
    if headline is None:
        print("**Incomplete for Task 4**: no headline candidate was selectable (see the "
              "selector above), so the manifest carries the per-order winners, their "
              "neighbours and the first losers only.\n")
    print("```")
    for lane in sorted(roles, key=lambda x: (len(orders_of[x]) == 0, x)):
        print(f"NCU-CAPTURE lane={lane} orders={','.join(sorted(orders_of[lane])) or 'n/a'} "
              f"roles={','.join(sorted(roles[lane]))}")
    print("```")


# --- v3 R8 interior emitter -------------------------------------------------------
#
# DEDICATED (amendment A2). Everything above this line is written around the two R5
# rotations: their lane sets, their per-rotation thresholds, C\*, the extension trigger, the
# broad knee, the both-orders headline selector. R8 sweeps ONE contiguous axis and asks a
# different question — where the loss begins, whether it is monotone, and what each step costs
# per removed production — so it carries its own validator, its own decision rows and its own
# manifest, and the R5 path is left byte-identical.


def ipaired(s, a, b):
    """The paired per-round contrast `a - b` on `eval + finalize`, under R8's signed rule
    (amendment A1): a WIN or a LOSS needs sign-stability >= 87/96; anything below that, either
    sign, is a WASH."""
    d = [x - y for x, y in zip(s["tot"][a], s["tot"][b])]
    verdict, med, on = signed(d, INTERIOR["threshold"])
    lo, hi = iqr(d)
    return {"med": med, "lo": lo, "hi": hi, "on": on, "n": len(d), "verdict": verdict}


def interior_session(key, rounds, arms, trailer, sched):
    """The R8 log contract, fail-closed (amendment A5): exactly this rotation, recorded at
    `--log-trace 24`, at 96 rounds / 12 warmup, with ordered admitted prefixes and the
    one-BF-per-step axis the counts oracle derives. A gate that cannot be evaluated is an
    error, never a skipped section."""
    order = key[1]
    if order not in ANCHORS or order not in R5_SESSION:
        sys.exit(f"{R8}/{order}: unknown term order — the R4-frozen anchor band is "
                 f"preregistered for {sorted(ANCHORS)} only, so a `{order}` section cannot be "
                 f"adjudicated")
    if not arms:
        sys.exit(f"{R8}/{order}: no ARM lines for this order — old-format or truncated log")
    if trailer is None:
        sys.exit(f"{R8}/{order}: no `{R8} done order={order} …` trailer — the run did not "
                 f"finish, or the log is truncated")
    if sched is None:
        sys.exit(f"{R8}/{order}: ARM or SAMPLE rows with no `{R8} schedule` line")
    if not rounds:
        sys.exit(f"{R8}/{order}: the log declares this order ({sched[1]} rounds x {sched[0]} "
                 f"lanes) but carries no SAMPLE rows — a declared order is emitted or it is an "
                 f"error, never silently skipped")
    lanes = list(arms)
    if set(lanes) != INTERIOR["lanes"]:
        missing = sorted(INTERIOR["lanes"] - set(lanes))
        extra = sorted(set(lanes) - INTERIOR["lanes"])
        sys.exit(f"{R8}/{order}: lane set is not the interior rotation — missing {missing}, "
                 f"unexpected {extra}")
    if len(lanes) != trailer[2] or len(lanes) != sched[0]:
        sys.exit(f"{R8}/{order}: {len(lanes)} ARM lines but the trailer declares {trailer[2]} "
                 f"lanes — the log is truncated or mixes builds")
    for lane in lanes:
        want = INTERIOR_GRID[lane]
        if arms[lane]["grid"] != want:
            sys.exit(f"{R8}/{order}: lane {lane} declares grid={arms[lane]['grid']}, and this "
                     f"rung's lanes are preregistered at `--log-trace {INTERIOR_TRACE}`, where "
                     f"it is {want} — a session recorded at another trace is internally "
                     f"consistent, so nothing else would see it")
    if (sched[1], sched[2]) != (trailer[1], trailer[0]):
        sys.exit(f"{R8}/{order}: the schedule line declares rounds={sched[1]} "
                 f"warmup={sched[2]} but the trailer declares rounds={trailer[1]} "
                 f"warmup={trailer[0]} — the log mixes two runs, or the header does not "
                 f"describe what ran")
    # THE PREREGISTERED SHAPE. The signed threshold is a literal keyed to 96 rounds, and the
    # flank rule reads the first and last full 12-round cycle, so neither a different round
    # count nor a partial-cycle warmup has a preregistered rule to be decided under.
    if (trailer[1], trailer[0]) != (INTERIOR["rounds"], INTERIOR["warmup"]):
        sys.exit(f"{R8}/{order}: the log declares rounds={trailer[1]} warmup={trailer[0]}, "
                 f"and the interior rotation is preregistered at {INTERIOR['rounds']} rounds / "
                 f"{INTERIOR['warmup']} warmup with the signed threshold "
                 f"{INTERIOR['threshold']}/{INTERIOR['rounds']} (A1/A5) — no other shape has a "
                 f"preregistered threshold, so this log cannot be decided")
    for r in sorted(rounds):
        if set(rounds[r]) != set(lanes):
            sys.exit(f"{R8}/{order}: round {r} carries {sorted(rounds[r])}, expected {lanes} — "
                     f"incomplete rounds are not droppable, the contrasts are paired")
        for lane, (_, _, kernel) in rounds[r].items():
            if kernel != arms[lane]["kernel"]:
                sys.exit(f"{R8}/{order}: round {r} lane {lane} ran `{kernel}` but its ARM line "
                         f"declares `{arms[lane]['kernel']}` — the log describes a kernel the "
                         f"run did not use")
    if len(rounds) != trailer[1]:
        sys.exit(f"{R8}/{order}: {len(rounds)} rounds in the log, trailer claims rounds="
                 f"{trailer[1]} — truncated log")
    if len(rounds) % len(lanes) != 0:
        sys.exit(f"{R8}/{order}: {len(rounds)} rounds over {len(lanes)} lanes is not balanced — "
                 f"every lane must start equally often")
    want_ids = list(range(trailer[0], trailer[0] + trailer[1]))
    if sorted(rounds) != want_ids:
        got = sorted(rounds)
        sys.exit(f"{R8}/{order}: round ids are {got[:4]}…{got[-1]}, expected the consecutive "
                 f"run {want_ids[0]}…{want_ids[-1]} (warmup {trailer[0]}, rounds {trailer[1]}) "
                 f"— gaps, duplicates or a renumbered log, none of which is a paired rotation")
    per = len(rounds) // len(lanes)
    slots = defaultdict(int)
    for r in sorted(rounds):
        for slot, lane in enumerate(rounds[r]):
            slots[(lane, slot)] += 1
    for lane in lanes:
        for slot in range(len(lanes)):
            if slots[(lane, slot)] != per:
                sys.exit(f"{R8}/{order}: lane {lane} runs at rotation position {slot} in "
                         f"{slots[(lane, slot)]} rounds, expected {per} — the rotation is not "
                         f"balanced, so a lane keeps a position and its median carries that "
                         f"position's clock state")
    keys = sorted(rounds)
    # ADMITTED-ID GATE, ordered against the controller-derived oracle prefix. The interior
    # points differ from one another by ONE source, so a reversal among equal-ref sources moves
    # no count at all; only the list sees it.
    for lane in lanes:
        f = arms[lane]
        ids, k = f["ids"], f["admitted"]
        if len(ids) != k:
            sys.exit(f"{R8}/{order}: lane {lane} declares {k} admitted sources but lists "
                     f"{len(ids)} ids")
        if LANE_K[lane] != k:
            sys.exit(f"{R8}/{order}: lane {lane} admits {k} sources but its name claims K = "
                     f"{LANE_K[lane]} — the label and the plan disagree")
        want = ORACLE_ORDER[:k]
        if ids != want:
            at = next(i for i, (g, w) in enumerate(zip(ids, want)) if g != w)
            sys.exit(f"{R8}/{order}: lane {lane} admits source {ids[at]} at admission position "
                     f"{at}, the oracle ordering has {want[at]} — the admitted prefix is not "
                     f"the canonical one (counts cannot see this)")
    for i, a in enumerate(lanes):
        for b in lanes[i + 1:]:
            if arms[a]["ids"] == arms[b]["ids"] and arms[a]["threads"] == arms[b]["threads"] \
               and arms[a]["removals"]:
                sys.exit(f"{R8}/{order}: lanes {a} and {b} declare the SAME plan at the same "
                         f"block size — one experiment under two labels")
            if all(rounds[r][a][:2] == rounds[r][b][:2] for r in keys):
                sys.exit(f"{R8}/{order}: lanes {a} and {b} carry BIT-IDENTICAL samples in every "
                         f"round — the log aliases one lane's data onto another")
    # THE AXIS, checked rather than trusted. Every step from hot16 through k24 admits exactly
    # one more source at refs 3, which is one more slab unit and two more removals. The
    # per-removal columns divide by these DELTAS off the ARM lines, so a log whose axis is not
    # this one would be priced in a currency the rung never preregistered.
    for below, above in zip(INTERIOR_AXIS, INTERIOR_AXIS[1:]):
        step = tuple(arms[above][f] - arms[below][f] for f in ("admitted", "c", "removals"))
        if step != (1, 1, 2):
            sys.exit(f"{R8}/{order}: the step {above} − {below} moves (admitted, C, removals) "
                     f"by {step}; the interior axis is one BF source at refs 3 per step = "
                     f"(1, 1, 2), and the per-removal columns divide by those deltas")
    tot = {a: [rounds[r][a][0] + rounds[r][a][1] for r in keys] for a in lanes}
    return {
        "order": order, "lanes": lanes, "arms": arms, "rounds": rounds, "keys": keys,
        "tot": tot,
        "med": {a: median(tot[a]) for a in lanes},
        "med_ev": {a: median(rounds[r][a][0] for r in keys) for a in lanes},
        "med_fin": {a: median(rounds[r][a][1] for r in keys) for a in lanes},
    }


def interior_shape(s):
    """One order's frontier shape (amendment A1): the eight adjacent steps in axis order, the
    eight cumulative contrasts against the incumbent, the winner (most negative cumulative
    median among the signed WINs, ties toward smaller K) and the first loser (the smallest n
    whose cumulative contrast is a signed LOSS)."""
    steps = [(above, below, ipaired(s, above, below))
             for below, above in zip(INTERIOR_AXIS, INTERIOR_AXIS[1:])]
    cum = {lane: ipaired(s, lane, INTERIOR_AXIS[0]) for lane in INTERIOR_AXIS[1:]}
    wins = [lane for lane in INTERIOR_AXIS[1:] if cum[lane]["verdict"] == "win"]
    winner = min(wins, key=lambda lane: (cum[lane]["med"], LANE_K[lane])) if wins else None
    loser = next((lane for lane in INTERIOR_AXIS[1:] if cum[lane]["verdict"] == "lose"), None)
    return steps, cum, winner, loser


def interior_flank(s, lane):
    """The first and last full cycle's block medians for one anchor lane, with the scaled
    threshold that goes with it (amendment A6)."""
    cycle = len(s["lanes"])
    first = median(s["tot"][lane][:cycle])
    last = median(s["tot"][lane][-cycle:])
    return first, last, abs(last - first), max(FLANK_MS, FLANK_REL * s["med"][lane])


def interior_emit(s):
    order = s["order"]
    steps, cum, winner, loser = interior_shape(s)
    print(f"\n### `{R8}` — `--term-order {order}`, {len(s['keys'])} paired rounds, "
          f"{len(s['lanes'])} lanes\n")
    print("| lane | kernel | regs | blocks/SM | threads | grid | C | removals | admitted | "
          "median `eval` | median `finalize` | median `eval+fin` |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    for a in s["lanes"]:
        f = s["arms"][a]
        print(f"| `{a}` | `{f['kernel']}` | {f['regs']} | {f['blocks_sm']} | {f['threads']} | "
              f"{f['grid']} | {f['c']} | {f['removals']} | {f['admitted']} | "
              f"{s['med_ev'][a]:.3f} | {s['med_fin'][a]:.3f} | **{s['med'][a]:.3f}** |")
    print(f"\nAdmitted-id lists gated ORDERED against the controller oracle "
          f"(`expected-counts-r8.md` / `oracle-derivation.txt`), all {len(s['lanes'])} lanes; "
          f"grids gated against `--log-trace {INTERIOR_TRACE}`. Signed rule at this rotation: "
          f"{INTERIOR['threshold']}/{INTERIOR['rounds']} (amendment A1, preregistered "
          f"literal).")

    print(f"\n**Adjacent steps ({order})** — each step admits ONE more BF source at refs 3, so "
          f"it removes two productions; paired per round on `eval + finalize`.\n")
    print("| step | K | C step | removals step | median (ms) | IQR | on-sign | verdict | "
          "µs / removal |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    for above, below, c in steps:
        f, g = s["arms"][above], s["arms"][below]
        # The divisor is the removals DELTA off the two ARM lines, which Rust fills from each
        # lane's own planned counts — this emitter holds no removal constant.
        rm = f["removals"] - g["removals"]
        print(f"| `{above}` − `{below}` | {f['admitted']} | +{f['c'] - g['c']} | +{rm} | "
              f"**{c['med']:+.3f}** | {c['lo']:+.3f} … {c['hi']:+.3f} | {c['on']}/{c['n']} | "
              f"**{VERDICT[c['verdict']]}** | {1000.0 * c['med'] / rm:+.2f} |")

    base = INTERIOR_AXIS[0]
    print(f"\n**Cumulative vs `{base}` ({order})** — the same axis read from the incumbent, "
          f"which is what locates the winner and the first loser.\n")
    print(f"| lane | K | C | removals over `{base}` | median (ms) | IQR | on-sign | verdict | "
          f"µs / removal |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    for lane in INTERIOR_AXIS[1:]:
        f, c = s["arms"][lane], cum[lane]
        rm = f["removals"] - s["arms"][base]["removals"]
        print(f"| `{lane}` | {f['admitted']} | {f['c']} | {rm} | **{c['med']:+.3f}** | "
              f"{c['lo']:+.3f} … {c['hi']:+.3f} | {c['on']}/{c['n']} | "
              f"**{VERDICT[c['verdict']]}** | {1000.0 * c['med'] / rm:+.2f} |")

    # THE HARD GATE (amendment A6). R5-session context follows it, and is context only.
    print(f"\n**Anchor band ({order})** — the R4-frozen ±2 % band, the HARD gate: a session "
          f"with an OUT anchor is INVALID, is repeated soaked, and emits no conclusion.\n")
    print("| anchor | this session | R4 frozen | delta | verdict |")
    print("| --- | --- | --- | --- | --- |")
    s["sanity"] = True
    for lane, target in zip(("control@256", "hot16@128"), ANCHORS[order]):
        got = s["med"][lane]
        rel = (got - target) / target
        ok = abs(rel) <= SANITY_TOL
        s["sanity"] = s["sanity"] and ok
        print(f"| `{lane}` | {got:.3f} | {target:.3f} | {100.0 * rel:+.2f} % | "
              f"**{'IN' if ok else 'OUT'}** |")
    print(f"\nR5-session context (REPORT-ONLY, amendment A6) — the R5 primary rotation's own "
          f"medians, for reading this session against the rung the interior extends; nothing "
          f"below gates on them.\n")
    print("| anchor | this session | R5 session | delta |")
    print("| --- | --- | --- | --- |")
    for lane, target in zip(("control@256", "hot16@128"), R5_SESSION[order]):
        got = s["med"][lane]
        print(f"| `{lane}` | {got:.3f} | {target:.3f} | {100.0 * (got - target) / target:+.2f} "
              f"% |")

    print(f"\n**Flank ({order})** — block medians of each anchor lane's FIRST and LAST full "
          f"cycle ({len(s['lanes'])} rounds each) against max({FLANK_MS:.2f} ms, "
          f"{100.0 * FLANK_REL:.1f} % of that lane's session median), amendment A6.\n")
    print("| anchor lane | first cycle | last cycle | drift | threshold | verdict |")
    print("| --- | --- | --- | --- | --- | --- |")
    s["flank"] = True
    for lane in INTERIOR_ANCHORS:
        first, last, drift, tol = interior_flank(s, lane)
        ok = drift <= tol
        s["flank"] = s["flank"] and ok
        print(f"| `{lane}` | {first:.3f} | {last:.3f} | {drift:.3f} | {tol:.3f} | "
              f"**{'PASS' if ok else 'TRIP'}** |")


def interior_decisions(s, selecting):
    """A1's decision bullets for one order. `selecting` is the LOCALITY session; the census
    one prints the same shape as DIAGNOSTIC context and alters nothing."""
    steps, cum, winner, loser = interior_shape(s)
    role = "SELECTION" if selecting else "diagnostic only — alters nothing (A1)"
    print(f"\n**`{s['order']}` — {role}**\n")
    pattern = " ".join("−" if c["med"] < 0 else "+" if c["med"] > 0 else "0"
                       for _, _, c in steps)
    verdicts = " ".join(VERDICT[c["verdict"]] for _, _, c in steps)
    print(f"- adjacent-step sign pattern, `{steps[0][0]} − {steps[0][1]}` first: `{pattern}` "
          f"({verdicts}) — reported verbatim; this is the monotonicity evidence.")
    if winner is None:
        print(f"- winner: **none** — no interior point wins over `{INTERIOR_AXIS[0]}` under "
              f"the signed rule, so the incumbent stands.")
    else:
        c, f = cum[winner], s["arms"][winner]
        print(f"- winner: **`{winner}`** (K = {f['admitted']}, C = {f['c']}) at "
              f"{c['med']:+.3f} ms vs `{INTERIOR_AXIS[0]}`, {c['on']}/{c['n']} on-sign — the "
              f"most negative cumulative median among the signed WINs, ties toward smaller K.")
    if loser is None:
        print(f"- first loser: **none** — no cumulative contrast is a signed LOSS through "
              f"`{INTERIOR_AXIS[-1]}`.")
    else:
        c, f = cum[loser], s["arms"][loser]
        print(f"- first loser: **`{loser}`** (K = {f['admitted']}, C = {f['c']}) at "
              f"{c['med']:+.3f} ms, {c['on']}/{c['n']} on-sign — the smallest K whose "
              f"cumulative contrast is a signed LOSS.")
    print(f"- the axis is RIGHT-CENSORED at `{INTERIOR_AXIS[-1]}`: K = "
          f"{s['arms'][INTERIOR_AXIS[-1]]['admitted']} is the largest measured point and no "
          f"claim is made past it.")
    return winner, loser


def interior_report(sessions):
    print("## v3 R8 — the admission-frontier interior (K17–23)\n")
    print(f"Every figure below is EMITTED, not transcribed: this script is the single "
          f"authority for the derived decisions, and each names the preregistered rule (plan "
          f"amendments A1/A5/A6/A7) it implements. The rung sweeps ONE contiguous admission "
          f"axis — `{INTERIOR_AXIS[0]}` through `{INTERIOR_AXIS[-1]}`, one BF source at refs 3 "
          f"per step — so it is decided by the eight adjacent steps and the eight cumulative "
          f"contrasts, paired per round on `eval + finalize`, under one signed rule "
          f"({INTERIOR['threshold']}/{INTERIOR['rounds']}). Curves are NEVER pooled across "
          f"term orders: the SELECTION runs on `locality` and census is diagnostic only.\n")
    for order in ("locality", "census"):
        interior_emit(sessions[order])

    print("\n### Preregistered decisions (A1)")
    invalid =[order for order in ("locality", "census") if not sessions[order]["sanity"]]
    tripped = [order for order in ("locality", "census") if not sessions[order]["flank"]]
    if invalid:
        print(f"> **SESSION INVALID (A6)** — an anchor outside the R4-frozen ±2 % band in: "
              f"{', '.join(invalid)}. The rule is a soaked repeat, and NO conclusion is emitted "
              f"from this session; the rows above and below are printed for diagnosis only and "
              f"DO NOT STAND.\n")
    if tripped:
        print(f"> **FLANK TRIPPED (A6)** — an anchor lane whose first and last full cycle "
              f"disagree past the scaled threshold in: {', '.join(tripped)}. That session is a "
              f"soaked-repeat candidate; the flank table above names the lane that drifted.\n")
    winner, loser = interior_decisions(sessions["locality"], True)
    interior_decisions(sessions["census"], False)

    print("\n### ncu capture manifest (A7)\n")
    print(f"Deduplicated {{`{INTERIOR_AXIS[0]}`, the locality winner, the locality first "
          f"loser, `{INTERIOR_AXIS[-1]}`}}, each under BOTH term orders (amendment A7). A7's "
          f"fallback {{`{INTERIOR_AXIS[0]}`, `k20@128`, `{INTERIOR_AXIS[-1]}`}} applies when "
          f"the sweep locates NEITHER a first loser nor a winner: with no signed decision on "
          f"the axis the mechanism question is about its middle, not about a boundary nothing "
          f"found. A winner without a first loser IS the decision, so it is profiled. Task 3 "
          f"consumes this block as AUTHORITATIVE and does not reconstruct it.\n")
    roles = defaultdict(set)
    roles[INTERIOR_AXIS[0]].add("incumbent")
    roles[INTERIOR_AXIS[-1]].add("censoring-endpoint")
    if loser is not None:
        roles[loser].add("first-loser")
    if winner is not None:
        roles[winner].add("winner")
    elif loser is None:
        roles["k20@128"].add("axis-midpoint")
    if invalid:
        print(f"**NOT AUTHORITATIVE**: {', '.join(invalid)} is invalid under A6, so this "
              f"session selects no capture set. Repeat the session soaked and re-emit.")
        sys.exit(f"{R8}: session invalid — {', '.join(invalid)} carries an anchor outside the "
                 f"R4-frozen ±2 % band (A6); repeat it soaked, and do not record conclusions "
                 f"from this log set")
    print("```")
    for lane in sorted(roles, key=lambda x: LANE_K[x]):
        print(f"NCU-CAPTURE lane={lane} orders=census,locality "
              f"roles={','.join(sorted(roles[lane]))}")
    print("```")


def interior(orders, runs, arms, done, sched, where, narrowed):
    if narrowed:
        sys.exit(f"{where}: the {R8} path is preregistered on BOTH term orders (A5), so "
                 f"`--order` cannot narrow it — emit the two session logs together")
    if set(orders) != {"census", "locality"}:
        sys.exit(f"{where}: the {R8} rung is preregistered on EXACTLY both term orders (census "
                 f"and locality); this log set carries {', '.join(orders) or 'none'} — a "
                 f"one-order log set decides nothing (A5)")
    sessions = {}
    for order in ("locality", "census"):
        key = (R8, order)
        sessions[order] = interior_session(key, runs[key], arms.get(key, {}), done.get(key),
                                          sched.get(key))
    interior_report(sessions)


# --- v3 R9 reorder emitter --------------------------------------------------------
#
# DEDICATED, on the R8 precedent, and REPORTING rather than adjudicating (RR): every number the
# rung asks for is computed and printed — the five rows under both term orders, the anchor lanes
# against every reference this repo holds, the flank readings, the build facts — and the emitter
# issues no verdict. Policy observations are collected as FLAGS and printed first, so nothing is
# hidden and nothing is decided here.


def rflag(flags, scope, tag, text):
    flags.append((scope, tag, text))


def rtier(pct):
    """How a carveout tier prints. `None` means the log's echoes did not agree on one, and the
    word carries the unit itself — a stray `%` after it reads as a number that is not there."""
    return f"{pct} %" if pct is not None else "non-uniform"


def rpaired(s, a, b):
    """The paired per-round contrast `a - b` on `eval + finalize`, with the rung's signed LABEL: at
    least 87 of 96 rounds on one side and the median agreeing is called WIN or LOSS, anything else
    WASH. A label, not a gate — nothing branches on it."""
    d = [x - y for x, y in zip(s["tot"][a], s["tot"][b])]
    verdict, med, on = signed(d, REORDER["threshold"])
    lo, hi = iqr(d)
    return {"med": med, "lo": lo, "hi": hi, "on": on, "n": len(d), "verdict": verdict,
            "min": min(d), "max": max(d)}


def reorder_carveout(files, order, flags, where):
    """The carveout block (Task 2's log grammar) as OBSERVATION. One log is one process, so the
    hinted set is a property of the FILE — the echoes precede every schedule line. Returns
    `(path, percent)`; the percent is read off the echoes, and every disagreement with the rung's
    premise (the three hinted symbols, uniform, agreeing with the set line) is flagged."""
    hits = sorted(p for p, e in files.items() if (R9, order) in e["sections"])
    if not hits:
        rflag(flags, order, "CARVEOUT-ATTRIBUTION",
              f"no log file declares a {R9} order={order} section, so there is no carveout block "
              f"to read — the L1 configuration these rows were taken at is unknown")
        return None, None
    if len(hits) > 1:
        # The timing is all computable; the only unattributable thing is which process's carveout
        # block describes these rows, and `hint = None` already renders that as **non-uniform**.
        rflag(flags, order, "CARVEOUT-ATTRIBUTION",
              f"{len(hits)} log files declare this section "
              f"({', '.join(os.path.basename(p) for p in hits)}) — one session is one process per "
              f"term order, so the carveout block read below is one of several and may not describe "
              f"these rows")
    path, env = hits[0], files[hits[0]]
    if len(env["sections"]) != 1:
        rflag(flags, order, "CARVEOUT-ATTRIBUTION",
              f"`{os.path.basename(path)}` declares "
              f"{sorted(f'{t}/{o}' for t, o in env['sections'])} — one log is one process, so the "
              f"carveout block below is shared between two term orders rather than attributable "
              f"to one")
    for n, line in env["loose"]:
        rflag(flags, order, "CARVEOUT-GRAMMAR",
              f"`{os.path.basename(path)}`:{n}: `{line}` is not the harness's carveout literal "
              f"(`  carveout hint       <pct>% (<symbol>)` / `  carveout symbols    <n> local "
              f"(<symbols>)`) — the L1 configuration this line describes is unread")
    got = [s for _, s in env["echoes"]]
    if got != REORDER_HINTED:
        rflag(flags, order, "CARVEOUT-SET",
              f"the applied echoes are {[f'{p}%:{s}' for p, s in env['echoes']]}; the rotation's "
              f"hinted set is {REORDER_HINTED} in that order — a missing, spurious, duplicated or "
              f"reordered echo means the bodies were not steered as the rung's premise assumes")
    pcts = sorted({p for p, _ in env["echoes"]})
    if len(pcts) > 1:
        rflag(flags, order, "CARVEOUT-UNIFORMITY",
              f"the hinted symbols are steered to {pcts} % — the rung's premise is ONE L1 "
              f"configuration for all three bodies (amendment A3), so these rows contrast bodies "
              f"across two configurations")
    if len(env["symbols"]) != 1:
        rflag(flags, order, "CARVEOUT-SETLINE",
              f"`{os.path.basename(path)}` carries {len(env['symbols'])} `carveout symbols` lines, "
              f"one expected — that line states the whole hinted set, and without exactly one a "
              f"MISSING symbol is indistinguishable from an unhinted one")
    else:
        count, names = env["symbols"][0]
        if names != REORDER_HINTED or count != len(REORDER_HINTED):
            rflag(flags, order, "CARVEOUT-SETLINE",
                  f"the set line says `{count} local ({', '.join(names)})` and the per-symbol "
                  f"echoes say {[s for _, s in env['echoes']]} — the two must describe one "
                  f"configuration")
    return path, (pcts[0] if len(pcts) == 1 else None)


def reorder_session(key, rounds, arms, trailer, sched, flags):
    """One term order's session. ERRORS only where no meaningful number can be computed: no ARM
    lines, no schedule, no trailer, no samples, an unknown lane, an incomplete round, a round set
    that is not the declared run, or rounds that do not form complete cycles. Everything else — the
    trace, the round shape, the header's own consistency, the rotation balance, the bodies, the
    plan, the admission order, the aliasing shape — is computed and FLAGGED."""
    order = key[1]
    if not arms:
        sys.exit(f"{R9}/{order}: no ARM lines for this order — old-format or truncated log")
    if trailer is None:
        sys.exit(f"{R9}/{order}: no `{R9} done order={order} …` trailer — the run did not finish, "
                 f"or the log is truncated")
    if sched is None:
        sys.exit(f"{R9}/{order}: ARM or SAMPLE rows with no `{R9} schedule` line")
    if not rounds:
        sys.exit(f"{R9}/{order}: the log declares this order ({sched[1]} rounds x {sched[0]} "
                 f"lanes) but carries no SAMPLE rows — there is nothing to summarize")
    lanes = list(arms)
    if set(lanes) != REORDER["lanes"]:
        missing = sorted(REORDER["lanes"] - set(lanes))
        extra = sorted(set(lanes) - REORDER["lanes"])
        sys.exit(f"{R9}/{order}: lane set is not the reorder rotation — missing {missing}, "
                 f"unexpected {extra}; an unknown lane has no row to be printed in")
    for r in sorted(rounds):
        if set(rounds[r]) != set(lanes):
            sys.exit(f"{R9}/{order}: round {r} carries {sorted(rounds[r])}, expected {lanes} — the "
                     f"contrasts are paired per round, so an incomplete round has no contrast")
    if len(rounds) != trailer[1]:
        sys.exit(f"{R9}/{order}: {len(rounds)} rounds in the log, trailer claims rounds="
                 f"{trailer[1]} — truncated log")
    if len(rounds) % len(lanes) != 0:
        sys.exit(f"{R9}/{order}: {len(rounds)} rounds over {len(lanes)} lanes is not a whole number "
                 f"of cycles — the rotation's own arithmetic does not close")
    want_ids = list(range(trailer[0], trailer[0] + trailer[1]))
    if sorted(rounds) != want_ids:
        got = sorted(rounds)
        sys.exit(f"{R9}/{order}: round ids are {got[:4]}…{got[-1]}, expected the consecutive run "
                 f"{want_ids[0]}…{want_ids[-1]} (warmup {trailer[0]}, rounds {trailer[1]}) — rounds "
                 f"are missing or renumbered, so the log does not describe the run it declares")

    # From here on: observations. Everything below computes.
    if len(lanes) != trailer[2] or len(lanes) != sched[0]:
        rflag(flags, order, "HEADER",
              f"the log carries {len(lanes)} ARM lines while the schedule declares "
              f"lanes={sched[0]} and the trailer lanes={trailer[2]} — the lane set is this "
              f"rotation's, so what disagrees is the header's own count")
    if (sched[1], sched[2]) != (trailer[1], trailer[0]):
        rflag(flags, order, "HEADER",
              f"the schedule line declares rounds={sched[1]} warmup={sched[2]} and the trailer "
              f"declares rounds={trailer[1]} warmup={trailer[0]} — the header does not describe "
              f"what ran")
    if (trailer[1], trailer[0]) != (REORDER["rounds"], REORDER["warmup"]):
        rflag(flags, order, "ROUND-SHAPE",
              f"the session ran {trailer[1]} rounds / {trailer[0]} warmup; the rung's shape is "
              f"{REORDER['rounds']} / {REORDER['warmup']}, which is what the "
              f"{REORDER['threshold']}/{REORDER['rounds']} sign label and the "
              f"{REORDER['warmup']}-round flank cycle are written for")
    for lane in lanes:
        want = REORDER_GRID[lane]
        if arms[lane]["grid"] != want:
            rflag(flags, order, "TRACE",
                  f"lane `{lane}` declares grid={arms[lane]['grid']}; at `--log-trace "
                  f"{REORDER_TRACE}` it is {want} — this session was recorded at another trace, "
                  f"which no other line in the log shows")
        if arms[lane]["kernel"] != REORDER_BODY[lane]:
            rflag(flags, order, "BODY",
                  f"lane `{lane}` declares body `{arms[lane]['kernel']}`; the rotation runs it on "
                  f"`{REORDER_BODY[lane]}` — the three cached lanes share one plan, so the body "
                  f"field is the only thing that says which body ran")
    # ONE flag per lane, not per round: a lane whose every sample names another body would otherwise
    # print 96 identical rows and drown the block, which is the only protection this rung has.
    forged = {}
    for r in sorted(rounds):
        for lane, (_, _, kernel) in rounds[r].items():
            if kernel != arms[lane]["kernel"] and lane not in forged:
                forged[lane] = (r, kernel, 0)
            if kernel != arms[lane]["kernel"]:
                first, k, n = forged[lane]
                forged[lane] = (first, k, n + 1)
    for lane, (first, kernel, n) in forged.items():
        rflag(flags, order, "SAMPLE-BODY",
              f"lane `{lane}` names `{kernel}` in {n} of {len(rounds)} rounds (first at round "
              f"{first}) but its ARM line declares `{arms[lane]['kernel']}`")
    per = len(rounds) // len(lanes)
    slots = defaultdict(int)
    for r in sorted(rounds):
        for slot, lane in enumerate(rounds[r]):
            slots[(lane, slot)] += 1
    for lane in lanes:
        off = [slot for slot in range(len(lanes)) if slots[(lane, slot)] != per]
        if off:
            rflag(flags, order, "ROTATION-BALANCE",
                  f"lane `{lane}` does not take rotation positions {off} exactly {per} times — a "
                  f"lane that keeps a position carries that position's clock state into its median")
            break
    keys = sorted(rounds)
    for lane in lanes:
        f = arms[lane]
        ids, k = f["ids"], f["admitted"]
        if len(ids) != k:
            rflag(flags, order, "ADMISSION",
                  f"lane `{lane}` declares {k} admitted sources but lists {len(ids)} ids")
        if REORDER_K[lane] != k:
            rflag(flags, order, "LANE-LABEL",
                  f"lane `{lane}` admits {k} sources and its name claims K = {REORDER_K[lane]}")
        want = ORACLE_ORDER[:k]
        if ids != want:
            at = next((i for i, (g, w) in enumerate(zip(ids, want)) if g != w), None)
            where_at = (f"at admission position {at}: {ids[at]} where the oracle has {want[at]}"
                        if at is not None else "in its length")
            rflag(flags, order, "ADMISSION",
                  f"lane `{lane}`'s admitted prefix is not the canonical one — {where_at} (no "
                  f"count can see this)")
    base = arms[R9_INCUMBENT]
    for lane in REORDER_ONE_PLAN[1:]:
        keyed = ("c", "removals", "admitted", "ids", "threads")
        if tuple(arms[lane][k] for k in keyed) != tuple(base[k] for k in keyed):
            rflag(flags, order, "PLAN",
                  f"lane `{lane}` declares C={arms[lane]['c']} removals={arms[lane]['removals']} "
                  f"admitted={arms[lane]['admitted']} at {arms[lane]['threads']} threads and "
                  f"`{R9_INCUMBENT}` declares {base['c']} / {base['removals']} / "
                  f"{base['admitted']} at {base['threads']} — the headline row reads as a BODY "
                  f"contrast only while the plan is one plan")
    for i, a in enumerate(lanes):
        for b in lanes[i + 1:]:
            if (arms[a]["ids"], arms[a]["threads"], arms[a]["kernel"]) == \
               (arms[b]["ids"], arms[b]["threads"], arms[b]["kernel"]) and arms[a]["removals"]:
                rflag(flags, order, "ALIAS",
                      f"lanes `{a}` and `{b}` declare the same plan on the same body at the same "
                      f"block size — one experiment under two labels")
            if all(rounds[r][a][:2] == rounds[r][b][:2] for r in keys):
                rflag(flags, order, "ALIAS",
                      f"lanes `{a}` and `{b}` carry BIT-IDENTICAL samples in every round — one "
                      f"lane's data appears under two labels")
    tot = {a: [rounds[r][a][0] + rounds[r][a][1] for r in keys] for a in lanes}
    return {
        "order": order, "lanes": lanes, "arms": arms, "rounds": rounds, "keys": keys, "tot": tot,
        "med": {a: median(tot[a]) for a in lanes},
        "med_ev": {a: median(rounds[r][a][0] for r in keys) for a in lanes},
        "med_fin": {a: median(rounds[r][a][1] for r in keys) for a in lanes},
    }


def reorder_flank(s, lane):
    """The first and last full cycle's block medians for one anchor lane, with the scaled reading
    that goes with it: max(0.05 ms, 0.5 % of that lane's session median)."""
    cycle = len(s["lanes"])
    first = median(s["tot"][lane][:cycle])
    last = median(s["tot"][lane][-cycle:])
    return first, last, abs(last - first), max(FLANK_MS, FLANK_REL * s["med"][lane])


def reorder_readings(s, flags):
    """The anchor-reference deltas and the flank readings, computed before anything prints so the
    flags block can lead the output."""
    order = s["order"]
    s["refs"] = {}
    for i, lane in enumerate(REORDER_ANCHOR_LANES):
        got, tells = s["med"][lane], []
        for name, lanes_n, table in REORDER_REFERENCES:
            if order not in table:
                continue
            ref = table[order][i]
            rel = (got - ref) / ref
            s["refs"].setdefault(lane, []).append((name, lanes_n, ref, rel))
            if abs(rel) > R9_OFFSET_TELL:
                tells.append(f"{name} ({lanes_n} lanes) {100.0 * rel:+.2f} %")
        if tells:
            # The span is read off the reference table itself, so the prose cannot drift from the
            # lane counts the rows print.
            span = sorted({n for _, n, _ in REORDER_REFERENCES})
            rflag(flags, order, "ANCHOR",
                  f"`{lane}` reads {got:.3f} ms, more than "
                  f"{100.0 * R9_OFFSET_TELL:.1f} % off " + "; ".join(tells)
                  + f" — this rotation carries {len(s['lanes'])} lanes against their "
                    f"{span[0]}–{span[-1]}, so read the reference table before calling it machine "
                    f"drift")
    s["flank"] = {}
    for lane in REORDER_FLANK_LANES:
        first, last, drift, tol = reorder_flank(s, lane)
        s["flank"][lane] = (first, last, drift, tol)
        if drift > tol:
            rflag(flags, order, "FLANK",
                  f"`{lane}`'s first and last full cycle differ by {drift:.3f} ms against the "
                  f"{tol:.3f} ms scaled reading — the session moved under itself")


def reorder_emit(s):
    order = s["order"]
    print(f"\n### `{R9}` — `--term-order {order}`, {len(s['keys'])} paired rounds, "
          f"{len(s['lanes'])} lanes\n")
    print("| lane | body | regs | blocks/SM | threads | grid | C | removals | admitted | "
          "median `eval` | median `finalize` | median `eval+fin` |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    for a in s["lanes"]:
        f = s["arms"][a]
        print(f"| `{a}` | `{f['kernel']}` | {f['regs']} | {f['blocks_sm']} | {f['threads']} | "
              f"{f['grid']} | {f['c']} | {f['removals']} | {f['admitted']} | "
              f"{s['med_ev'][a]:.3f} | {s['med_fin'][a]:.3f} | **{s['med'][a]:.3f}** |")
    print(f"\nBodies, admitted prefixes, grids and the one-plan-three-bodies premise are all "
          f"checked and reported in the flags block above; nothing here is filtered out on their "
          f"account. Sign label at this rotation: {REORDER['threshold']}/{REORDER['rounds']}.")

    print(f"\n**Rows ({order})** — paired per round on `eval + finalize`, each naming its baseline. "
          f"WIN / LOSS / WASH are LABELS at "
          f"{REORDER['threshold']}/{REORDER['rounds']}; the reading is the median, the sign count "
          f"and the spread.\n")
    print("| # | contrast | baseline | median (ms) | IQR | min … max | % of baseline | on-sign | "
          "label | occupancy | what it isolates |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    for i, (a, b, what) in enumerate(REORDER_ROWS, 1):
        c = rpaired(s, a, b)
        occ = "same class" if s["arms"][a]["blocks_sm"] == s["arms"][b]["blocks_sm"] else \
              f"**{s['arms'][a]['blocks_sm']} v {s['arms'][b]['blocks_sm']} blocks/SM — NOT " \
              f"occupancy-neutral**"
        print(f"| {i} | `{a}` − `{b}` | `{b}` | **{c['med']:+.3f}** | {c['lo']:+.3f} … "
              f"{c['hi']:+.3f} | {c['min']:+.3f} … {c['max']:+.3f} | "
              f"{100.0 * c['med'] / s['med'][b]:+.2f} % | {c['on']}/{c['n']} | "
              f"**{VERDICT[c['verdict']]}** | {occ} | {what} |")

    print(f"\n**Anchor lanes against every reference we hold ({order})** — absolute medians are "
          f"rotation-composition dependent, so each reference carries the LANE COUNT of the "
          f"rotation that produced it against this rung's {len(s['lanes'])}. Nothing here gates; "
          f"the flags block calls out a delta past {100.0 * R9_OFFSET_TELL:.1f} %.\n")
    print("| anchor lane | this session (6 lanes) | reference | lanes | reference median | delta |")
    print("| --- | --- | --- | --- | --- | --- |")
    for lane in REORDER_ANCHOR_LANES:
        for name, lanes_n, ref, rel in s["refs"].get(lane, []):
            print(f"| `{lane}` | {s['med'][lane]:.3f} | {name} | {lanes_n} | {ref:.3f} | "
                  f"{100.0 * rel:+.2f} % |")

    print(f"\n**Flank ({order})** — block medians of each INCUMBENT-body anchor lane's FIRST and "
          f"LAST full cycle ({len(s['lanes'])} rounds each), against max({FLANK_MS:.2f} ms, "
          f"{100.0 * FLANK_REL:.1f} % of that lane's session median). The bodies under test are not "
          f"their own drift sentinels. A reading, not a mandate.\n")
    print("| anchor lane | first cycle | last cycle | drift | scaled reading | over? |")
    print("| --- | --- | --- | --- | --- | --- |")
    for lane in REORDER_FLANK_LANES:
        first, last, drift, tol = s["flank"][lane]
        print(f"| `{lane}` | {first:.3f} | {last:.3f} | {drift:.3f} | {tol:.3f} | "
              f"{'**yes**' if drift > tol else 'no'} |")


def reorder_flags_block(flags):
    print("\n### Flags\n")
    if not flags:
        print("**None.** Every observation below matched the rung's own description of itself — "
              "the trace, the round shape, the rotation balance, the bodies, the plan, the "
              "admitted prefixes, the carveout set and its uniformity, the anchor references and "
              "the flank. The tables are the reading.")
        return
    print(f"{len(flags)} observation(s). **Nothing here stops the emitter or decides anything** — "
          f"each row is printed first so it cannot be missed, and every judgement it invites (is "
          f"this offset composition or drift? does this shape still answer the question?) is RR's "
          f"on the whole picture below.\n")
    print("| # | scope | flag | what was observed |")
    print("| --- | --- | --- | --- |")
    for i, (scope, tag, text) in enumerate(flags, 1):
        print(f"| {i} | `{scope}` | **{tag}** | {text} |")


def reorder_report(sessions, paths, flags):
    orders = ("locality", "census")
    hints = {o: sessions[o]["hint"] for o in orders}
    print("## v3 R9 — the gate-first reordered pair body\n")
    print(f"Every figure below is EMITTED, not transcribed. The rung contrasts BODIES at one plan — "
          f"the incumbent, the bounded gate-first body and the unbounded one, all three at hot16's "
          f"admitted set — under both term orders, paired per round on `eval + finalize`. This "
          f"emitter REPORTS: it computes the whole picture, flags what disagrees with the rung's "
          f"own description of itself, and issues NO verdict. Rows are never pooled across term "
          f"orders.\n")
    print("| term order | log | carveout applied (read off the log) | hinted symbols |")
    print("| --- | --- | --- | --- |")
    for order in orders:
        pct = hints[order]
        print(f"| `{order}` | `{os.path.basename(paths[order])}` | "
              f"**{rtier(pct)}** | "
              + ", ".join(f"`{sym}`" for sym in REORDER_HINTED) + " |")
    reorder_flags_block(flags)
    for order in orders:
        reorder_emit(sessions[order])

    print("\n### The whole picture, in one place\n")
    # This is the block a record is most likely to quote, so it restates the flag COUNT: the flags
    # block above is unmissable top-to-bottom and invisible to an excerpt.
    print(f"**{len(flags)} flag(s) above; this table is not a verdict.**"
          + ("" if flags else " Nothing disagreed with the rung's own description of itself.")
          + "\n")
    headline = {o: rpaired(sessions[o], R9_BOUNDED, R9_INCUMBENT) for o in orders}
    print(f"**Row 1, the headline contrast** (`{R9_BOUNDED}` − `{R9_INCUMBENT}`), both orders side "
          f"by side. No gate: the medians, the sign counts and the spreads are the reading.\n")
    print("| order | median (ms) | IQR | min … max | on-sign | label | carveout |")
    print("| --- | --- | --- | --- | --- | --- | --- |")
    for o in orders:
        c = headline[o]
        pct = hints[o]
        print(f"| `{o}` | **{c['med']:+.3f}** | {c['lo']:+.3f} … {c['hi']:+.3f} | "
              f"{c['min']:+.3f} … {c['max']:+.3f} | {c['on']}/{c['n']} | "
              f"**{VERDICT[c['verdict']]}** | {rtier(pct)} |")

    # THE BUILD FACTS, off the ARM lines rather than written here. Their cross-order comparison is
    # computed before the flags block prints (see `reorder`), so a disagreement is already up there.
    a_loc = sessions["locality"]["arms"]
    regs = {lane: a_loc[lane]["regs"] for lane in REORDER_LANES}
    blocks = {lane: a_loc[lane]["blocks_sm"] for lane in REORDER_LANES}
    print(f"\n**Build facts** (off the ARM lines): `{R9_INCUMBENT}` {regs[R9_INCUMBENT]} regs / "
          f"{blocks[R9_INCUMBENT]} blocks/SM, `{R9_BOUNDED}` {regs[R9_BOUNDED]} / "
          f"{blocks[R9_BOUNDED]}, `{R9_FREE}` {regs[R9_FREE]} / {blocks[R9_FREE]}. Carveout "
          f"{rtier(hints['locality'])} on all three hinted symbols. Any disagreement between "
          f"the two orders' logs is in the flags block.")

    cut = regs[R9_BOUNDED] < regs[R9_INCUMBENT]
    print(f"\n**Reference: what each combination would mean** — a labelled reading of the rung's "
          f"two axes, NOT a selection. The register facts are static (above); the timing is row 1 "
          f"(above, both orders). Which cell this session sits in, and what to do about it, is "
          f"RR's call.\n")
    print("| registers vs the incumbent | row 1 | what it would mean |")
    print("| --- | --- | --- |")
    print("| reduced | wash or win | a register cut that costs no time — the R10 headroom case |")
    print("| reduced | loss | a register cut paid for in time |")
    print("| unchanged | win | a performance win with no register headroom |")
    print("| unchanged | wash or loss | neither a register cut nor a time win |")
    print(f"\nThis session's register axis, stated: `{R9_BOUNDED}` is "
          f"{'BELOW' if cut else 'NOT below'} `{R9_INCUMBENT}` "
          f"({regs[R9_BOUNDED]} vs {regs[R9_INCUMBENT]} registers), and `{R9_FREE}` runs "
          f"{regs[R9_FREE]} registers at {blocks[R9_FREE]} blocks/SM.")

    print("\n### ncu capture set\n")
    print(f"A FIXED set — the incumbent and the two gate-first bodies — under BOTH term orders. The "
          f"three lanes of interest are the rung's whole question, so no timing outcome and no "
          f"selection rule decides it.\n")
    print("```")
    for lane, role in REORDER_CAPTURE:
        pct = hints["locality"]
        print(f"NCU-CAPTURE lane={lane} orders=census,locality roles={role} "
              f"body={REORDER_BODY[lane]} regs={regs[lane]} "
              f"carveout={pct if pct is not None else 'non-uniform'}")
    print("```")
    # Restated at the foot as well as in the leading block: a cross-order disagreement is the one
    # observation that invalidates reading the two orders as one session, and it is worth twice.
    late = [f for f in flags if f[0] == "session"]
    if late:
        print("\n**Session-level flags** (restated from the flags block — they are what makes "
              "reading the two orders together a question):\n")
        for _, tag, text in late:
            print(f"- **{tag}** — {text}")


def reorder(orders, runs, arms, done, sched, files, where, narrowed):
    if narrowed:
        sys.exit(f"{where}: the {R9} rung is read over BOTH term orders, so `--order` cannot narrow "
                 f"it — emit the two session logs together")
    if set(orders) != {"census", "locality"}:
        sys.exit(f"{where}: the {R9} rung is read over EXACTLY both term orders (census and "
                 f"locality); this log set carries {', '.join(orders) or 'none'} — the missing "
                 f"order's rows cannot be computed")
    flags, sessions, paths = [], {}, {}
    for order in ("locality", "census"):
        key = (R9, order)
        paths[order], hint = reorder_carveout(files, order, flags, where)
        sessions[order] = reorder_session(key, runs[key], arms.get(key, {}), done.get(key),
                                         sched.get(key), flags)
        sessions[order]["hint"] = hint
        reorder_readings(sessions[order], flags)
    # The cross-order observations are appended by `reorder_report` while it reads the two orders
    # together; it prints the flags block from the same list, so nothing lands after the fact
    # unseen — the block is assembled first and the late rows are restated at the end.
    cross = []
    a_loc, a_cen = (sessions[o]["arms"] for o in ("locality", "census"))
    keyed = ("regs", "blocks_sm", "threads", "grid", "kernel", "c", "removals", "admitted", "ids")
    for lane in REORDER_LANES:
        if tuple(a_loc[lane][k] for k in keyed) != tuple(a_cen[lane][k] for k in keyed):
            rflag(cross, "session", "BUILD-FACTS",
                  f"lane `{lane}` declares different facts in the two orders' logs (registers, "
                  f"occupancy tier, body or plan) — those are facts of the BUILD, so these two "
                  f"logs describe two builds and their rows are not one session")
    if sessions["locality"]["hint"] != sessions["census"]["hint"]:
        rflag(cross, "session", "CARVEOUT-TIER",
              f"the two orders were recorded at {rtier(sessions['locality']['hint'])} and "
              f"{rtier(sessions['census']['hint'])} — the rung's premise is one L1 configuration, "
              f"so these are two experiments")
    flags.extend(cross)
    reorder_report(sessions, paths, flags)


def r9b_paired(s, a, b):
    """The paired per-round contrast `a - b` on `eval + finalize`, with this rung's signed LABEL: at
    least 87 of 96 rounds on one side and the median agreeing is called WIN or LOSS, anything else
    WASH. A label, not a gate — nothing branches on it."""
    d = [x - y for x, y in zip(s["tot"][a], s["tot"][b])]
    verdict, med, on = signed(d, R9B_THRESHOLD)
    lo, hi = iqr(d)
    return {"med": med, "lo": lo, "hi": hi, "on": on, "n": len(d), "verdict": verdict,
            "min": min(d), "max": max(d)}


def r9b_scan(path):
    """The pre-scan that routes a log set here, and the ONLY thing that can tell the two R9b
    rotations apart: the rotation keywords a file declares and the lane labels its ARM lines name.
    An unreadable file returns nothing, so the shared parser raises on it exactly as it always
    has."""
    tags, labels = set(), set()
    try:
        with open(path) as fh:
            for raw in fh:
                line = raw.strip()
                m = SCHED.match(line) or DONE.match(line)
                if m and m.group(1) in KNOWN:
                    tags.add(m.group(1))
                    continue
                m = ARM_IDS.match(line) or ARM.match(line)
                if m:
                    labels.add(m.group(1))
    except OSError:
        return set(), set()
    return tags, labels


def r9b_shape_of(labels):
    for name, shape in R9B_SHAPES.items():
        if labels == set(shape["lanes"]):
            return name
    return None


def r9b_split(paths, where):
    """Group a log set into SESSIONS by lane label set. The tag cannot do it — both rotations print
    `R9B schedule … lanes=8` — so a file that names neither rotation's lanes, or that declares an
    R9b section without ARM lines, has no session to be read in and no row to be printed in."""
    groups = defaultdict(list)
    for path in paths:
        tags, labels = r9b_scan(path)
        base = os.path.basename(path)
        if tags - {R9B}:
            sys.exit(f"{where}: `{base}` declares {sorted(tags - {R9B})} beside {R9B} — each "
                     f"rotation is summarized under its own rules; emit them separately")
        if R9B not in tags:
            sys.exit(f"{where}: `{base}` declares no {R9B} section while the rest of the set does — "
                     f"emit one rung at a time")
        name = r9b_shape_of(labels)
        if name is None:
            detail = "; ".join(
                f"{s} is missing {sorted(set(R9B_SHAPES[s]['lanes']) - labels)} and does not name "
                f"{sorted(labels - set(R9B_SHAPES[s]['lanes']))}" for s in R9B_SHAPES)
            sys.exit(f"{where}: `{base}` names lanes {sorted(labels) or 'none'}, which is neither "
                     f"R9b rotation ({detail}) — the two rotations share the tag {R9B}, so the lane "
                     f"SET is the only thing that says which one a log is")
        groups[name].append(path)
    return groups


def r9b_carveout(files, name, order, flags, where):
    """The carveout block as OBSERVATION, per SHAPE: one log is one process, so the hinted set is a
    property of the FILE (the echoes precede every schedule line). Returns `(path, percent)`. The
    expected set is this rotation's own HINTED order, which is NOT its lane order — the CLASS
    rotation echoes `cd` before `b`."""
    scope, want = f"{name}/{order}", R9B_SHAPES[name]["hinted"]
    hits = sorted(p for p, e in files.items() if (R9B, order) in e["sections"])
    if not hits:
        rflag(flags, scope, "CARVEOUT-ATTRIBUTION",
              f"no log file declares a {R9B} order={order} section for this rotation, so there is "
              f"no carveout block to read — the L1 configuration these rows were taken at is "
              f"unknown")
        return None, None
    if len(hits) > 1:
        rflag(flags, scope, "CARVEOUT-ATTRIBUTION",
              f"{len(hits)} log files declare this section "
              f"({', '.join(os.path.basename(p) for p in hits)}) — one session is one process per "
              f"term order, so the carveout block read below is one of several and may not describe "
              f"these rows")
    path, env = hits[0], files[hits[0]]
    if len(env["sections"]) != 1:
        rflag(flags, scope, "CARVEOUT-ATTRIBUTION",
              f"`{os.path.basename(path)}` declares "
              f"{sorted(f'{t}/{o}' for t, o in env['sections'])} — one log is one process, so the "
              f"carveout block below is shared between two term orders rather than attributable "
              f"to one")
    for n, line in env["loose"]:
        rflag(flags, scope, "CARVEOUT-GRAMMAR",
              f"`{os.path.basename(path)}`:{n}: `{line}` is not the harness's carveout literal "
              f"(`  carveout hint       <pct>% (<symbol>)` / `  carveout symbols    <n> local "
              f"(<symbols>)`) — the L1 configuration this line describes is unread")
    got = [s for _, s in env["echoes"]]
    if got != want:
        rflag(flags, scope, "CARVEOUT-SET",
              f"the applied echoes are {[f'{p}%:{s}' for p, s in env['echoes']]}; the "
              f"`{R9B_SHAPES[name]['flag']}` rotation's hinted set is {want} IN THAT ORDER, which is "
              f"the harness's HINTED order and not its lane order — a missing, spurious, duplicated "
              f"or reordered echo means the cells were not steered as these rows assume")
    pcts = sorted({p for p, _ in env["echoes"]})
    if len(pcts) > 1:
        rflag(flags, scope, "CARVEOUT-UNIFORMITY",
              f"the hinted symbols are steered to {pcts} % — every row below contrasts cells at ONE "
              f"L1 configuration, so these rows span two configurations")
    if len(env["symbols"]) != 1:
        rflag(flags, scope, "CARVEOUT-SETLINE",
              f"`{os.path.basename(path)}` carries {len(env['symbols'])} `carveout symbols` lines, "
              f"one expected — that line states the whole hinted set, and without exactly one a "
              f"MISSING symbol is indistinguishable from an unhinted one")
    else:
        count, names = env["symbols"][0]
        if names != want or count != len(want):
            rflag(flags, scope, "CARVEOUT-SETLINE",
                  f"the set line says `{count} local ({', '.join(names)})` and the per-symbol "
                  f"echoes say {[s for _, s in env['echoes']]} — the two must describe one "
                  f"configuration")
    return path, (pcts[0] if len(pcts) == 1 else None)


def r9b_session(name, key, rounds, arms, trailer, sched, flags):
    """One term order of one rotation. ERRORS only where no meaningful number can be computed: no
    ARM lines, no schedule, no trailer, no samples, a lane the rotation does not name, an incomplete
    round, a round set that is not the declared run, or rounds that do not form complete cycles.
    Everything else — the trace, the round shape, the header's own consistency, the rotation balance,
    the bodies, the budgets, the plan, the admission order, the aliasing shape — is computed and
    FLAGGED."""
    order, lanes_want = key[1], R9B_SHAPES[name]["lanes"]
    scope = f"{name}/{order}"
    if not arms:
        sys.exit(f"{R9B}/{name}/{order}: no ARM lines for this order — old-format or truncated log")
    if trailer is None:
        sys.exit(f"{R9B}/{name}/{order}: no `{R9B} done order={order} …` trailer — the run did not "
                 f"finish, or the log is truncated")
    if sched is None:
        sys.exit(f"{R9B}/{name}/{order}: ARM or SAMPLE rows with no `{R9B} schedule` line")
    if not rounds:
        sys.exit(f"{R9B}/{name}/{order}: the log declares this order ({sched[1]} rounds x "
                 f"{sched[0]} lanes) but carries no SAMPLE rows — there is nothing to summarize")
    lanes = list(arms)
    if set(lanes) != set(lanes_want):
        missing = sorted(set(lanes_want) - set(lanes))
        extra = sorted(set(lanes) - set(lanes_want))
        sys.exit(f"{R9B}/{name}/{order}: lane set is not the {R9B_SHAPES[name]['flag']} rotation — "
                 f"missing {missing}, unexpected {extra}; an unknown lane has no row to be printed "
                 f"in")
    for r in sorted(rounds):
        if set(rounds[r]) != set(lanes):
            sys.exit(f"{R9B}/{name}/{order}: round {r} carries {sorted(rounds[r])}, expected "
                     f"{lanes} — the contrasts are paired per round, so an incomplete round has no "
                     f"contrast")
    if len(rounds) != trailer[1]:
        sys.exit(f"{R9B}/{name}/{order}: {len(rounds)} rounds in the log, trailer claims rounds="
                 f"{trailer[1]} — truncated log")
    if len(rounds) % len(lanes) != 0:
        sys.exit(f"{R9B}/{name}/{order}: {len(rounds)} rounds over {len(lanes)} lanes is not a whole "
                 f"number of cycles — the rotation's own arithmetic does not close")
    want_ids = list(range(trailer[0], trailer[0] + trailer[1]))
    if sorted(rounds) != want_ids:
        got = sorted(rounds)
        sys.exit(f"{R9B}/{name}/{order}: round ids are {got[:4]}…{got[-1]}, expected the "
                 f"consecutive run {want_ids[0]}…{want_ids[-1]} (warmup {trailer[0]}, rounds "
                 f"{trailer[1]}) — rounds are missing or renumbered, so the log does not describe "
                 f"the run it declares")

    # From here on: observations. Everything below computes.
    if len(lanes) != trailer[2] or len(lanes) != sched[0]:
        rflag(flags, scope, "HEADER",
              f"the log carries {len(lanes)} ARM lines while the schedule declares "
              f"lanes={sched[0]} and the trailer lanes={trailer[2]} — the lane set is this "
              f"rotation's, so what disagrees is the header's own count")
    if (sched[1], sched[2]) != (trailer[1], trailer[0]):
        rflag(flags, scope, "HEADER",
              f"the schedule line declares rounds={sched[1]} warmup={sched[2]} and the trailer "
              f"declares rounds={trailer[1]} warmup={trailer[0]} — the header does not describe "
              f"what ran")
    if (trailer[1], trailer[0]) != (R9B_ROUNDS, R9B_WARMUP):
        rflag(flags, scope, "ROUND-SHAPE",
              f"the session ran {trailer[1]} rounds / {trailer[0]} warmup; the rung's shape is "
              f"{R9B_ROUNDS} / {R9B_WARMUP}, which is what the {R9B_THRESHOLD}/{R9B_ROUNDS} sign "
              f"label and the {len(lanes)}-round flank cycle are written for")
    for lane in lanes:
        body, budget, kernel = R9B_CELL[lane]
        if arms[lane]["grid"] != R9B_GRID[lane]:
            rflag(flags, scope, "TRACE",
                  f"lane `{lane}` declares grid={arms[lane]['grid']}; at `--log-trace "
                  f"{R9B_TRACE}` it is {R9B_GRID[lane]} — this session was recorded at another "
                  f"trace, which no other line in the log shows")
        got = arms[lane]["kernel"]
        if got == kernel:
            continue
        # A cell is a (body, budget) pair and the kernel is the only field that carries it, so an
        # observed symbol is named as the CELL it is: same body at another budget is a budget swap,
        # anything else a body swap.
        seen = R9B_BY_KERNEL.get(got)
        if seen and seen[1] == body:
            rflag(flags, scope, "BUDGET",
                  f"lane `{lane}` runs body {body} at budget {budget} in this rotation but declares "
                  f"`{got}`, which is {body} at {seen[2]} — the register budget is not monotone "
                  f"(`(128,6)` is the maximum-register cell), so a swapped budget cannot be read "
                  f"off any other field")
        else:
            named = f"{seen[1]} at {seen[2]} (`{seen[0]}`'s cell)" if seen else "no cell of this grid"
            rflag(flags, scope, "BODY",
                  f"lane `{lane}` declares body `{got}` = {named}; the rotation runs it on "
                  f"`{kernel}` = {body} at {budget} — every cached lane shares one plan, so the "
                  f"kernel field is the only thing that says which cell ran")
    # ONE flag per lane, not per round: a lane whose every sample named another cell would otherwise
    # print 96 identical rows and drown the block, which is the only protection this rung has.
    forged = {}
    for r in sorted(rounds):
        for lane, (_, _, kernel) in rounds[r].items():
            if kernel != arms[lane]["kernel"]:
                first, k, n = forged.get(lane, (r, kernel, 0))
                forged[lane] = (first, k, n + 1)
    for lane, (first, kernel, n) in forged.items():
        rflag(flags, scope, "SAMPLE-BODY",
              f"lane `{lane}` names `{kernel}` in {n} of {len(rounds)} rounds (first at round "
              f"{first}) but its ARM line declares `{arms[lane]['kernel']}`")
    per = len(rounds) // len(lanes)
    slots = defaultdict(int)
    for r in sorted(rounds):
        for slot, lane in enumerate(rounds[r]):
            slots[(lane, slot)] += 1
    for lane in lanes:
        off = [slot for slot in range(len(lanes)) if slots[(lane, slot)] != per]
        if off:
            rflag(flags, scope, "ROTATION-BALANCE",
                  f"lane `{lane}` does not take rotation positions {off} exactly {per} times — a "
                  f"lane that keeps a position carries that position's clock state into its median")
            break
    keys = sorted(rounds)
    for lane in lanes:
        f = arms[lane]
        ids, k = f["ids"], f["admitted"]
        if len(ids) != k:
            rflag(flags, scope, "ADMISSION",
                  f"lane `{lane}` declares {k} admitted sources but lists {len(ids)} ids")
        if R9B_K[lane] != k:
            rflag(flags, scope, "LANE-LABEL",
                  f"lane `{lane}` admits {k} sources and its name claims K = {R9B_K[lane]}")
        want = ORACLE_ORDER[:k]
        if ids != want:
            at = next((i for i, (g, w) in enumerate(zip(ids, want)) if g != w), None)
            where_at = (f"at admission position {at}: {ids[at]} where the oracle has {want[at]}"
                        if at is not None else "in its length")
            rflag(flags, scope, "ADMISSION",
                  f"lane `{lane}`'s admitted prefix is not the canonical one — {where_at} (no "
                  f"count can see this)")
    base = arms[R9B_INC]
    for lane in R9B_ONE_PLAN[name]:
        if lane == R9B_INC:
            continue
        keyed = ("c", "removals", "admitted", "ids", "threads")
        if tuple(arms[lane][k] for k in keyed) != tuple(base[k] for k in keyed):
            rflag(flags, scope, "PLAN",
                  f"lane `{lane}` declares C={arms[lane]['c']} removals={arms[lane]['removals']} "
                  f"admitted={arms[lane]['admitted']} at {arms[lane]['threads']} threads and "
                  f"`{R9B_INC}` declares {base['c']} / {base['removals']} / {base['admitted']} at "
                  f"{base['threads']} — every row reads as a CELL contrast only while the plan is "
                  f"one plan")
    # The aliasing key carries the BUDGET as well as the body: this rotation puts one body on three
    # budgets, so `(plan, block size, body)` alone would call three legitimate cells one experiment.
    # The budget rides the kernel name, so the extra field states the axis rather than adding
    # information — and it is the axis a future cell could collide on.
    for i, a in enumerate(lanes):
        for b in lanes[i + 1:]:
            keyed = [(arms[x]["ids"], arms[x]["threads"], arms[x]["kernel"], R9B_CELL[x][1])
                     for x in (a, b)]
            if keyed[0] == keyed[1] and arms[a]["removals"]:
                rflag(flags, scope, "ALIAS",
                      f"lanes `{a}` and `{b}` declare the same plan on the same body at the same "
                      f"budget and block size — one experiment under two labels")
            if all(rounds[r][a][:2] == rounds[r][b][:2] for r in keys):
                rflag(flags, scope, "ALIAS",
                      f"lanes `{a}` and `{b}` carry BIT-IDENTICAL samples in every round — one "
                      f"lane's data appears under two labels")
    tot = {a: [rounds[r][a][0] + rounds[r][a][1] for r in keys] for a in lanes}
    return {
        "shape": name, "order": order, "lanes": lanes, "arms": arms, "rounds": rounds, "keys": keys,
        "tot": tot, "scope": scope,
        "med": {a: median(tot[a]) for a in lanes},
        "med_ev": {a: median(rounds[r][a][0] for r in keys) for a in lanes},
        "med_fin": {a: median(rounds[r][a][1] for r in keys) for a in lanes},
    }


def r9b_readings(s, flags):
    """The anchor-reference deltas and the flank readings, computed before anything prints so the
    flags block can lead the output.

    THE FLAG KEYS TO THE CAMPAIGN BASELINE AND TO NOTHING ELSE — to this session's OWN rotation's row
    of it, on a device whose identity is recorded. The pre-provenance references are computed and
    printed beside it and can never raise a flag: they disagree with each other by more than the
    reporting threshold, so a flag keyed to them reports their disagreement rather than the
    session."""
    scope, order, name = s["scope"], s["order"], s["shape"]
    s["base"], s["spread"], s["pre"] = {}, {}, {}
    other = next(n for n in R9B_SHAPES if n != name)
    for i, lane in enumerate(R9B_ANCHOR_LANES):
        got = s["med"][lane]
        ref = R9B_BASELINE[name][order][i]
        rel = (got - ref) / ref
        s["base"][lane] = (ref, rel)
        alt = R9B_BASELINE[other][order][i]
        s["spread"][lane] = (other, alt, (got - alt) / alt, (alt - ref) / ref)
        if abs(rel) > R9_OFFSET_TELL:
            rflag(flags, scope, "ANCHOR",
                  f"`{lane}` reads {got:.3f} ms against the campaign baseline's {ref:.3f} "
                  f"({100.0 * rel:+.2f} %, past {100.0 * R9_OFFSET_TELL:.1f} %) for this rotation on "
                  f"{R9B_BASELINE_DEVICE['uuid']}. The other R9b rotation's row is {alt:.3f} at the "
                  f"same 8 lanes ({100.0 * (alt - ref) / ref:+.2f} % of composition spread), so read "
                  f"that spread, and the rotation's composition, before calling it machine drift. "
                  f"The pre-provenance references below raise nothing and never can")
    for i, lane in enumerate(R9B_PRE_PROVENANCE_LANES):
        for ref_name, lanes_n, table in R9B_PRE_PROVENANCE:
            if order not in table:
                continue
            ref = table[order][i]
            s["pre"].setdefault(lane, []).append(
                (ref_name, lanes_n, ref, (s["med"][lane] - ref) / ref))
    s["flank"] = {}
    for lane in R9B_FLANK_LANES:
        cycle = len(s["lanes"])
        first = median(s["tot"][lane][:cycle])
        last = median(s["tot"][lane][-cycle:])
        drift, tol = abs(last - first), max(FLANK_MS, FLANK_REL * s["med"][lane])
        s["flank"][lane] = (first, last, drift, tol)
        if drift > tol:
            rflag(flags, scope, "FLANK",
                  f"`{lane}`'s first and last full cycle differ by {drift:.3f} ms against the "
                  f"{tol:.3f} ms scaled reading — the session moved under itself")


def r9b_tier(s, a, b):
    """The two lanes' ARITHMETIC block tier, off the static register line the ARM lines carry. It is
    arithmetic and says so: R9 measured a body whose static 70 was ALLOCATED as 72, so the realized
    figure belongs to the G0 captures and to nothing here."""
    ta, tb = s["arms"][a]["blocks_sm"], s["arms"][b]["blocks_sm"]
    return f"same tier ({ta})" if ta == tb else f"**{ta} v {tb} — NOT tier-neutral**"


def r9b_emit(s):
    name, order = s["shape"], s["order"]
    shape = R9B_SHAPES[name]
    print(f"\n### `{R9B}` {name} (`{shape['flag']}`) — `--term-order {order}`, "
          f"{len(s['keys'])} paired rounds, {len(s['lanes'])} lanes\n")
    print(f"{shape['what']}.\n")
    print("| lane | body | budget | kernel | static regs | arith blocks/SM | threads | grid | C | "
          "removals | admitted | median `eval` | median `finalize` | median `eval+fin` |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    for a in s["lanes"]:
        f, cell = s["arms"][a], R9B_CELL[a]
        print(f"| `{a}` | {cell[0]} | {cell[1]} | `{f['kernel']}` | {f['regs']} | {f['blocks_sm']} "
              f"| {f['threads']} | {f['grid']} | {f['c']} | {f['removals']} | {f['admitted']} | "
              f"{s['med_ev'][a]:.3f} | {s['med_fin'][a]:.3f} | **{s['med'][a]:.3f}** |")
    print(f"\nStatic registers and the block tier derived from them are ARITHMETIC, off the ARM "
          f"lines — the realized register allocation and occupancy are the G0 captures' (amendment "
          f"A7), and the budget axis is NOT monotone in registers. Bodies, budgets, admitted "
          f"prefixes, grids and the one-plan premise are all checked and reported in the flags block "
          f"above; nothing here is filtered out on their account. Sign label at this rotation: "
          f"{R9B_THRESHOLD}/{R9B_ROUNDS}.")

    print(f"\n**Rows ({name}, {order})** — paired per round on `eval + finalize`, each naming its "
          f"baseline. WIN / LOSS / WASH are LABELS at {R9B_THRESHOLD}/{R9B_ROUNDS}; the reading is "
          f"the median, the sign count and the spread.\n")
    print("| # | contrast | baseline | median (ms) | IQR | min … max | % of baseline | on-sign | "
          "label | arith block tier | what it isolates |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |")
    for i, (a, b, what) in enumerate(shape["rows"], 1):
        c = r9b_paired(s, a, b)
        print(f"| {i} | `{a}` − `{b}` | `{b}` | **{c['med']:+.3f}** | {c['lo']:+.3f} … "
              f"{c['hi']:+.3f} | {c['min']:+.3f} … {c['max']:+.3f} | "
              f"{100.0 * c['med'] / s['med'][b]:+.2f} % | {c['on']}/{c['n']} | "
              f"**{VERDICT[c['verdict']]}** | {r9b_tier(s, a, b)} | {what} |")

    print(f"\n**Anchor lanes against the CAMPAIGN BASELINE ({name}, {order})** — the v3 R9b session, "
          f"re-based per RR 2026-08-13, and the first reference this campaign holds that records the "
          f"machine it was measured on. **This is the only thing the `ANCHOR` flag keys to**, at "
          f"{100.0 * R9_OFFSET_TELL:.1f} %, and it is compared rotation to its own rotation. Run "
          f"shape: {R9B_BASELINE_RUN}. Device: "
          + "; ".join(f"{k} `{v}`" for k, v in R9B_BASELINE_DEVICE.items()) + ".\n")
    alt_name = s["spread"][R9B_CTL][0]
    print(f"| anchor lane | this session ({name}, {len(s['lanes'])} lanes) | baseline ({name}) | "
          f"delta | baseline ({alt_name}, same {len(s['lanes'])} lanes) | delta | composition "
          f"spread | flank at capture |")
    print("| --- | --- | --- | --- | --- | --- | --- | --- |")
    for lane in R9B_ANCHOR_LANES:
        ref, rel = s["base"][lane]
        _, alt, alt_rel, spread = s["spread"][lane]
        print(f"| `{lane}` | {s['med'][lane]:.3f} | {ref:.3f} | {100.0 * rel:+.2f} % | {alt:.3f} | "
              f"{100.0 * alt_rel:+.2f} % | {100.0 * spread:+.2f} % | "
              f"{R9B_BASELINE_FLANK[(name, order)]} |")
    print(f"\nThe two rotations both carry {len(s['lanes'])} lanes and still differ: that column is "
          f"composition INSIDE a fixed lane count, kept rather than averaged away. `{alt_name}`'s "
          f"own flank at capture: {R9B_BASELINE_FLANK[(alt_name, order)]}.")
    # THE RETENTION RULE, in the output: two baselines live, the flag on the current one only.
    if len(R9B_BASELINES) > 1:
        prev_label, prev = R9B_BASELINES[1]
        print(f"\n**The previous baseline ({prev_label})**, kept live beside the current one so the "
              f"campaign's own step is visible. The `ANCHOR` flag does NOT key to it.\n")
        print("| anchor lane | this session | previous baseline | delta |")
        print("| --- | --- | --- | --- |")
        for i, lane in enumerate(R9B_ANCHOR_LANES):
            ref = prev[name][order][i]
            print(f"| `{lane}` | {s['med'][lane]:.3f} | {ref:.3f} | "
                  f"{100.0 * (s['med'][lane] - ref) / ref:+.2f} % |")
    else:
        print(f"\nBaselines keep TWO live — the current one and the immediately previous one — and "
              f"`{R9B_BASELINES[0][0]}` is the first this campaign has held, so there is no previous "
              f"row to print. The four references below are not baselines: none records a machine.")

    print(f"\n**Pre-provenance references ({name}, {order})** — every reference the campaign held "
          f"before the re-base. Reported as context and **never a flag basis**: none records the "
          f"machine it was measured on, and they disagree with each other by more than the "
          f"{100.0 * R9_OFFSET_TELL:.1f} % reporting threshold, so a flag keyed to them would report "
          f"their disagreement rather than this session. Two anchors, not three.\n")
    print(f"| anchor lane | this session ({len(s['lanes'])} lanes) | reference | lanes | "
          f"reference median | delta | provenance |")
    print("| --- | --- | --- | --- | --- | --- | --- |")
    for lane in R9B_PRE_PROVENANCE_LANES:
        for ref_name, lanes_n, ref, rel in s["pre"].get(lane, []):
            print(f"| `{lane}` | {s['med'][lane]:.3f} | {ref_name} | {lanes_n} | {ref:.3f} | "
                  f"{100.0 * rel:+.2f} % | **{R9B_UNRECORDED}** |")

    print(f"\n**Flank ({name}, {order})** — block medians of each INCUMBENT-body anchor lane's FIRST "
          f"and LAST full cycle ({len(s['lanes'])} rounds each), against max({FLANK_MS:.2f} ms, "
          f"{100.0 * FLANK_REL:.1f} % of that lane's session median). Every cell under test — body "
          f"or budget — is excluded: a cell is not its own drift sentinel. A reading, not a "
          f"mandate.\n")
    print("| anchor lane | first cycle | last cycle | drift | scaled reading | over? |")
    print("| --- | --- | --- | --- | --- | --- |")
    for lane in R9B_FLANK_LANES:
        first, last, drift, tol = s["flank"][lane]
        print(f"| `{lane}` | {first:.3f} | {last:.3f} | {drift:.3f} | {tol:.3f} | "
              f"{'**yes**' if drift > tol else 'no'} |")


def r9b_bridge(sessions, flags):
    """`c-hot16@128`'s reading in each session. A paired contrast is valid only INSIDE a session, so
    this is the session-comparability CONTEXT and not a decision. Build facts that disagree between
    the two sessions are flagged: the bridge lane is one cell of one build, so a register count or a
    kernel that moves means the two sessions are two builds."""
    rows, keyed = [], ("regs", "blocks_sm", "threads", "grid", "kernel", "c", "removals",
                       "admitted", "ids")
    names = [n for n in R9B_SHAPES if n in sessions]
    for order in ("locality", "census"):
        got = {n: sessions[n][order] for n in names if order in sessions[n]}
        meds = {n: s["med"][R9B_BRIDGE] for n, s in got.items()}
        rows.append((order, meds))
        if len(got) < 2:
            continue
        a, b = (got[n] for n in names)
        fa, fb = a["arms"][R9B_BRIDGE], b["arms"][R9B_BRIDGE]
        if tuple(fa[k] for k in keyed) != tuple(fb[k] for k in keyed):
            rflag(flags, "bridge", "BRIDGE",
                  f"`{R9B_BRIDGE}` declares different facts in the two sessions' `{order}` logs "
                  f"({fa['regs']} regs / {fa['kernel']} against {fb['regs']} regs / "
                  f"{fb['kernel']}) — "
                  f"those are facts of the BUILD, so the bridge lane does not bridge two sessions "
                  f"of one build")
        lo, hi = meds[names[0]], meds[names[1]]
        rel = (hi - lo) / lo
        if abs(rel) > R9_OFFSET_TELL:
            rflag(flags, "bridge", "BRIDGE",
                  f"`{R9B_BRIDGE}` reads {lo:.3f} ms in {names[0]} and {hi:.3f} ms in {names[1]} "
                  f"under `{order}` ({100.0 * rel:+.2f} %, past the "
                  f"{100.0 * R9_OFFSET_TELL:.1f} % reporting threshold) — the two rotations put "
                  f"different neighbours around it, so a cross-session comparison of any other row "
                  f"carries at least this much")
    return rows


def r9b_pct(pct):
    """The carveout tier as a manifest FIELD: no space, so an `NCU-*` line stays one grep."""
    return pct if pct is not None else "non-uniform"


def r9b_manifest(sessions, hints):
    """The ncu manifest, printed and authoritative, in two parts. The G0 list is EVERY timed cell,
    one launch each (amendment A7) — without it most of the register curve would rest on static REG
    lines, which is the error R9 documented. The Full-Picture list is five fixed lanes plus one
    conditional slot; the slot is filled from the CLASS session's own rows and is a capture-set
    choice, not a verdict."""
    where = {}
    for name in R9B_SHAPES:
        if name not in sessions:
            continue
        for order, s in sessions[name].items():
            for lane in s["lanes"]:
                where.setdefault(lane, (name, s))
    print("\n### ncu manifest\n")
    print("**G0 — every timed cell, one launch each** (amendment A7): "
          + ", ".join(R9B_G0_READS) + ". A configuration reading, so one launch per cell and no "
          "term order; the `static_regs` field is the ARM line's figure and is exactly what the "
          "capture is there to replace.\n")
    print("```")
    for lane in R9B_G0:
        body, budget, kernel = R9B_CELL[lane]
        if lane in where:
            name, s = where[lane]
            pct = hints[name].get("locality")
            print(f"NCU-G0 cell={lane} session={name} body={body} budget={budget} kernel={kernel} "
                  f"static_regs={s['arms'][lane]['regs']} carveout={r9b_pct(pct)}")
        else:
            print(f"NCU-G0 cell={lane} session=ABSENT body={body} budget={budget} kernel={kernel} "
                  f"static_regs=unread carveout=unread")
    print("```")
    best = {}
    if "CLASS" in sessions:
        for order, s in sessions["CLASS"].items():
            ranked = sorted(R9B_FULL_CANDIDATES,
                            key=lambda lane: r9b_paired(s, lane, R9B_INC)["med"])
            best[order] = (ranked[0], r9b_paired(s, ranked[0], R9B_INC)["med"])
    print(f"\n**Full Picture** — five FIXED lanes plus ONE conditional slot, both term orders. The "
          f"slot is the CLASS session's lowest-median corrected body against `{R9B_INC}`, chosen "
          f"from {{" + ", ".join(f'`{c}`' for c in R9B_FULL_CANDIDATES) + "}: a capture-set choice "
          f"and nothing else.\n")
    print("```")
    for lane, role in R9B_FULL:
        body, budget, kernel = R9B_CELL[lane]
        if lane in where:
            name, s = where[lane]
            pct = hints[name].get("locality")
            print(f"NCU-FULL lane={lane} orders=census,locality role={role} session={name} "
                  f"body={body} budget={budget} kernel={kernel} "
                  f"static_regs={s['arms'][lane]['regs']} carveout={r9b_pct(pct)}")
        else:
            print(f"NCU-FULL lane={lane} orders=census,locality role={role} session=ABSENT "
                  f"body={body} budget={budget} kernel={kernel} static_regs=unread carveout=unread")
    if not best:
        print("NCU-FULL lane=PENDING orders=census,locality role=class-best session=ABSENT — the "
              "CLASS session is not in this invocation, so no row selects it")
    elif len({lane for lane, _ in best.values()}) == 1:
        lane = best["locality"][0]
        body, budget, kernel = R9B_CELL[lane]
        reading = ", ".join(f"{o} {best[o][1]:+.3f} ms" for o in ("locality", "census") if o in best)
        print(f"NCU-FULL lane={lane} orders=census,locality role=class-best session=CLASS "
              f"body={body} budget={budget} kernel={kernel} vs_incumbent=[{reading}]")
    else:
        for order in ("locality", "census"):
            lane, med = best[order]
            body, budget, kernel = R9B_CELL[lane]
            print(f"NCU-FULL lane={lane} orders={order} role=class-best session=CLASS body={body} "
                  f"budget={budget} kernel={kernel} vs_incumbent=[{order} {med:+.3f} ms]")
    print("```")
    if len({lane for lane, _ in best.values()}) > 1:
        print("\nThe two term orders name DIFFERENT lowest-median corrected bodies — "
              + "; ".join(f"{o}: `{best[o][0]}`" for o in ("locality", "census"))
              + " — so BOTH are listed above and neither is reconciled.")


def r9b_report(sessions, paths, hints, bridge, flags):
    print("## v3 R9b — the corrected grouped-path bodies, over a register-budget grid\n")
    print(f"Every figure below is EMITTED, not transcribed. R9 measured a grouped-term path that "
          f"duplicated its coefficient DECODE; R9b repairs it and re-measures on two axes, which run "
          f"as TWO rotations under ONE tag — so a session is identified here by its LANE SET, never "
          f"by the tag. This emitter REPORTS: it computes the whole picture, flags what disagrees "
          f"with the rung's own description of itself, and issues NO verdict. Rows are never pooled "
          f"across term orders, and a paired contrast is only valid INSIDE one session.\n")
    reorder_flags_block(flags)
    print("\n### Sessions in this report\n")
    print("| rotation | lanes | term order | log | carveout applied (read off the log) | "
          "hinted symbols, in HINTED order |")
    print("| --- | --- | --- | --- | --- | --- |")
    for name in R9B_SHAPES:
        if name not in sessions:
            continue
        for order in ("locality", "census"):
            s = sessions[name].get(order)
            if s is None:
                continue
            # `None` reaches here only when no file declares this section's carveout block, which the
            # flags block has already said; the row still prints the session it summarizes.
            where = paths[name][order]
            print(f"| {name} (`{R9B_SHAPES[name]['flag']}`) | {len(s['lanes'])} | `{order}` | "
                  f"`{os.path.basename(where) if where else 'unattributed'}` | "
                  f"**{rtier(hints[name][order])}** | "
                  + ", ".join(f"`{sym}`" for sym in R9B_SHAPES[name]["hinted"]) + " |")
    missing = [n for n in R9B_SHAPES if n not in sessions]
    if missing:
        print(f"\n**{', '.join(missing)} not in this invocation.** Its rows, its anchor readings and "
              f"its half of the bridge are absent; pass both rotations' four logs together to get "
              f"them.")
    for name in R9B_SHAPES:
        if name in sessions:
            for order in ("locality", "census"):
                if order in sessions[name]:
                    r9b_emit(sessions[name][order])

    print(f"\n### The bridge — `{R9B_BRIDGE}` in both sessions\n")
    print(f"**CONTEXT, NOT A DECISION.** `{R9B_BRIDGE}` is the one cell both rotations carry. A "
          f"paired per-round contrast is only valid inside one session, so this row cannot be used "
          f"as one: it is the session-comparability reading, and how much of any cross-session "
          f"difference it explains is RR's call.\n")
    names = [n for n in R9B_SHAPES if n in sessions]
    print("| term order | " + " | ".join(f"{n} median" for n in names)
          + (" | delta | % |" if len(names) == 2 else " |"))
    print("| --- | " + " | ".join("---" for _ in names) + (" | --- | --- |" if len(names) == 2
                                                           else " |"))
    for order, meds in bridge:
        cells = " | ".join(f"{meds[n]:.3f}" if n in meds else "—" for n in names)
        if len(names) == 2 and len(meds) == 2:
            lo, hi = meds[names[0]], meds[names[1]]
            print(f"| `{order}` | {cells} | {hi - lo:+.3f} | {100.0 * (hi - lo) / lo:+.2f} % |")
        else:
            print(f"| `{order}` | {cells} |")

    print("\n### The whole picture, in one place\n")
    # This is the block a record is most likely to quote, so it restates the flag COUNT: the flags
    # block above is unmissable top-to-bottom and invisible to an excerpt.
    print(f"**{len(flags)} flag(s) above; this table is not a verdict.**"
          + ("" if flags else " Nothing disagreed with the rung's own description of itself.")
          + "\n")
    if "CLASS" in sessions:
        print(f"**The recovery rows** (`<corrected body>` − `{R9B_DROPIN}`) and **R9's drop-in "
              f"re-measured** (`{R9B_DROPIN}` − `{R9B_INC}`), both orders side by side. No gate: "
              f"the medians, the sign counts and the spreads are the reading.\n")
        print("| row | " + " | ".join(f"{o} median | {o} on-sign | {o} label" for o in
                                      ("locality", "census")) + " |")
        print("| --- | " + " | ".join("---" for _ in range(6)) + " |")
        for a, b in [(lane, R9B_DROPIN) for lane in R9B_FULL_CANDIDATES] + [(R9B_DROPIN, R9B_INC)]:
            cells = []
            for order in ("locality", "census"):
                s = sessions["CLASS"].get(order)
                if s is None:
                    cells += ["—", "—", "—"]
                    continue
                c = r9b_paired(s, a, b)
                cells += [f"**{c['med']:+.3f}** ({100.0 * c['med'] / s['med'][b]:+.2f} %)",
                          f"{c['on']}/{c['n']}", f"**{VERDICT[c['verdict']]}**"]
            print(f"| `{a}` − `{b}` | " + " | ".join(cells) + " |")
    if "BUDGET" in sessions:
        print(f"\n**The budget axis**, both orders side by side — the two separator rows and the "
              f"unmodified body's own two budgets.\n")
        print("| row | what it isolates | " + " | ".join(f"{o} median | {o} label" for o in
                                                        ("locality", "census")) + " |")
        print("| --- | --- | " + " | ".join("---" for _ in range(4)) + " |")
        for a, b, what in R9B_BUDGET_ROWS:
            cells = []
            for order in ("locality", "census"):
                s = sessions["BUDGET"].get(order)
                if s is None:
                    cells += ["—", "—"]
                    continue
                c = r9b_paired(s, a, b)
                cells += [f"**{c['med']:+.3f}** ({100.0 * c['med'] / s['med'][b]:+.2f} %)",
                          f"**{VERDICT[c['verdict']]}**"]
            print(f"| `{a}` − `{b}` | {what} | " + " | ".join(cells) + " |")

    facts = {}
    for name in R9B_SHAPES:
        s = sessions.get(name, {}).get("locality")
        if s is None:
            continue
        for lane in s["lanes"]:
            if lane in R9B_G0:
                facts.setdefault(lane, s["arms"][lane])
    print(f"\n**Build facts** (off the ARM lines, STATIC — the realized figures are the G0 "
          f"captures'): "
          + "; ".join(f"`{lane}` {facts[lane]['regs']} regs / {facts[lane]['blocks_sm']} arith "
                      f"blocks/SM" for lane in R9B_G0 if lane in facts)
          + ". The register budget is NOT monotone — `(128,6)` is the maximum-register cell — so "
            "budget order is not register order. Any disagreement between the two orders' logs, or "
            "between the two sessions, is in the flags block.")
    r9b_manifest(sessions, hints)
    late = [f for f in flags if f[0] in ("session", "bridge")]
    if late:
        print("\n**Session- and bridge-level flags** (restated from the flags block — they are what "
              "makes reading two orders, or two sessions, together a question):\n")
        for scope, tag, text in late:
            print(f"- **{tag}** (`{scope}`) — {text}")


def r9b(paths, where, narrowed):
    """The R9b entry point. It parses the log set ITSELF, one session at a time: the two rotations
    carry one tag and one lane count, so the shared parser — which keys a section by (tag, order) —
    would read two sessions as one mixed run."""
    if narrowed:
        sys.exit(f"{where}: the {R9B} rung is read over BOTH term orders, so `--order` cannot narrow "
                 f"it — emit the session logs together")
    groups = r9b_split(paths, where)
    sessions, paths_by, hints, flags = {}, {}, {}, []
    for name in R9B_SHAPES:
        if name not in groups:
            continue
        runs, arms, done, sched, files = parse(groups[name], where)
        orders = sorted({o for _, o in set(runs) | set(sched) | set(done)})
        if set(orders) != {"census", "locality"}:
            sys.exit(f"{where}: the {R9B} {name} rotation is read over EXACTLY both term orders "
                     f"(census and locality); its logs carry {', '.join(orders) or 'none'} — the "
                     f"missing order's rows cannot be computed")
        sessions[name], paths_by[name], hints[name] = {}, {}, {}
        for order in ("locality", "census"):
            key = (R9B, order)
            paths_by[name][order], hint = r9b_carveout(files, name, order, flags, where)
            sessions[name][order] = r9b_session(name, key, runs[key], arms.get(key, {}),
                                                done.get(key), sched.get(key), flags)
            hints[name][order] = hint
            r9b_readings(sessions[name][order], flags)
    if not sessions:
        sys.exit(f"{where}: no {R9B} session in this log set")
    # The cross-order and cross-session observations, appended before the block prints so nothing
    # lands after the fact unseen.
    keyed = ("regs", "blocks_sm", "threads", "grid", "kernel", "c", "removals", "admitted", "ids")
    for name, per_order in sessions.items():
        a_loc, a_cen = (per_order[o]["arms"] for o in ("locality", "census"))
        for lane in R9B_SHAPES[name]["lanes"]:
            if tuple(a_loc[lane][k] for k in keyed) != tuple(a_cen[lane][k] for k in keyed):
                rflag(flags, "session", "BUILD-FACTS",
                      f"{name}: lane `{lane}` declares different facts in the two orders' logs "
                      f"(registers, block tier, cell or plan) — those are facts of the BUILD, so "
                      f"these two logs describe two builds and their rows are not one session")
        if hints[name]["locality"] != hints[name]["census"]:
            rflag(flags, "session", "CARVEOUT-TIER",
                  f"{name}: the two orders were recorded at {rtier(hints[name]['locality'])} and "
                  f"{rtier(hints[name]['census'])} — every row contrasts cells at one L1 "
                  f"configuration, so these are two experiments")
    bridge = r9b_bridge(sessions, flags)
    r9b_report(sessions, paths_by, hints, bridge, flags)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("log", nargs="+")
    ap.add_argument("--order", help="emit only this term order")
    args = ap.parse_args()
    where = ", ".join(args.log)
    # R9b is routed BEFORE the shared parser, because it is the one rung whose log set can carry TWO
    # sessions: the shared parser keys a section by (tag, order) and the two R9b rotations share the
    # tag, so it would read the pair as one mixed run. An unreadable path scans as nothing and falls
    # through to the parser, which raises on it exactly as it always has.
    if any(R9B in r9b_scan(p)[0] for p in args.log):
        r9b(args.log, where, args.order)
        return
    runs, arms, done, sched, files = parse(args.log, where)
    keys = set(runs) | set(sched)
    tags = {tag for tag, _ in keys}
    if not keys:
        sys.exit(f"{where}: no SAMPLE lines and no `<ROTATION> schedule` line")
    # The two grammars are summarized under different preregistered rules, so a log set
    # carrying both is rejected rather than emitted under one of them.
    if R4 in tags and tags & set(FRONTIER):
        sys.exit(f"{where}: carries both {R4} and frontier sections — they are summarized "
                 f"under different preregistered rules; emit them separately")
    if tags - KNOWN:
        sys.exit(f"{where}: unknown rotation keyword(s) {sorted(tags - KNOWN)}")
    # The interior rung is decided under its own rules (amendment A2), so it is emitted alone.
    if R8 in tags and tags - {R8}:
        sys.exit(f"{where}: carries {R8} and {sorted(tags - {R8})} — the interior rung is "
                 f"decided under its own preregistered rules; emit it separately")
    # Same for the reorder rung: it is a BODY contrast at one plan, and no other rotation's rules
    # can summarize it.
    if R9 in tags and tags - {R9}:
        sys.exit(f"{where}: carries {R9} and {sorted(tags - {R9})} — the reorder rung is read "
                 f"under its own rules; emit it separately")

    # A DECLARED order is emitted or it is an error. Iterating the orders that happen to
    # carry SAMPLE rows silently drops a section whose samples were truncated away, and
    # `--order X` against a log without X used to exit 0 with no output at all.
    orders = sorted({o for _, o in keys}, key=lambda o: (o != "locality", o))
    if args.order:
        if args.order not in orders:
            sys.exit(f"{where}: no `{args.order}` section — the log carries "
                     f"{', '.join(orders)}")
        orders = [args.order]

    if R9 in tags:
        reorder(orders, runs, arms, done, sched, files, where, args.order)
        return
    if R8 in tags:
        interior(orders, runs, arms, done, sched, where, args.order)
        return
    if R4 in tags:
        for order in orders:
            key = (R4, order)
            emit(order, runs[key], arms.get(key, {}), done.get(key), sched.get(key))
        return
    frontier(orders, sorted(tags), runs, arms, done, sched, where)


if __name__ == "__main__":
    main()
