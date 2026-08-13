#!/usr/bin/env bash
# v3 R9b fixture matrix. Every row states the OBSERVATION or the GUARD it exercises; a fixture that
# stops behaving the way it does here means the emitter's reporting surface moved.
#
# The R9b emitter REPORTS rather than adjudicates (RR's amendment A10), so the suite is split the same
# way: `flagged` rows prove a policy observation reaches the flags block with the right text, and
# `rejects` rows are reserved for the cases where no meaningful number can be computed — a missing
# order, missing rounds, an incomplete round, an unknown lane, a truncated log, a foreign rotation in
# the set. Nothing else exits non-zero, and `no-flags` pins the clean state.
#
# THE TWO ROTATIONS SHARE ONE TAG, so a whole class of rows here is about the emitter recovering the
# SHAPE from the lane label set alone, and about the four-log invocation that is the only way the
# bridge lane's two medians can be printed.
#
# SELF-GENERATING: the logs are derived data, so `make_fixtures.py` writes them into a mktemp dir at
# run time and they are removed on exit. Nothing here needs a file that is not in the tracked tree —
# except the ACCEPTED-GRAMMAR rows, which replay real session logs when they are present and print a
# SKIP note when they are not (a clean checkout has no `.agents/` tree, and R9b's own session is
# Task 4's to measure). Those rows are the only ones in the suite that can be skipped, and none of
# them can fail the lane.
#
# EVERY match below reads its captured output through a HERE-STRING, never `printf … | grep -q`.
# Under `pipefail` that pipeline is a race: `grep -q` exits on the first match, the writer takes
# SIGPIPE, and the pipeline's status becomes the writer's 141 even though the match succeeded. It is
# invisible while the output fits one pipe write and fires once the report grows — measured at 4 % of
# runs on this suite's 39 KB four-log invocation, in a different row each time. A here-string is fed
# by the shell itself, so only grep's own status reaches the `if`.
#
# Run from anywhere:  bash gpu/gkr_uniskip_bench/tools/r9b_fixtures/check.sh
set -uo pipefail

DIR=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$DIR/../../../.." && pwd)
E=${E:-"python3 $ROOT/gpu/gkr_uniskip_bench/tools/r4_table.py"}
# Overridable so the clean-checkout SKIP paths are themselves testable.
SESSION=${SESSION:-$ROOT/.agents/sdd/2026-08-13-v3-r9b}
R9SESSION=${R9SESSION:-$ROOT/.agents/sdd/2026-08-12-v3-r9}
R8SESSION=${R8SESSION:-$ROOT/.agents/sdd/2026-08-12-v3-r8}
pass=0
fail=0
skip=0
# --- the whole-matrix reporting layer (RR, 2026-08-13: never reject on a gate prematurely) ---------
# Every row runs, every outcome prints, and the run ends with the full section matrix plus a
# MISMATCHES block naming what each row expected and what it found. The exit status is information
# for automation and nothing here is conditional on it.
MISMATCHES=()
SECTIONS=()
SECTION=""
sect_p=0
sect_f=0
section() { # section <name>
  [ -z "$SECTION" ] || SECTIONS+=("$SECTION|$((pass - sect_p + fail - sect_f))|$((pass - sect_p))|$((fail - sect_f))")
  SECTION=$1; sect_p=$pass; sect_f=$fail
  echo "### $1"
}
# The record is `|`-separated and an expectation can itself be a markdown table row, so `|` is folded
# to `¦` on the way in; the inline print below keeps the value verbatim.
bar() { printf '%s' "${1//|/¦}"; }
miss() { # miss <kind> <row name> <expected> <found>
  fail=$((fail+1))
  MISMATCHES+=("$(bar "$2")|$(bar "$3")|$(bar "$4")")
  printf 'MISMATCH(%s) %s\n  expected: %s\n  found:    %s\n' "$1" "$2" "$3" "$4"
}

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
python3 "$DIR/make_fixtures.py" "$TMP" >/dev/null || { echo "FAIL: fixture generation"; exit 1; }

# emits <name> <expected-substring> -- <args...>
# The emitter must succeed and print the substring. Every printed-surface row is one of these: under
# the reporting contract a policy observation never changes the exit status, so "emits" is also what
# proves a flagged session still reports everything.
emits() {
  local name=$1 want=$2; shift 3
  local out rc
  out=$($E "$@" 2>&1); rc=$?
  if [ "$rc" != 0 ]; then
    miss rejected "$name" "exit 0 and the substring below" "exit $rc: $(tail -1 <<< "$out")"; return
  fi
  if grep -qF -- "$want" <<< "$out"; then pass=$((pass+1));
  else miss outcome "$name" "$want" "not in the emitter's output"; fi
}

# flagged <name> <flag-row-substring> -- <args...>
# A POLICY observation: the emitter exits 0, prints everything, and carries the flag row. Both legs
# are checked — a row that only grepped for the text would pass on an emitter that had gone back to
# rejecting, and a row that only checked the status would pass on one that had gone silent.
flagged() {
  local name=$1 want=$2; shift 3
  local out rc
  out=$($E "$@" 2>/dev/null); rc=$?
  if [ "$rc" != 0 ]; then
    miss rejected "$name" "exit 0 — a policy observation must not stop the emitter" "exit $rc"
    return
  fi
  if ! grep -qF -- "$want" <<< "$out"; then
    miss flag "$name" "$want" "not in the flags block"; return
  fi
  # The whole picture is still printed: the G0 manifest is the last block, so its presence proves the
  # run went all the way through rather than stopping politely at the flag.
  if ! grep -qF -- "NCU-G0 cell=hot16@128" <<< "$out"; then
    printf 'FAIL(truncated) %s — flagged but the report stops before the ncu manifest\n' "$name"; fail=$((fail+1)); return
  fi
  pass=$((pass+1))
}

# flagged_once <name> <flag-substring> <expected-count> -- <args...>
# Some observations are true in every round; the block is the rung's only protection, so they must
# collapse to one row per lane rather than repeat.
flagged_once() {
  local name=$1 want=$2 want_n=$3; shift 4
  local out rc n
  out=$($E "$@" 2>/dev/null); rc=$?
  if [ "$rc" != 0 ]; then miss rejected "$name" "exit 0" "exit $rc"; return; fi
  n=$(grep -cF -- "$want" <<< "$out")
  if [ "$n" = "$want_n" ]; then pass=$((pass+1));
  else miss count "$name" "$want_n row(s) matching: $want" "$n row(s)"; fi
}

# rejects <name> <expected-substring> -- <args...>
rejects() {
  local name=$1 want=$2; shift 3
  local out rc
  out=$($E "$@" 2>&1 >/dev/null); rc=$?
  if [ "$rc" = 0 ]; then
    miss accepted "$name" "a non-zero exit — no number can be computed here" "exit 0"; return
  fi
  if grep -qF -- "$want" <<< "$out"; then pass=$((pass+1));
  else miss message "$name" "$want" "${out:-<nothing on stderr>}"; fi
}

# absent <name> <forbidden-extended-regex> -- <args...>
# A rejected run emits nothing, so the exit status is checked FIRST: otherwise a crashing emitter
# would pass every one of these rows for the wrong reason.
absent() {
  local name=$1 nope=$2; shift 3
  local out rc
  out=$($E "$@" 2>/dev/null); rc=$?
  if [ "$rc" != 0 ]; then miss rejected "$name" "exit 0" "exit $rc"; return; fi
  if grep -qE -- "$nope" <<< "$out"; then
    miss outcome "$name" "the output must NOT match: $nope" "it matched"
  else pass=$((pass+1)); fi
}

# One CLASS session = the two logs that rotation requires, locality first; likewise BUDGET; `both` is
# the four-log invocation that the bridge row needs.
cls() { printf '%s %s ' "$TMP/$1-class-locality.log" "$TMP/$1-class-census.log"; }
bud() { printf '%s %s ' "$TMP/$1-budget-locality.log" "$TMP/$1-budget-census.log"; }
both() { printf '%s %s %s %s ' "$TMP/$1-class-locality.log" "$TMP/$1-class-census.log" \
                               "$TMP/$1-budget-locality.log" "$TMP/$1-budget-census.log"; }
# A one-log mutant rides the conforming half, so only the mutated log is under test.
half() { printf '%s %s ' "$TMP/$1-class-locality.log" "$TMP/good-class-census.log"; }
# A mutated BUDGET session beside the conforming CLASS one: that is how a cross-SESSION observation
# (the bridge) is reached at all.
bridge() { printf '%s %s %s %s ' "$TMP/good-class-locality.log" "$TMP/good-class-census.log" \
                                 "$TMP/$1-budget-locality.log" "$TMP/$1-budget-census.log"; }

section "the real grammar"
# None of these rows decides anything: they prove the emitter accepts what the runner really writes,
# and that the paths this one rides beside still emit.
if [ -r "$SESSION/r9b-class-locality.log" ] && [ -r "$SESSION/r9b-class-census.log" ]; then
  emits "the real R9b CLASS session logs are read end to end" \
    "### The whole picture, in one place" \
    -- "$SESSION/r9b-class-locality.log" "$SESSION/r9b-class-census.log"
else
  echo "  SKIP accepted-grammar row: no R9b CLASS session logs at $SESSION (not measured yet)"
  skip=$((skip+1))
fi
if [ -r "$SESSION/r9b-budget-locality.log" ] && [ -r "$SESSION/r9b-budget-census.log" ]; then
  emits "the real R9b BUDGET session logs are read end to end" \
    "### The bridge — \`c-hot16@128\` in both sessions" \
    -- "$SESSION/r9b-budget-locality.log" "$SESSION/r9b-budget-census.log"
  emits "and all four real logs together print the bridge with both medians" \
    "**CONTEXT, NOT A DECISION.**" \
    -- "$SESSION/r9b-class-locality.log" "$SESSION/r9b-class-census.log" \
       "$SESSION/r9b-budget-locality.log" "$SESSION/r9b-budget-census.log"
else
  echo "  SKIP accepted-grammar rows: no R9b BUDGET session logs at $SESSION (not measured yet)"
  skip=$((skip+2))
fi
if [ -r "$R9SESSION/reorder-locality.log" ] && [ -r "$R9SESSION/reorder-census.log" ]; then
  emits "the archived R9 session logs still emit under the REORDER path (now legacy)" \
    "## v3 R9 — the gate-first reordered pair body" \
    -- "$R9SESSION/reorder-locality.log" "$R9SESSION/reorder-census.log"
  # THE PROVENANCE OF THE R9 REFERENCE ROW: the two medians this file's reference table carries are
  # that path's own output over those logs, and this row is what re-derives them rather than trusting
  # the literal.
  emits "and the R9 reference medians this rung quotes are that path's own output, locality" \
    "| \`control@256\` | \`eval_lsb_pair\` | 72 | 3 | 256 | 32768 | 0 | 0 | 0 | 16.692 | 0.033 | **16.725** |" \
    -- "$R9SESSION/reorder-locality.log" "$R9SESSION/reorder-census.log"
  emits "and its incumbent anchor, census" \
    "| \`hot16@128\` | \`eval_lsb_pair_cached_128_lb\` | 72 | 7 | 128 | 65536 | 28 | 145 | 16 | 15.394 | 0.063 | **15.458** |" \
    -- "$R9SESSION/reorder-locality.log" "$R9SESSION/reorder-census.log"
else
  echo "  SKIP R9-regression rows: no R9 session logs at $R9SESSION"
  skip=$((skip+3))
fi
if [ -r "$R8SESSION/interior-locality.log" ] && [ -r "$R8SESSION/interior-census.log" ]; then
  emits "the archived R8 session logs still emit under the interior path" \
    "## v3 R8 — the admission-frontier interior (K17–23)" \
    -- "$R8SESSION/interior-locality.log" "$R8SESSION/interior-census.log"
else
  echo "  SKIP R8-regression row: no R8 session logs at $R8SESSION"
  skip=$((skip+1))
fi

section "the reporting contract"
emits "the emitter says what it is: it reports, it does not decide" \
  "This emitter REPORTS: it computes the whole picture, flags what disagrees with the rung's own description of itself, and issues NO verdict." \
  -- $(both good)
emits "a conforming session set raises NO flag at all" \
  "**None.** Every observation below matched the rung's own description of itself" -- $(both good)
absent "no pass/fail gate line anywhere in the output" \
  "gate is \*\*(MET|NOT met)\*\*|clears wash-or-better" -- $(both good)
absent "no selected cell" "SELECTED" -- $(both good)
emits "the two rotations are named by their lane sets, not by the tag" \
  "which run as TWO rotations under ONE tag — so a session is identified here by its LANE SET, never by the tag" \
  -- $(both good)
emits "the block tier is labelled ARITHMETIC and handed to the G0 captures" \
  "the realized register allocation and occupancy are the G0 captures' (amendment A7), and the budget axis is NOT monotone in registers" \
  -- $(both good)
emits "and the build-facts line says budget order is not register order" \
  "The register budget is NOT monotone — \`(128,6)\` is the maximum-register cell — so budget order is not register order." \
  -- $(both good)

section "the printed surface — CLASS"
emits "the CLASS rotation is identified with its flag and its lane count" \
  "| CLASS (\`--r9b-class\`) | 8 | \`locality\` | \`good-class-locality.log\` | **16 %** |" -- $(both good)
emits "every lane carries its body AND its budget beside the kernel" \
  "| \`c-hot16@128\` | C | (128,7) | \`eval_lsb_pair_cached_reorder_c_128_lb\` | 70 | 7 | 128 | 65536 | 28 | 145 | 16 | 14.577 | 0.063 | **14.640** |" \
  -- $(cls good)
emits "row 1 is C against the incumbent" \
  "| 1 | \`c-hot16@128\` − \`hot16@128\` | \`hot16@128\` | **-0.150** | -0.155 … -0.143 | -0.171 … -0.126 | -1.01 % | 96/96 | **WIN** | same tier (7) |" \
  -- $(cls good)
emits "rows 2-4 carry the other three corrected bodies against the incumbent" \
  "| 4 | \`bd-hot16@128\` − \`hot16@128\` | \`hot16@128\` | **+0.251**" -- $(cls good)
emits "row 5 is THE RECOVERY ROW, C" \
  "| 5 | \`c-hot16@128\` − \`reorder-hot16@128\` | \`reorder-hot16@128\` | **-0.949** | -0.951 … -0.948 | -0.979 … -0.918 | -6.09 % | 96/96 | **WIN** | same tier (7) | THE RECOVERY ROW, C — what the decode repair gives back against the implementation R9 measured |" \
  -- $(cls good)
emits "rows 6-8 are the recovery rows for B, C+D and B+D" \
  "| 8 | \`bd-hot16@128\` − \`reorder-hot16@128\` | \`reorder-hot16@128\` | **-0.546**" -- $(cls good)
emits "row 9 re-measures R9's drop-in INSIDE this session" \
  "| 9 | \`reorder-hot16@128\` − \`hot16@128\` | \`hot16@128\` | **+0.802** | +0.793 … +0.807 | +0.787 … +0.813 | +5.42 % | 96/96 | **LOSS** | same tier (7) | R9's drop-in re-measured INSIDE this session — the +5.43 % reference point, on this rotation and this machine |" \
  -- $(cls good)
emits "the recovery rows are restated for BOTH orders side by side" \
  "| \`c-hot16@128\` − \`reorder-hot16@128\` | **-0.949** (-6.09 %) | 96/96 | **WIN** | **-0.969** (-6.01 %) | 96/96 | **WIN** |" \
  -- $(cls good)

section "the printed surface — BUDGET, and the two separator rows"
emits "the BUDGET rotation is identified with its own flag" \
  "| BUDGET (\`--r9b-budget\`) | 8 | \`locality\` | \`good-budget-locality.log\` | **16 %** |" -- $(both good)
emits "the incumbent's own three budgets are on lanes, non-monotone registers and all" \
  "| \`hot16-lb6@128\` | incumbent | (128,6) | \`eval_lsb_pair_cached_128_lb6\` | 80 | 6 |" -- $(bud good)
emits "and the unbounded incumbent, the arm R9 never timed" \
  "| \`hot16-free@128\` | incumbent | unbounded | \`eval_lsb_pair_cached_128\` | 75 | 6 |" -- $(bud good)
emits "rows 1-2 are labelled the budget axis on an UNMODIFIED body — RR's question" \
  "the budget axis on an UNMODIFIED body (RR's question) — the incumbent at (128, 6), the grid's maximum-register cell" \
  -- $(bud good)
emits "and row 2 names the debt it discharges" \
  "the incumbent unbounded, the arm R9's record left as static arithmetic (A8)" -- $(bud good)
emits "the first separator row is labelled the remat collapse at constant block tier" \
  "| 4 | \`c-hot16-lb6@128\` − \`c-hot16@128\` | \`c-hot16@128\` | **-0.100** | -0.119 … -0.081 | -0.129 … -0.071 | -0.68 % | 96/96 | **WIN** | **6 v 7 — NOT tier-neutral** | the remat collapse at constant block tier |" \
  -- $(bud good)
emits "the second is labelled the extra block at constant collapse" \
  "| 5 | \`c-hot16-free@128\` − \`c-hot16-lb6@128\` | \`c-hot16-lb6@128\` | **-0.150** | -0.162 … -0.138 | -0.170 … -0.130 | -1.03 % | 96/96 | **WIN** | **8 v 6 — NOT tier-neutral** | the extra block at constant collapse |" \
  -- $(bud good)
emits "and C unbounded against the incumbent closes the axis" \
  "| 6 | \`c-hot16-free@128\` − \`hot16@128\` | \`hot16@128\` | **-0.398**" -- $(bud good)

section "the bridge"
emits "the bridge is marked CONTEXT and not a decision" \
  "**CONTEXT, NOT A DECISION.** \`c-hot16@128\` is the one cell both rotations carry." -- $(both good)
emits "and it says a paired contrast is only valid inside one session" \
  "A paired per-round contrast is only valid inside one session, so this row cannot be used as one" \
  -- $(both good)
emits "both medians and their delta, locality" "| \`locality\` | 14.640 | 14.640 | +0.000 | +0.00 % |" \
  -- $(both good)
emits "both medians and their delta, census" "| \`census\` | 15.170 | 15.170 | +0.000 | +0.00 % |" \
  -- $(both good)
emits "a CLASS-only invocation says the other rotation is absent" \
  "**BUDGET not in this invocation.** Its rows, its anchor readings and its half of the bridge are absent" \
  -- $(cls good)
emits "and prints the half of the bridge it has" "| \`locality\` | 14.640 |" -- $(cls good)
flagged "a bridge lane whose BUILD facts move between the two sessions" \
  "\`c-hot16@128\` declares different facts in the two sessions' \`locality\` logs (70 regs / eval_lsb_pair_cached_reorder_c_128_lb against 71 regs / eval_lsb_pair_cached_reorder_c_128_lb)" \
  -- $(bridge bridge-facts)
flagged "a bridge lane 7 % apart in the two sessions" \
  "reads 14.640 ms in CLASS and 15.690 ms in BUDGET under \`locality\` (+7.17 %, past the 1.5 % reporting threshold)" \
  -- $(bridge bridge-medians)
emits "and that flag says what a cross-session comparison then carries" \
  "the two rotations put different neighbours around it, so a cross-session comparison of any other row carries at least this much" \
  -- $(bridge bridge-medians)

section "the CAMPAIGN BASELINE — the re-base, and the only thing the ANCHOR flag keys to"
emits "the baseline says what it is and what keys to it" \
  "**This is the only thing the \`ANCHOR\` flag keys to**, at 1.5 %, and it is compared rotation to its own rotation." \
  -- $(cls good)
emits "the device identity travels with the numbers, uuid and all" \
  "Device: name \`NVIDIA RTX PRO 6000 Blackwell Server Edition\`; uuid \`GPU-cbaba4fd-068d-d035-1c18-1d9c16f1648b\`; serial \`1794525048975\`; driver \`610.57.04\`; vbios \`98.02.8D.00.08\`; power cap \`600.00 W\`; MIG mode \`Disabled\`; compute mode \`Default\`; ncu \`2026.2.1.0 (build 38283040)\`; CUDA \`13.3, V13.3.73\`." \
  -- $(cls good)
emits "so does the run shape the medians were taken at" \
  "Run shape: 8 lanes, 96 paired rounds / 8 warmup, \`--log-trace 24\`, carveout 16 % uniform, one process per (rotation, order), 80 s discarded soak each, binary sha256 \`881594043a89\`." \
  -- $(cls good)
# THREE anchors since the re-base, and BOTH rotations on every row: the spread between two 8-lane
# rotations is a fact a future rung needs, so it is a column rather than an average.
emits "the CLASS baseline row for control@256, with the BUDGET row and the spread beside it" \
  "| \`control@256\` | 16.650 | 16.725 | -0.45 % | 16.778 | -0.76 % | +0.32 % | clean (0.004–0.015 ms drift) |" \
  -- $(cls good)
emits "control_lb@128 is an anchor now — the third of the three" \
  "| \`control_lb@128\` | 16.473 | 16.455 | +0.11 % | 16.493 | -0.12 % | +0.23 % | clean (0.004–0.015 ms drift) |" \
  -- $(cls good)
emits "and the incumbent" \
  "| \`hot16@128\` | 14.788 | 14.793 | -0.03 % | 14.823 | -0.24 % | +0.20 % | clean (0.004–0.015 ms drift) |" \
  -- $(cls good)
# THE RETENTION RULE, in the output (RR 2026-08-13): two baselines live, older ones archived, the
# pre-provenance block frozen at four.
emits "the retention rule is stated where a future rung will read it" \
  "Baselines keep TWO live — the current one and the immediately previous one — and \`R9b session, 2026-08-13\` is the first this campaign has held, so there is no previous row to print. The four references below are not baselines: none records a machine." \
  -- $(cls good)
emits "the spread is kept, not averaged away, and the other rotation's flank is named" \
  "The two rotations both carry 8 lanes and still differ: that column is composition INSIDE a fixed lane count, kept rather than averaged away. \`BUDGET\`'s own flank at capture: clean (0.010–0.055 ms drift)." \
  -- $(cls good)
# The flank status of the baseline session itself, in-code, so a future rung choosing a canonical pair
# sees which census reference moved under itself without re-reading the measurement report.
emits "the CLASS/census baseline row is marked FLANK at capture" \
  "| **FLANK: 0.088–0.099 ms drift, past its 0.077–0.085 ms readings** |" -- $(cls good)
emits "and BUDGET/census is named the flank-clean census reference" \
  "clean (0.011–0.023 ms drift) — the flank-clean census reference" -- $(bud good)
emits "the BUDGET rotation reads against its OWN baseline row" \
  "| \`control@256\` | 16.650 | 16.778 | -0.76 % | 16.725 | -0.45 % | -0.32 % |" -- $(bud good)

section "the pre-provenance block — reported, labelled, and never a flag basis"
emits "it says what it is and why it cannot flag" \
  "Reported as context and **never a flag basis**: none records the machine it was measured on, and they disagree with each other by more than the 1.5 % reporting threshold, so a flag keyed to them would report their disagreement rather than this session. Two anchors, not three." \
  -- $(cls good)
emits "the R4-frozen literal, labelled 11 lanes and unrecorded" \
  "| \`control@256\` | 16.650 | R4 frozen | 11 | 16.624 | +0.15 % | **machine identity: unrecorded** |" \
  -- $(cls good)
emits "the archived R5 session, labelled 10 lanes" \
  "| \`control@256\` | 16.650 | R5 session | 10 | 16.567 | +0.50 % | **machine identity: unrecorded** |" \
  -- $(cls good)
emits "the archived R8 session, labelled 12 lanes" \
  "| \`control@256\` | 16.650 | R8 session | 12 | 16.738 | -0.53 % | **machine identity: unrecorded** |" \
  -- $(cls good)
emits "the R9 session, labelled 6 lanes — the rung this one corrects" \
  "| \`control@256\` | 16.650 | R9 session | 6 | 16.725 | -0.45 % | **machine identity: unrecorded** |" \
  -- $(cls good)
emits "the incumbent anchor gets the same four references" \
  "| \`hot16@128\` | 14.788 | R9 session | 6 | 14.794 | -0.04 % | **machine identity: unrecorded** |" \
  -- $(cls good)
emits "the R9 census pair is pinned too" \
  "| \`hot16@128\` | 15.288 | R9 session | 6 | 15.458 | -1.10 % | **machine identity: unrecorded** |" \
  -- $(cls good)
absent "control_lb@128 has no pre-provenance row — the old references carry two anchors" \
  "^\| .control_lb@128. \| 16\..* \| (R4 frozen|R5 session|R8 session|R9 session) \|" -- $(cls good)

section "THE RE-BASE, proved in one fixture: on the baseline, far from the history, no flag"
emits "a session sitting exactly on the baseline reads 0.00 % against it" \
  "| \`control@256\` | 16.903 | 16.903 | +0.00 % | 16.893 | +0.06 % | -0.06 % |" \
  -- $(cls baseline-exact)
emits "and +2.16 % against R4-frozen at the same time" \
  "| \`control@256\` | 16.903 | R4 frozen | 11 | 16.545 | +2.16 % | **machine identity: unrecorded** |" \
  -- $(cls baseline-exact)
emits "and +1.53 % against R5, also past the threshold" \
  "| \`hot16@128\` | 15.352 | R5 session | 10 | 15.120 | +1.53 % | **machine identity: unrecorded** |" \
  -- $(cls baseline-exact)
absent "yet NO ANCHOR flag fires — the historical block cannot raise one" \
  "\*\*ANCHOR\*\*" -- $(cls baseline-exact)
emits "so that session is flag-free, which is the whole point of the re-base" \
  "**None.** Every observation below matched the rung's own description of itself" -- $(cls baseline-exact)
emits "and both rotations of it are flag-free together" \
  "**0 flag(s) above; this table is not a verdict.**" -- $(both baseline-exact)

section "the flank reading"
emits "the flank is a reading with its threshold beside it, not a mandate" \
  "| \`hot16@128\` | 14.789 | 14.791 | 0.002 | 0.074 | no |" -- $(cls good)
absent "no cell under test is a flank sentinel — the incumbent's other budgets included" \
  "^\| .(hot16-lb6@128|hot16-free@128|c-hot16). \| 1[45]\..* \| (yes|no) \|" -- $(bud good)

section "the ncu manifest — G0 for every timed cell, Full Picture for six"
emits "G0 names all ten timed cells and what each capture reads" \
  "**G0 — every timed cell, one launch each** (amendment A7): allocated-registers, register-limit, shared-limit, warps-limit, blocks-limit, blocks-per-sm, achieved-occupancy." \
  -- $(both good)
emits "the incumbent's G0 line" \
  "NCU-G0 cell=hot16@128 session=CLASS body=incumbent budget=(128,7) kernel=eval_lsb_pair_cached_128_lb static_regs=72 carveout=16" \
  -- $(both good)
emits "the lowest-register cell's G0 line, off the BUDGET session" \
  "NCU-G0 cell=c-hot16-free@128 session=BUDGET body=C budget=unbounded kernel=eval_lsb_pair_cached_reorder_c_128 static_regs=64 carveout=16" \
  -- $(both good)
emits "the maximum-register cell's G0 line" \
  "NCU-G0 cell=hot16-lb6@128 session=BUDGET body=incumbent budget=(128,6) kernel=eval_lsb_pair_cached_128_lb6 static_regs=80 carveout=16" \
  -- $(both good)
emits "the static register field says it is what the capture replaces" \
  "the \`static_regs\` field is the ARM line's figure and is exactly what the capture is there to replace" \
  -- $(both good)
emits "a G0 cell whose session was not passed is named ABSENT rather than dropped" \
  "NCU-G0 cell=c-hot16-free@128 session=ABSENT body=C budget=unbounded kernel=eval_lsb_pair_cached_reorder_c_128 static_regs=unread carveout=unread" \
  -- $(cls good)
emits "the Full Picture is five fixed lanes plus one conditional slot" \
  "**Full Picture** — five FIXED lanes plus ONE conditional slot, both term orders." -- $(both good)
emits "R9's drop-in is a FIXED member" \
  "NCU-FULL lane=reorder-hot16@128 orders=census,locality role=r9-dropin session=CLASS" -- $(both good)
emits "so are C at (128,6), C unbounded and the unbounded incumbent" \
  "NCU-FULL lane=hot16-free@128 orders=census,locality role=incumbent-unbounded session=BUDGET" \
  -- $(both good)
emits "the conditional slot is the CLASS session's lowest-median corrected body" \
  "NCU-FULL lane=c-hot16@128 orders=census,locality role=class-best session=CLASS body=C budget=(128,7) kernel=eval_lsb_pair_cached_reorder_c_128_lb vs_incumbent=[locality -0.150 ms, census -0.120 ms]" \
  -- $(both good)
emits "and it says the choice is a capture-set choice and nothing else" \
  "a capture-set choice and nothing else" -- $(both good)
emits "with no CLASS session there is no best row, and the slot says so" \
  "NCU-FULL lane=PENDING orders=census,locality role=class-best session=ABSENT — the CLASS session is not in this invocation, so no row selects it" \
  -- $(bud good)
absent "and no 'best' is computed from the rotation that cannot select one" \
  "role=class-best session=CLASS" -- $(bud good)
emits "the two orders disagreeing on the best body lists BOTH" \
  "NCU-FULL lane=b-hot16@128 orders=census role=class-best session=CLASS" -- $(cls best-split)
emits "and says so in prose" \
  "The two term orders name DIFFERENT lowest-median corrected bodies — locality: \`c-hot16@128\`; census: \`b-hot16@128\` — so BOTH are listed above and neither is reconciled." \
  -- $(cls best-split)
absent "the controls are not in either manifest" "NCU-(G0 cell|FULL lane)=control" -- $(both good)

section "the sign LABEL, at its threshold and one below it"
emits "87/96 on one side is labelled WIN" \
  "| \`c-hot16@128\` − \`reorder-hot16@128\` | **-0.100** (-0.64 %) | 87/96 | **WIN** |" \
  -- $(cls sign-at-threshold)
emits "86/96 at the same median is labelled WASH" \
  "| \`c-hot16@128\` − \`reorder-hot16@128\` | **-0.100** (-0.64 %) | 86/96 | **WASH** |" \
  -- $(cls sign-below-threshold)
emits "a wobbling recovery row is labelled WASH and still prints its median" \
  "| \`c-hot16@128\` − \`reorder-hot16@128\` | **+0.011** (+0.07 %) | 48/96 | **WASH** |" -- $(cls recovery-wash)
emits "every corrected body slower than the drop-in is four LOSS labels, printed" \
  "| \`bd-hot16@128\` − \`reorder-hot16@128\` | **+0.604** (+3.87 %) | 96/96 | **LOSS** |" \
  -- $(cls recovery-loss)
emits "and that session still gets its whole capture manifest" \
  "NCU-G0 cell=bd-hot16@128 session=CLASS" -- $(cls recovery-loss)

section "policy observations reach the flags block, and stop nothing"
flagged "a session recorded at another --log-trace" \
  "lane \`control@256\` declares grid=16384; at \`--log-trace 24\` it is 32768" -- $(cls wrong-trace)
flagged "a session at another warmup" \
  "the session ran 96 rounds / 12 warmup; the rung's shape is 96 / 8" -- $(cls wrong-warmup)
flagged "a session at another round count that still closes into cycles" \
  "the session ran 104 rounds / 8 warmup; the rung's shape is 96 / 8" -- $(cls wrong-rounds)
flagged "the lanes ran in a fixed order every round" \
  "lane \`control@256\` does not take rotation positions [0, 1, 2, 3, 4, 5, 6, 7] exactly 12 times" \
  -- $(cls rotation-fixed)
# A SWAPPED BODY and a SWAPPED BUDGET are different observations, and the emitter names the cell it
# actually saw rather than quoting a symbol at the reader.
flagged "a lane declaring another BODY's cell" \
  "lane \`c-hot16@128\` declares body \`eval_lsb_pair_cached_reorder_b_128_lb\` = B at (128,7) (\`b-hot16@128\`'s cell); the rotation runs it on \`eval_lsb_pair_cached_reorder_c_128_lb\` = C at (128,7)" \
  -- $(cls body-swapped)
flagged "a lane declaring the same body at another BUDGET" \
  "lane \`c-hot16@128\` runs body C at budget (128,7) in this rotation but declares \`eval_lsb_pair_cached_reorder_c_128_lb6\`, which is C at (128,6)" \
  -- $(cls budget-swapped)
emits "and that flag says why no other field could see it" \
  "the register budget is not monotone (\`(128,6)\` is the maximum-register cell), so a swapped budget cannot be read off any other field" \
  -- $(cls budget-swapped)
flagged "the unmodified body's own budget swapped, in the BUDGET rotation" \
  "lane \`hot16-free@128\` runs body incumbent at budget unbounded in this rotation but declares \`eval_lsb_pair_cached_128_lb6\`, which is incumbent at (128,6)" \
  -- $(bud budget-swapped-inc)
flagged "a lane pricing a different plan from the incumbent every row is read against" \
  "every row reads as a CELL contrast only while the plan is one plan" -- $(cls plan-mismatch)
flagged "a reversal among two equal-ref sources" \
  "admitted prefix is not the canonical one — at admission position 12: 9 where the oracle has 8" \
  -- $(cls ids-reversed)
flagged "two lanes carrying one lane's data" \
  "carry BIT-IDENTICAL samples in every round" -- $(half lane-aliased)
flagged "a lane whose samples name another cell in one round" \
  "lane \`bd-hot16@128\` names \`eval_lsb_pair_cached_reorder_cd_128_lb\` in 1 of 96 rounds (first at round 20)" \
  -- $(half kernel-forged)
flagged_once "a lane whose EVERY sample names another cell is ONE observation" \
  "**SAMPLE-BODY** | lane \`bd-hot16@128\` names \`eval_lsb_pair_cached_reorder_cd_128_lb\` in 96 of 96 rounds (first at round 8)" \
  1 -- $(half body-drift)
flagged "one lane's register count moving between the two orders' logs" \
  "CLASS: lane \`c-hot16@128\` declares different facts in the two orders' logs (registers, block tier, cell or plan)" \
  -- $(half regs-cross-order)
flagged "the header's own lane count disagreeing with the ARM lines" \
  "the log carries 8 ARM lines while the schedule declares lanes=7 and the trailer lanes=7" \
  -- $(cls header-lanes)
flagged "an anchor lane off the campaign baseline, with the device it was measured on named" \
  "\`control@256\` reads 17.149 ms against the campaign baseline's 16.725 (+2.54 %, past 1.5 %) for this rotation on GPU-cbaba4fd-068d-d035-1c18-1d9c16f1648b" \
  -- $(cls anchor-offset)
flagged "and the flag hands over the composition spread and the historical block's standing" \
  "The other R9b rotation's row is 16.778 at the same 8 lanes (+0.32 % of composition spread), so read that spread, and the rotation's composition, before calling it machine drift. The pre-provenance references below raise nothing and never can" \
  -- $(cls anchor-offset)
flagged "a drifting anchor lane" \
  "\`hot16@128\`'s first and last full cycle differ by 0.302 ms against the 0.074 ms scaled reading" \
  -- $(cls flank-tripped)

section "the carveout grammar — per ROTATION, in HINTED order"
flagged "a missing per-symbol echo" \
  "a missing, spurious, duplicated or reordered echo means the cells were not steered as these rows assume" \
  -- $(cls echo-missing)
flagged "and the CLASS rotation's own hinted set is quoted, cd BEFORE b" \
  "the \`--r9b-class\` rotation's hinted set is ['eval_lsb_pair_cached_128_lb', 'eval_lsb_pair_cached_reorder_128_lb', 'eval_lsb_pair_cached_reorder_c_128_lb', 'eval_lsb_pair_cached_reorder_cd_128_lb', 'eval_lsb_pair_cached_reorder_b_128_lb', 'eval_lsb_pair_cached_reorder_bd_128_lb'] IN THAT ORDER" \
  -- $(cls echo-missing)
# CONCERN 3, pinned: the echo order is the HINTED table's, not the lane order. A fixture echoing the
# LANE order must be flagged, or a real echo-order change would pass unremarked.
flagged "the echoes in LANE order (b before cd) rather than HINTED order" \
  "which is the harness's HINTED order and not its lane order" -- $(cls echo-lane-order)
flagged "an echo for a symbol the rotation does not hint" \
  "'16%:eval_lsb_seg_g'" -- $(cls echo-extra)
flagged "one symbol echoed twice" \
  "'16%:eval_lsb_pair_cached_reorder_bd_128_lb', '16%:eval_lsb_pair_cached_128_lb'" \
  -- $(cls echo-duplicated)
flagged "the hinted symbols steered to two different percents" \
  "the hinted symbols are steered to [16, 33] % — every row below contrasts cells at ONE L1 configuration" \
  -- $(cls echo-wrong-pct)
flagged "no carveout-symbols line at all" \
  "carries 0 \`carveout symbols\` lines, one expected" -- $(cls symbols-missing)
flagged "two carveout-symbols lines" \
  "carries 2 \`carveout symbols\` lines, one expected" -- $(cls symbols-twice)
flagged "the set line's count disagreeing with its own list" \
  "the set line says \`5 local (eval_lsb_pair_cached_128_lb," -- $(cls symbols-count-wrong)
flagged "the set line's list disagreeing with the per-symbol echoes" \
  "the two must describe one configuration" -- $(cls symbols-disagree)
flagged "a carveout line that is neither grammar" \
  "is not the harness's carveout literal" -- $(cls echo-malformed)
# The BUDGET rotation hints a DIFFERENT set, so the check has to be shape-keyed.
flagged "the BUDGET rotation's own hinted set, one symbol short" \
  "the \`--r9b-budget\` rotation's hinted set is ['eval_lsb_pair_cached_128_lb', 'eval_lsb_pair_cached_128_lb6', 'eval_lsb_pair_cached_128', 'eval_lsb_pair_cached_reorder_c_128_lb', 'eval_lsb_pair_cached_reorder_c_128_lb6', 'eval_lsb_pair_cached_reorder_c_128'] IN THAT ORDER" \
  -- $(bud echo-missing-budget)
flagged "both term orders in one log: the carveout block is not attributable" \
  "one log is one process, so the carveout block below is shared between two term orders" \
  -- "$TMP/two-orders-class-locality.log"
flagged "the two orders recorded at different tiers, one of them non-uniform" \
  "CLASS: the two orders were recorded at non-uniform and 16 % — every row contrasts cells at one L1 configuration" \
  -- "$TMP/echo-wrong-pct-class-locality.log" "$TMP/good-class-census.log"
emits "a non-uniform carveout is reported as such in the header, not resolved to a number" \
  "| CLASS (\`--r9b-class\`) | 8 | \`locality\` | \`echo-wrong-pct-class-locality.log\` | **non-uniform** |" \
  -- $(cls echo-wrong-pct)
emits "and in the capture manifest" "carveout=non-uniform" -- $(cls echo-wrong-pct)

section "the flag count travels with the block a record quotes"
emits "a clean session set says so where the headline table is" \
  "**0 flag(s) above; this table is not a verdict.** Nothing disagreed with the rung's own description of itself." \
  -- $(both good)
emits "and a flagged session carries its count into the same place" \
  "**16 flag(s) above; this table is not a verdict.**" -- $(cls wrong-trace)
emits "session- and bridge-level flags are restated at the foot" \
  "**Session- and bridge-level flags** (restated from the flags block — they are what makes reading two orders, or two sessions, together a question):" \
  -- $(half regs-cross-order)

section "the errors that remain: no meaningful number can be computed"
rejects "one order alone" "read over EXACTLY both term orders" -- "$TMP/good-class-locality.log"
rejects "one rotation's locality beside the other's census: each is then a half" \
  "read over EXACTLY both term orders" \
  -- "$TMP/good-class-locality.log" "$TMP/good-budget-census.log"
rejects "--order cannot narrow the R9b path" "\`--order\` cannot narrow it" \
  -- --order locality $(cls good)
rejects "an order nobody measured" "its logs carry census, reverse" -- $(half unknown-order)
rejects "a lane neither rotation names" \
  "which is neither R9b rotation (CLASS is missing ['c-hot16@128'] and does not name ['c-hot17@128']" \
  -- $(half lane-unknown)
rejects "and the message names the BUDGET rotation's own miss too" \
  "BUDGET is missing ['c-hot16-free@128', 'c-hot16-lb6@128', 'c-hot16@128', 'hot16-free@128', 'hot16-lb6@128']" \
  -- $(half lane-unknown)
rejects "an ARM line without its admitted-id list" \
  "the two grammars are not interchangeable" -- $(half arm-without-ids)
rejects "no done trailer" "the run did not finish, or the log is truncated" -- $(half no-trailer)
rejects "renumbered rounds" "rounds are missing or renumbered" -- $(half renumbered)
rejects "one lane is one sample short" \
  "the contrasts are paired per round, so an incomplete round has no contrast" -- $(half sample-dropped)
rejects "a duplicated (round, lane) sample" \
  "duplicate sample for order=locality round=20 lane=c-hot16@128" -- $(half sample-duplicated)
rejects "one log relabelled as another rotation" \
  "declares ['FRONTIER-INTERIOR'] beside R9B" -- $(half wrong-tag)
rejects "both logs relabelled: they are then read under the interior rules, which reject them" \
  "lane set is not the interior rotation" -- $(cls wrong-tag)
rejects "an R4 factorial log in the set" \
  "declares ['CACHE-FACTORIAL'] beside R9B" -- $(cls good) "$TMP/not-r9b.log"

section ""   # close the last section

echo
echo "================================================================================"
echo "THE WHOLE MATRIX — every R9b fixture row this run computed"
echo "================================================================================"
echo
echo "| section | rows | matched | mismatched |"
echo "| --- | --- | --- | --- |"
for row in ${SECTIONS[@]+"${SECTIONS[@]}"}; do
  IFS='|' read -r sname srows sok sbad <<< "$row"
  printf '| %s | %s | %s | %s |\n' "$sname" "$srows" "$sok" "$sbad"
done
printf '| **total** | **%d** | **%d** | **%d** |\n' "$((pass + fail))" "$pass" "$fail"
[ "$skip" = 0 ] || printf '\n%d row(s) SKIPPED — a log this suite replays is not on disk yet; not a verdict either way.\n' "$skip"
echo
if [ "$fail" = 0 ]; then
  echo "### MISMATCHES — none."
  echo
  echo "**Every row computed its answer and every answer matched.**"
else
  echo "### MISMATCHES — $fail"
  echo
  echo "Each row computed an answer and the answer was not the expected one. Nothing was rejected on"
  echo "any one of them: every row above ran and the matrix is complete."
  echo
  echo "| # | row | expected | found |"
  echo "| --- | --- | --- | --- |"
  i=0
  for row in ${MISMATCHES[@]+"${MISMATCHES[@]}"}; do
    i=$((i+1))
    IFS='|' read -r mname mwant mgot <<< "$row"
    printf '| %s | %s | %s | %s |\n' "$i" "$mname" "$mwant" "$mgot"
  done
fi
echo
printf 'fixture matrix: %d passed, %d failed, %d skipped\n' "$pass" "$fail" "$skip"
echo "exit status $(( fail > 0 )) — information for automation only; the report above is printed either way."
exit $(( fail > 0 ))
