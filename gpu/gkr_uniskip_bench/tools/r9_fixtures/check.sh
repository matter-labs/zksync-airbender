#!/usr/bin/env bash
# v3 R9 gate-first-reorder fixture matrix. Every row states the OBSERVATION or the GUARD it
# exercises; a fixture that stops behaving the way it does here means the emitter's reporting
# surface moved.
#
# The R9 emitter REPORTS rather than adjudicates (RR's call for this rung), so the suite is split
# the same way: `flagged` rows prove a policy observation reaches the flags block with the right
# text, and `rejects` rows are reserved for the cases where no meaningful number can be computed —
# a missing order, missing rounds, an incomplete round, an unknown lane, a truncated log, a log the
# parser cannot read. Nothing else exits non-zero, and `no-flags` pins the clean state.
#
# SELF-GENERATING: the logs are derived data, so `make_fixtures.py` writes them into a mktemp dir
# at run time and they are removed on exit. Nothing here needs a file that is not in the tracked
# tree — except the ACCEPTED-GRAMMAR rows, which replay real session logs when they are present
# and print a SKIP note when they are not (a clean checkout has no `.agents/` tree, and R9's own
# session is Task 4's to measure). Those rows are the only ones in the suite that can be skipped,
# and none of them can fail the lane.
#
# Run from anywhere:  bash gpu/gkr_uniskip_bench/tools/r9_fixtures/check.sh
set -uo pipefail

DIR=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$DIR/../../../.." && pwd)
E=${E:-"python3 $ROOT/gpu/gkr_uniskip_bench/tools/r4_table.py"}
# Overridable so the clean-checkout SKIP paths are themselves testable.
SESSION=${SESSION:-$ROOT/.agents/sdd/2026-08-12-v3-r9}
R8SESSION=${R8SESSION:-$ROOT/.agents/sdd/2026-08-12-v3-r8}
R5SESSION=${R5SESSION:-$ROOT/.agents/sdd/2026-08-10-v3-r5}
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
# The emitter must succeed and print the substring. Every printed-surface row is one of these:
# under the reporting contract a policy observation never changes the exit status, so "emits" is
# also what proves a flagged session still reports everything.
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
  # The whole picture is still printed: the capture set is the last block, so its presence proves
  # the run went all the way through rather than stopping politely at the flag.
  if ! grep -qF -- "NCU-CAPTURE lane=hot16@128" <<< "$out"; then
    printf 'FAIL(truncated) %s — flagged but the report stops before the capture set\n' "$name"; fail=$((fail+1)); return
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

# One fixture session = the two logs the emitter requires, locality first.
sess() { printf '%s %s ' "$TMP/$1-locality.log" "$TMP/$1-census.log"; }
# A one-log mutant rides the conforming census log, so only the mutated half is under test.
half() { printf '%s %s ' "$TMP/$1-locality.log" "$TMP/good-census.log"; }

section "the real grammar"
# None of these rows decides anything: they prove the emitter accepts what the runner really
# writes, and that the two paths this file rides beside still emit.
if [ -r "$SESSION/reorder-locality.log" ] && [ -r "$SESSION/reorder-census.log" ]; then
  emits "the real R9 session logs are read end to end" "### The whole picture, in one place" \
    -- "$SESSION/reorder-locality.log" "$SESSION/reorder-census.log"
else
  echo "  SKIP accepted-grammar row: no R9 session logs at $SESSION (not measured yet)"
  skip=$((skip+1))
fi
if [ -r "$R8SESSION/interior-locality.log" ] && [ -r "$R8SESSION/interior-census.log" ]; then
  emits "the archived R8 session logs still emit under the interior path" \
    "## v3 R8 — the admission-frontier interior (K17–23)" \
    -- "$R8SESSION/interior-locality.log" "$R8SESSION/interior-census.log"
else
  echo "  SKIP R8-regression row: no R8 session logs at $R8SESSION"
  skip=$((skip+1))
fi
if [ -r "$R5SESSION/task3-primary-locality.log" ] && \
   [ -r "$R5SESSION/task3-primary-census.log" ]; then
  emits "the archived R5 session logs still emit under the legacy path" \
    "## v3 R5 — admission-frontier curves" \
    -- "$R5SESSION/task3-primary-locality.log" "$R5SESSION/task3-primary-census.log"
else
  echo "  SKIP legacy-regression row: no R5 session logs at $R5SESSION"
  skip=$((skip+1))
fi

section "the reporting contract"
emits "the emitter says what it is: it reports, it does not decide" \
  "This emitter REPORTS: it computes the whole picture, flags what disagrees with the rung's own description of itself, and issues NO verdict." \
  -- $(sess good)
emits "a conforming session raises NO flag at all" \
  "**None.** Every observation below matched the rung's own description of itself" -- $(sess good)
# The two lines the old build printed as answers. Their absence is the reporting contract.
absent "no pass/fail gate line anywhere in the output" \
  "gate is \*\*(MET|NOT met)\*\*|clears wash-or-better" -- $(sess good)
absent "no selected outcome-matrix cell" "SELECTED" -- $(sess good)
emits "the outcome matrix is printed as a labelled reference, not a selection" \
  "**Reference: what each combination would mean** — a labelled reading of the rung's two axes, NOT a selection." \
  -- $(sess good)
emits "and its register axis is stated as a fact rather than resolved into a cell" \
  "This session's register axis, stated: \`reorder-hot16@128\` is BELOW \`hot16@128\` (70 vs 72 registers), and \`reorder-hot16-free@128\` runs 64 registers at 8 blocks/SM." \
  -- $(sess good)
emits "the other side of the register axis is stated the same way" \
  "\`reorder-hot16@128\` is NOT below \`hot16@128\` (72 vs 72 registers)" -- $(sess regs-unchanged)

section "the printed surface"
emits "the carveout percent is READ off the log and printed in the header" \
  "| \`locality\` | \`good-locality.log\` | **16 %** | \`eval_lsb_pair_cached_128_lb\`, \`eval_lsb_pair_cached_reorder_128_lb\`, \`eval_lsb_pair_cached_reorder_128\` |" \
  -- $(sess good)
emits "lane facts — registers, occupancy tier, body, plan — come off the ARM lines" \
  "| \`reorder-hot16@128\` | \`eval_lsb_pair_cached_reorder_128_lb\` | 70 | 7 | 128 | 65536 | 28 | 145 | 16 | 14.525 | 0.063 | **14.588** |" \
  -- $(sess good)
emits "row 1 carries median, IQR, spread, sign count and a LABEL" \
  "| 1 | \`reorder-hot16@128\` − \`hot16@128\` | \`hot16@128\` | **-0.198** | -0.207 … -0.193 | -0.213 … -0.187 | -1.34 % | 96/96 | **WIN** | same class |" \
  -- $(sess good)
emits "row 2 is the envelope, and its occupancy tier is NOT the incumbent's" \
  "| 2 | \`reorder-hot16-free@128\` − \`hot16@128\` | \`hot16@128\` | **-0.348** | -0.357 … -0.343 | -0.379 … -0.319 | -2.35 % | 96/96 | **WIN** | **8 v 7 blocks/SM — NOT occupancy-neutral** |" \
  -- $(sess good)
emits "row 3 is labelled as the BUNDLED envelope delta, which it cannot decompose" \
  "the pure envelope delta — occupancy + twiddle remat BUNDLED: the unbounded body collapses the remat AND gains a block, and this row cannot separate them" \
  -- $(sess good)
emits "row 4 is the reordered machinery floor, against the bound-matched control" \
  "| 4 | \`reorder-cache0@128\` − \`control_lb@128\` | \`control_lb@128\` | **+0.671** | +0.651 … +0.679 | +0.631 … +0.699 | +4.09 % | 96/96 | **LOSS** |" \
  -- $(sess good)
emits "row 5 is capture under the reorder, against that floor" \
  "| 5 | \`reorder-hot16@128\` − \`reorder-cache0@128\` | \`reorder-cache0@128\` | **-2.482** |" -- $(sess good)
emits "row 1 is restated for BOTH orders side by side, with no reconciliation" \
  "| \`locality\` | **-0.198** | -0.207 … -0.193 | -0.213 … -0.187 | 96/96 | **WIN** | 16 % |" \
  -- $(sess good)
emits "and the other order beside it" \
  "| \`census\` | **-0.148** | -0.157 … -0.143 | -0.163 … -0.137 | 96/96 | **WIN** | 16 % |" \
  -- $(sess good)
emits "the build facts and the carveout are stated in one line" \
  "**Build facts** (off the ARM lines): \`hot16@128\` 72 regs / 7 blocks/SM, \`reorder-hot16@128\` 70 / 7, \`reorder-hot16-free@128\` 64 / 8. Carveout 16 % on all three hinted symbols." \
  -- $(sess good)

section "the anchor reference table — every reference, with its lane count"
emits "the R4-frozen literal, labelled 11 lanes" \
  "| \`control@256\` | 16.650 | R4 frozen | 11 | 16.624 | +0.15 % |" -- $(sess good)
emits "the archived R5 session, labelled 10 lanes — that rotation's own \`lanes=\` field" \
  "| \`control@256\` | 16.650 | R5 session | 10 | 16.567 | +0.50 % |" -- $(sess good)
emits "the archived R8 session, labelled 12 lanes" \
  "| \`control@256\` | 16.650 | R8 session | 12 | 16.738 | -0.53 % |" -- $(sess good)
emits "the incumbent anchor gets the same three references" \
  "| \`hot16@128\` | 14.788 | R8 session | 12 | 14.812 | -0.16 % |" -- $(sess good)
emits "the table says why the lane count is on it" \
  "absolute medians are rotation-composition dependent, so each reference carries the LANE COUNT of the rotation that produced it against this rung's 6" \
  -- $(sess good)
emits "the flank is a reading with its threshold beside it, not a mandate" \
  "| \`hot16@128\` | 14.794 | 14.796 | 0.002 | 0.074 | no |" -- $(sess good)
absent "the bodies under test are not flank sentinels" \
  "^\| .reorder-hot16@128. \| 14\.5" -- $(sess good)

section "the capture set"
emits "the incumbent is captured, with its body, registers and carveout" \
  "NCU-CAPTURE lane=hot16@128 orders=census,locality roles=incumbent body=eval_lsb_pair_cached_128_lb regs=72 carveout=16" \
  -- $(sess good)
emits "the bounded gate-first body is captured" \
  "NCU-CAPTURE lane=reorder-hot16@128 orders=census,locality roles=bounded-reorder body=eval_lsb_pair_cached_reorder_128_lb regs=70 carveout=16" \
  -- $(sess good)
emits "the unbounded gate-first body is captured" \
  "NCU-CAPTURE lane=reorder-hot16-free@128 orders=census,locality roles=unbounded-reorder body=eval_lsb_pair_cached_reorder_128 regs=64 carveout=16" \
  -- $(sess good)
absent "the machinery floor and the controls are not in the capture set" \
  "NCU-CAPTURE lane=(reorder-cache0|control)" -- $(sess good)
emits "a session where row 1 is slower captures the same three lanes" \
  "NCU-CAPTURE lane=reorder-hot16@128 orders=census,locality roles=bounded-reorder" -- $(sess row1-loss)

section "the sign LABEL, at its threshold and one below it"
emits "87/96 on one side is labelled WIN" \
  "| \`locality\` | **-0.100** | -0.100 … -0.100 | -0.100 … +0.100 | 87/96 | **WIN** | 16 % |" \
  -- $(sess sign-at-threshold)
emits "86/96 at the same median is labelled WASH" \
  "| \`locality\` | **-0.100** | -0.100 … -0.100 | -0.100 … +0.100 | 86/96 | **WASH** | 16 % |" \
  -- $(sess sign-below-threshold)
emits "a wobbling row 1 is labelled WASH and still prints its median" \
  "| \`locality\` | **-0.010** |" -- $(sess row1-wash)
emits "a slower row 1 is labelled LOSS in both orders" "| \`census\` | **+0.252** |" -- $(sess row1-loss)
emits "faster in one order and slower in the other: both rows print" \
  "| \`locality\` | **-0.198** | -0.207 … -0.193 | -0.213 … -0.187 | 96/96 | **WIN** | 16 % |" \
  -- $(sess row1-split)
emits "and the disagreement is left standing, not resolved" "| \`census\` | **+0.252** |" \
  -- $(sess row1-split)

section "policy observations reach the flags block, and stop nothing"
flagged "a session recorded at another --log-trace" \
  "lane \`control@256\` declares grid=16384; at \`--log-trace 24\` it is 32768" -- $(sess wrong-trace)
flagged "a session at another warmup" \
  "the session ran 96 rounds / 12 warmup; the rung's shape is 96 / 6" -- $(sess wrong-warmup)
flagged "a session at another round count" \
  "the session ran 102 rounds / 6 warmup; the rung's shape is 96 / 6" -- $(sess wrong-rounds)
flagged "the lanes ran in a fixed order every round" \
  "lane \`control@256\` does not take rotation positions [0, 1, 2, 3, 4, 5] exactly 16 times" \
  -- $(sess rotation-fixed)
flagged "a reorder lane declaring the incumbent's body" \
  "lane \`reorder-hot16@128\` declares body \`eval_lsb_pair_cached_128_lb\`; the rotation runs it on \`eval_lsb_pair_cached_reorder_128_lb\`" \
  -- $(sess body-forged)
flagged "a reorder lane pricing a different plan from the incumbent" \
  "the headline row reads as a BODY contrast only while the plan is one plan" -- $(sess plan-mismatch)
flagged "a reversal among two equal-ref sources" \
  "admitted prefix is not the canonical one — at admission position 12: 9 where the oracle has 8" \
  -- $(sess ids-reversed)
flagged "two lanes carrying one lane's data" \
  "carry BIT-IDENTICAL samples in every round" -- $(half lane-aliased)
flagged "a lane whose samples name another body in one round" \
  "lane \`reorder-hot16-free@128\` names \`eval_lsb_pair_cached_reorder_128_lb\` in 1 of 96 rounds (first at round 20)" \
  -- $(half kernel-forged)
flagged "one lane's register count moving between the two orders' logs" \
  "declares different facts in the two orders' logs (registers, occupancy tier, body or plan)" \
  -- $(half regs-cross-order)
flagged "an anchor lane off every reference, with all three deltas named" \
  "reads 17.149 ms, more than 1.5 % off R4 frozen (11 lanes) +3.16 %; R5 session (10 lanes) +3.51 %; R8 session (12 lanes) +2.46 %" \
  -- $(sess anchor-offset)
flagged "and the flag says why a thin rotation is the first suspicion" \
  "this rotation carries 6 lanes against their 10–12, so read the reference table before calling it machine drift" \
  -- $(sess anchor-offset)
flagged "a drifting anchor lane" \
  "\`hot16@128\`'s first and last full cycle differ by 0.302 ms against the 0.074 ms scaled reading" \
  -- $(sess flank-tripped)
flagged "a missing per-symbol echo" \
  "a missing, spurious, duplicated or reordered echo means the bodies were not steered as the rung's premise assumes" \
  -- $(sess echo-missing)
flagged "an echo for a symbol the rotation does not hint" \
  "the rotation's hinted set is ['eval_lsb_pair_cached_128_lb', 'eval_lsb_pair_cached_reorder_128_lb', 'eval_lsb_pair_cached_reorder_128'] in that order" \
  -- $(sess echo-extra)
flagged "the echoes in another order" \
  "the applied echoes are ['16%:eval_lsb_pair_cached_reorder_128', '16%:eval_lsb_pair_cached_reorder_128_lb', '16%:eval_lsb_pair_cached_128_lb']" \
  -- $(sess echo-reordered)
flagged "one symbol echoed twice" \
  "'16%:eval_lsb_pair_cached_reorder_128', '16%:eval_lsb_pair_cached_128_lb'" -- $(sess echo-duplicated)
# The UNIFORMITY observation, which is what the rung's premise actually needs — not a tier.
flagged "the hinted symbols steered to two different percents" \
  "the hinted symbols are steered to [16, 33] % — the rung's premise is ONE L1 configuration for all three bodies (amendment A3)" \
  -- $(sess echo-wrong-pct)
flagged "no carveout-symbols line at all" \
  "carries 0 \`carveout symbols\` lines, one expected" -- $(sess symbols-missing)
flagged "two carveout-symbols lines" \
  "carries 2 \`carveout symbols\` lines, one expected" -- $(sess symbols-twice)
flagged "the set line's count disagreeing with its own list" \
  "the set line says \`2 local (eval_lsb_pair_cached_128_lb, eval_lsb_pair_cached_reorder_128_lb, eval_lsb_pair_cached_reorder_128)\`" \
  -- $(sess symbols-count-wrong)
flagged "the set line's list disagreeing with the per-symbol echoes" \
  "the two must describe one configuration" -- $(sess symbols-disagree)
flagged "a carveout line that is neither grammar" \
  "is not the harness's carveout literal" -- $(sess echo-malformed)
flagged "both term orders in one log: the carveout block is not attributable" \
  "one log is one process, so the carveout block below is shared between two term orders" \
  -- "$TMP/two-orders-locality.log"
flagged "the header's own lane count disagreeing with the ARM lines" \
  "the log carries 6 ARM lines while the schedule declares lanes=5 and the trailer lanes=5" \
  -- $(sess header-lanes)
flagged "two log files declaring one section: the carveout block is one of several" \
  "2 log files declare this section (split-body-locality.log, split-trailer-locality.log)" \
  -- "$TMP/split-body-locality.log" "$TMP/split-trailer-locality.log" "$TMP/good-census.log"
# One row per lane, not per round: the same forgery in all 96 rounds used to print 96 rows.
flagged_once "a lane whose EVERY sample names another body is ONE observation" \
  "**SAMPLE-BODY** | lane \`reorder-hot16-free@128\` names \`eval_lsb_pair_cached_reorder_128_lb\` in 96 of 96 rounds (first at round 6)" \
  1 -- $(half body-drift)
flagged "the two orders recorded at different tiers, one of them non-uniform" \
  "the two orders were recorded at non-uniform and 16 % — the rung's premise is one L1 configuration" \
  -- "$TMP/echo-wrong-pct-locality.log" "$TMP/good-census.log"

section "the flag count travels with the block a record quotes"
emits "a clean session says so where the headline table is" \
  "**0 flag(s) above; this table is not a verdict.** Nothing disagreed with the rung's own description of itself." \
  -- $(sess good)
emits "and a flagged session carries its count into the same place" \
  "**12 flag(s) above; this table is not a verdict.**" -- $(sess wrong-trace)

# A non-uniform session still prints, and says so where the percent would have gone.
emits "a non-uniform carveout is reported as such in the header, not resolved to a number" \
  "| \`locality\` | \`echo-wrong-pct-locality.log\` | **non-uniform** |" -- $(sess echo-wrong-pct)
emits "and in the capture set" "carveout=non-uniform" -- $(sess echo-wrong-pct)
# The word carries its own unit: a stray `%` after it reads as a number that is not there.
emits "a non-uniform tier prints without a stray percent sign in the headline table" \
  "| 96/96 | **WIN** | non-uniform |" -- $(sess echo-wrong-pct)
emits "and in the build-facts line" \
  "Carveout non-uniform on all three hinted symbols." -- $(sess echo-wrong-pct)

section "the errors that remain: no meaningful number can be computed"
rejects "one order alone" "read over EXACTLY both term orders" -- "$TMP/good-locality.log"
rejects "--order cannot narrow the reorder path" "\`--order\` cannot narrow it" \
  -- --order locality $(sess good)
rejects "an order nobody measured" "this log set carries census, reverse" -- $(half unknown-order)
rejects "a lane the rotation does not name" \
  "lane set is not the reorder rotation — missing ['reorder-hot16@128'], unexpected ['reorder-hot17@128']" \
  -- $(half lane-unknown)
rejects "an ARM line without its admitted-id list" \
  "the two grammars are not interchangeable" -- $(half arm-without-ids)
rejects "no done trailer" "the run did not finish, or the log is truncated" -- $(half no-trailer)
rejects "renumbered rounds" "rounds are missing or renumbered" -- $(half renumbered)
rejects "one lane is one sample short" \
  "the contrasts are paired per round, so an incomplete round has no contrast" -- $(half sample-dropped)
rejects "a duplicated (round, lane) sample" \
  "duplicate sample for order=locality round=20 lane=reorder-hot16@128" -- $(half sample-duplicated)
rejects "one log relabelled as another rotation" \
  "carries FRONTIER-INTERIOR and ['REORDER']" -- $(half wrong-tag)
rejects "both logs relabelled: they are then read under the interior rules, which reject them" \
  "lane set is not the interior rotation" -- $(sess wrong-tag)
rejects "an R4 factorial log in the set" \
  "carries REORDER and ['CACHE-FACTORIAL']" -- $(sess good) "$TMP/not-r9.log"

section ""   # close the last section

echo
echo "================================================================================"
echo "THE WHOLE MATRIX — every R9 fixture row this run computed"
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
