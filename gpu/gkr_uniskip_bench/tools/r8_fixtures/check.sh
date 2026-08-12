#!/usr/bin/env bash
# v3 R8 admission-interior fixture matrix. Every row states the RULE or the GUARD it exercises;
# a fixture that stops behaving the way it does here means the emitter's decision surface moved.
#
# SELF-GENERATING: the logs are derived data, so `make_fixtures.py` writes them into a mktemp
# dir at run time and they are removed on exit. Nothing here needs a file that is not in the
# tracked tree — except the two ACCEPTED-GRAMMAR rows, which replay real session logs when they
# are present and print a SKIP note when they are not (a clean checkout has no `.agents/` tree).
# Those two are the only rows in the suite that can be skipped, and neither can fail the lane.
#
# Run from anywhere:  bash gpu/gkr_uniskip_bench/tools/r8_fixtures/check.sh
set -uo pipefail

DIR=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$DIR/../../../.." && pwd)
E=${E:-"python3 $ROOT/gpu/gkr_uniskip_bench/tools/r4_table.py"}
# Overridable so the clean-checkout SKIP paths are themselves testable.
SESSION=${SESSION:-$ROOT/.agents/sdd/2026-08-12-v3-r8}
R5SESSION=${R5SESSION:-$ROOT/.agents/sdd/2026-08-10-v3-r5}
pass=0
fail=0
skip=0

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
python3 "$DIR/make_fixtures.py" "$TMP" >/dev/null || { echo "FAIL: fixture generation"; exit 1; }

# rejects <name> <expected-substring> -- <args...>
rejects() {
  local name=$1 want=$2; shift 3
  local out rc
  out=$($E "$@" 2>&1 >/dev/null); rc=$?
  if [ "$rc" = 0 ]; then printf 'FAIL(accepted) %s\n' "$name"; fail=$((fail+1)); return; fi
  if printf '%s' "$out" | grep -qF -- "$want"; then pass=$((pass+1));
  else printf 'FAIL(message) %s\n  want: %s\n  got:  %s\n' "$name" "$want" "$out"; fail=$((fail+1)); fi
}

# emits <name> <expected-substring> -- <args...>
emits() {
  local name=$1 want=$2; shift 3
  local out rc
  out=$($E "$@" 2>&1); rc=$?
  if [ "$rc" != 0 ]; then printf 'FAIL(rejected) %s\n  %s\n' "$name" "$(printf '%s' "$out" | tail -1)"; fail=$((fail+1)); return; fi
  if printf '%s' "$out" | grep -qF -- "$want"; then pass=$((pass+1));
  else printf 'FAIL(outcome) %s\n  want: %s\n' "$name" "$want"; fail=$((fail+1)); fi
}

# absent <name> <forbidden-extended-regex> -- <args...>
# A rejected run emits nothing, so the exit status is checked FIRST: otherwise a crashing
# emitter would pass every one of these rows for the wrong reason.
absent() {
  local name=$1 nope=$2; shift 3
  local out rc
  out=$($E "$@" 2>/dev/null); rc=$?
  if [ "$rc" != 0 ]; then printf 'FAIL(rejected) %s\n' "$name"; fail=$((fail+1)); return; fi
  if printf '%s' "$out" | grep -qE -- "$nope"; then
    printf 'FAIL(outcome) %s\n  must NOT emit: %s\n' "$name" "$nope"; fail=$((fail+1))
  else pass=$((pass+1)); fi
}

# invalidated <name> <want-on-stdout> <forbidden-on-stdout> -- <args...>
# The A6 invalidation is BOTH a non-zero status (reason on stderr) and a printed record that
# names itself not authoritative. A row checking only one of the two would pass on an emitter
# that dropped the other, so this one checks both.
invalidated() {
  local name=$1 want=$2 nope=$3; shift 4
  local out rc
  out=$($E "$@" 2>/dev/null); rc=$?
  if [ "$rc" = 0 ]; then printf 'FAIL(accepted) %s\n' "$name"; fail=$((fail+1)); return; fi
  if ! printf '%s' "$out" | grep -qF -- "$want"; then
    printf 'FAIL(outcome) %s\n  want on stdout: %s\n' "$name" "$want"; fail=$((fail+1)); return
  fi
  if printf '%s' "$out" | grep -qF -- "$nope"; then
    printf 'FAIL(outcome) %s\n  must NOT emit: %s\n' "$name" "$nope"; fail=$((fail+1)); return
  fi
  pass=$((pass+1))
}

# One fixture session = the two logs the emitter requires, locality first.
sess() { printf '%s %s ' "$TMP/$1-locality.log" "$TMP/$1-census.log"; }
# A one-log mutant rides the conforming census log, so only the mutated half is under test.
half() { printf '%s %s ' "$TMP/$1-locality.log" "$TMP/good-census.log"; }

echo "### the real grammar"
# Neither row decides anything: they prove the emitter accepts what the runner really writes,
# and that the R5 path this file extends still emits.
if [ -r "$SESSION/interior-locality.log" ] && [ -r "$SESSION/interior-census.log" ]; then
  emits "the real R8 session logs are accepted" "### Preregistered decisions (A1)" \
    -- "$SESSION/interior-locality.log" "$SESSION/interior-census.log"
else
  echo "  SKIP accepted-grammar row: no R8 session logs at $SESSION (not measured yet)"
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

echo "### the emitted decision surface"
emits "the axis is stated, with the rotation's preregistered signed rule" \
  "under one signed rule (87/96)" -- $(sess good)
emits "lane facts come off the ARM lines" \
  "| \`k19@128\` | \`eval_lsb_pair_cached_128_lb\` | 72 | 7 | 128 | 65536 | 31 | 151 | 19 | 14.421 | 0.063 | **14.484** |" \
  -- $(sess good)
emits "the ordered admitted prefixes and the trace are gated, and the gate says so" \
  "all 12 lanes; grids gated against \`--log-trace 24\`" -- $(sess good)
emits "an adjacent step divides by the removals delta off the two ARM lines" \
  "| \`k19@128\` − \`k18@128\` | 19 | +1 | +2 | **-0.050** | -0.050 … -0.050 | 96/96 | **WIN** | -25.03 |" \
  -- $(sess good)
emits "an adjacent step that costs time is a signed LOSS" \
  "| \`k20@128\` − \`k19@128\` | 20 | +1 | +2 | **+0.096** | +0.095 … +0.105 | 96/96 | **LOSS** | +48.10 |" \
  -- $(sess good)
emits "the cumulative row divides by 2(n-16) removals, taken off the ARM lines" \
  "| \`k19@128\` | 19 | 31 | 6 | **-0.350** | -0.352 … -0.347 | 96/96 | **WIN** | -58.29 |" \
  -- $(sess good)
emits "the R4-frozen band is the HARD gate and reports IN" \
  "| \`control@256\` | 16.624 | 16.624 | -0.00 % | **IN** |" -- $(sess good)
emits "the R5-session anchors are context, report-only" \
  "| \`hot16@128\` | 14.834 | 14.717 | +0.80 % |" -- $(sess good)
emits "the flank is computed per anchor lane against the scaled threshold" \
  "| \`hot16@128\` | 14.830 | 14.832 | 0.002 | 0.074 | **PASS** |" -- $(sess good)
emits "the eight adjacent signs are printed verbatim as the monotonicity evidence" \
  "first: \`− − − + + + + +\` (WIN WIN WIN LOSS LOSS LOSS LOSS LOSS)" -- $(sess good)
emits "the winner is the most negative cumulative median among the signed WINs" \
  "- winner: **\`k19@128\`** (K = 19, C = 31) at -0.350 ms vs \`hot16@128\`, 96/96 on-sign" \
  -- $(sess good)
emits "the first loser is the smallest K whose cumulative contrast is a signed LOSS" \
  "- first loser: **\`k21@128\`** (K = 21, C = 33) at +0.100 ms, 96/96 on-sign" -- $(sess good)
emits "the axis is right-censored at the top measured point" \
  "the axis is RIGHT-CENSORED at \`k24@128\`: K = 24 is the largest measured point" \
  -- $(sess good)
emits "the selection is labelled as the locality one" "**\`locality\` — SELECTION**" \
  -- $(sess good)
emits "census carries the same rows, labelled diagnostic-only" \
  "**\`census\` — diagnostic only — alters nothing (A1)**" -- $(sess good)
emits "census's own winner is reported as context" \
  "- winner: **\`k18@128\`** (K = 18, C = 30) at -0.300 ms" -- $(sess good)

echo "### the ncu manifest (A7)"
emits "the incumbent is in the capture set" \
  "NCU-CAPTURE lane=hot16@128 orders=census,locality roles=incumbent" -- $(sess good)
emits "the locality winner is in the capture set" \
  "NCU-CAPTURE lane=k19@128 orders=census,locality roles=winner" -- $(sess good)
emits "the locality first loser is in the capture set" \
  "NCU-CAPTURE lane=k21@128 orders=census,locality roles=first-loser" -- $(sess good)
emits "the censoring endpoint is in the capture set" \
  "NCU-CAPTURE lane=k24@128 orders=census,locality roles=censoring-endpoint" -- $(sess good)
# Census is diagnostic only (A1), so its winner k18 enters the manifest ONLY if the selection
# leaked into it — which is exactly the failure this row is here to see.
absent "the census winner does not enter the capture set" \
  "NCU-CAPTURE lane=k18@128" -- $(sess good)

echo "### the signed threshold, at it and one below it"
emits "87/96 negative is a signed WIN" \
  "- winner: **\`k17@128\`** (K = 17, C = 29) at -0.100 ms vs \`hot16@128\`, 87/96 on-sign" \
  -- $(sess sign-at-threshold)
emits "86/96 negative is a WASH, in the same direction" \
  "first: \`− + + + + + + +\` (WASH LOSS LOSS LOSS LOSS LOSS LOSS LOSS)" \
  -- $(sess sign-below-threshold)
emits "a WASH selects nothing" \
  "- winner: **none** — no interior point wins over \`hot16@128\` under the signed rule" \
  -- $(sess sign-below-threshold)

echo "### the tie-break and the deduplication"
emits "two lanes tie on the FULL-PRECISION median (k19)" \
  "| \`k19@128\` | 19 | 31 | 6 | **-0.590** | -0.684 … -0.492 | 96/96 | **WIN** | -98.33 |" \
  -- $(sess tie-smaller-k)
emits "two lanes tie on the FULL-PRECISION median (k22)" \
  "| \`k22@128\` | 22 | 34 | 12 | **-0.590** | -0.684 … -0.492 | 96/96 | **WIN** | -49.17 |" \
  -- $(sess tie-smaller-k)
emits "the tie breaks toward the smaller K" \
  "- winner: **\`k19@128\`** (K = 19, C = 31) at -0.590 ms" -- $(sess tie-smaller-k)
emits "one lane in two roles is one manifest line" \
  "NCU-CAPTURE lane=k24@128 orders=census,locality roles=censoring-endpoint,first-loser" \
  -- $(sess tie-smaller-k)

echo "### right-censoring and A7's fallback capture set"
emits "no cumulative LOSS means no first loser" "- first loser: **none**" -- $(sess no-loser)
emits "with no first loser the capture set takes the axis midpoint" \
  "NCU-CAPTURE lane=k20@128 orders=census,locality roles=axis-midpoint" -- $(sess no-loser)
absent "A7's fallback set names the midpoint INSTEAD of the winner" \
  "roles=winner" -- $(sess no-loser)
emits "nothing winning means the incumbent stands" \
  "- winner: **none** — no interior point wins over \`hot16@128\` under the signed rule, so the incumbent stands." \
  -- $(sess no-winner)
emits "the first loser can be the first step" \
  "- first loser: **\`k17@128\`** (K = 17, C = 29)" -- $(sess no-winner)

echo "### the session-validity rules (A6)"
rejects "an out-of-band R4-frozen anchor invalidates the session" \
  "session invalid" -- $(sess anchor-out-of-band)
invalidated "the invalid session prints its tables and selects no capture set" \
  "**NOT AUTHORITATIVE**" "NCU-CAPTURE" -- $(sess anchor-out-of-band)
emits "a drifting anchor lane trips the flank rule" \
  "| \`hot16@128\` | 14.830 | 15.132 | 0.302 | 0.074 | **TRIP** |" -- $(sess flank-tripped)
emits "a tripped flank says what it calls for" \
  "**FLANK TRIPPED (A6)**" -- $(sess flank-tripped)
absent "a held session raises neither banner" \
  "FLANK TRIPPED|SESSION INVALID" -- $(sess good)

echo "### the log contract, fail-closed (A5)"
rejects "one order alone decides nothing" \
  "preregistered on EXACTLY both term orders" -- "$TMP/good-locality.log"
rejects "--order cannot narrow the interior path" \
  "\`--order\` cannot narrow it" -- --order locality $(sess good)
rejects "an order nobody preregistered" \
  "this log set carries census, reverse" -- $(half unknown-order)
rejects "a session recorded at another --log-trace" \
  "preregistered at \`--log-trace 24\`" -- $(sess wrong-trace)
rejects "a session at another warmup" \
  "preregistered at 96 rounds / 12 warmup" -- $(sess wrong-warmup)
rejects "a session at another round count" \
  "preregistered at 96 rounds / 12 warmup" -- $(sess wrong-rounds)
rejects "a lane the rotation does not name" \
  "lane set is not the interior rotation — missing ['k19@128'], unexpected ['k19b@128']" \
  -- $(half lane-unknown)
rejects "two lanes carrying one lane's data" \
  "BIT-IDENTICAL samples in every round" -- $(half lane-aliased)
rejects "one lane's ARM line carrying its neighbour's plan" \
  "lane k22@128 admits 21 sources but its name claims K = 22" -- $(sess lane-plan-duplicated)
rejects "a reversal among two equal-ref sources" \
  "the admitted prefix is not the canonical one" -- $(sess ids-reversed)
rejects "a step that is not one BF source at refs 3" \
  "moves (admitted, C, removals) by (1, 1, 3)" -- $(sess axis-broken)
rejects "an ARM line without its admitted-id list" \
  "the two grammars are not interchangeable" -- $(half arm-without-ids)
rejects "the lanes ran in a fixed order every round" \
  "the rotation is not balanced" -- $(sess rotation-fixed)
rejects "no done trailer" "the run did not finish, or the log is truncated" \
  -- $(half no-trailer)
rejects "renumbered rounds" "expected the consecutive run 12…107" -- $(half renumbered)
rejects "one lane is one sample short" "incomplete rounds are not droppable" \
  -- $(half sample-dropped)
rejects "a duplicated (round, lane) sample" \
  "duplicate sample for order=locality round=20 lane=k21@128" -- $(half sample-duplicated)
rejects "a lane whose samples name another body" \
  "ran \`eval_lsb_pair_128_lb\` but its ARM line declares" -- $(half kernel-forged)
rejects "one log relabelled as another rotation" \
  "carries FRONTIER-INTERIOR and ['FRONTIER-FACTORIAL']" -- $(half wrong-tag)
rejects "both logs relabelled: they are then judged under the R5 rules, which reject them" \
  "lane set is not the primary frontier rotation" -- $(sess wrong-tag)
rejects "an R4 factorial log in the set" \
  "carries FRONTIER-INTERIOR and ['CACHE-FACTORIAL']" -- $(sess good) "$TMP/not-r8.log"

printf 'fixture matrix: %d passed, %d failed, %d skipped\n' "$pass" "$fail" "$skip"
exit $(( fail > 0 ))
