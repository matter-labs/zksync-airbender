#!/usr/bin/env bash
# v3 R9 gate-first-reorder fixture matrix. Every row states the RULE or the GUARD it exercises; a
# fixture that stops behaving the way it does here means the emitter's decision surface moved.
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
# A rejected run emits nothing, so the exit status is checked FIRST: otherwise a crashing emitter
# would pass every one of these rows for the wrong reason.
absent() {
  local name=$1 nope=$2; shift 3
  local out rc
  out=$($E "$@" 2>/dev/null); rc=$?
  if [ "$rc" != 0 ]; then printf 'FAIL(rejected) %s\n' "$name"; fail=$((fail+1)); return; fi
  if printf '%s' "$out" | grep -qE -- "$nope"; then
    printf 'FAIL(outcome) %s\n  must NOT emit: %s\n' "$name" "$nope"; fail=$((fail+1))
  else pass=$((pass+1)); fi
}

# accepts <name> <want-on-stdout> -- <args...>
# The ACCEPTED-GRAMMAR row, and the only one that separates grammar from validity: the emitter must
# parse what the runner really writes and reach its decision tables. Whether that session's anchors
# hold is a fact about the machine that day, not about the grammar — an unsoaked pass legitimately
# trips the R4-frozen band — so a non-zero status is tolerated ONLY when the printed record says
# which rule stopped it. A crash prints nothing and still fails the row.
accepts() {
  local name=$1 want=$2; shift 3
  local out rc
  out=$($E "$@" 2>/dev/null); rc=$?
  if ! printf '%s' "$out" | grep -qF -- "$want"; then
    printf 'FAIL(grammar) %s\n  want on stdout: %s\n' "$name" "$want"; fail=$((fail+1)); return
  fi
  if [ "$rc" != 0 ] && ! printf '%s' "$out" | grep -qF -- "SESSION INVALID"; then
    printf 'FAIL(rejected) %s\n' "$name"; fail=$((fail+1)); return
  fi
  pass=$((pass+1))
}

# invalidated <name> <want-on-stdout> <forbidden-on-stdout> -- <args...>
# The invalidation is BOTH a non-zero status (reason on stderr) and a printed record that names
# itself not authoritative. A row checking only one of the two would pass on an emitter that
# dropped the other, so this one checks both.
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
# None of these rows decides anything: they prove the emitter accepts what the runner really
# writes, and that the two paths this file rides beside still emit.
if [ -r "$SESSION/reorder-locality.log" ] && [ -r "$SESSION/reorder-census.log" ]; then
  accepts "the real R9 session logs are accepted through every structural gate" \
    "### Preregistered decisions" \
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

echo "### the emitted decision surface"
emits "the rung states its one L1 configuration and its signed rule" \
  "at ONE L1 configuration (16 % on every hinted local symbol)" -- $(sess good)
emits "the applied carveout is read off the log, per order" \
  "| \`locality\` | \`good-locality.log\` | 16 % \`eval_lsb_pair_cached_128_lb\`, 16 % \`eval_lsb_pair_cached_reorder_128_lb\`, 16 % \`eval_lsb_pair_cached_reorder_128\` |" \
  -- $(sess good)
emits "lane facts — registers, occupancy tier, body, plan — come off the ARM lines" \
  "| \`reorder-hot16@128\` | \`eval_lsb_pair_cached_reorder_128_lb\` | 70 | 7 | 128 | 65536 | 28 | 145 | 16 | 14.571 | 0.063 | **14.634** |" \
  -- $(sess good)
emits "the bodies, the prefixes, the trace and the one-plan premise are gated, and it says so" \
  "grids gated against \`--log-trace 24\`, all 6 lanes; the three cached lanes are gated as ONE plan on three bodies" \
  -- $(sess good)
emits "row 1 is THE verdict row, paired and signed" \
  "| 1 | \`reorder-hot16@128\` − \`hot16@128\` | \`hot16@128\` | **-0.198** | -0.207 … -0.193 | -1.33 % | 96/96 | **WIN** | same class |" \
  -- $(sess good)
emits "row 2 is the envelope verdict, and its occupancy tier is NOT the incumbent's" \
  "| 2 | \`reorder-hot16-free@128\` − \`hot16@128\` | \`hot16@128\` | **-0.348** | -0.357 … -0.343 | -2.35 % | 96/96 | **WIN** | **8 v 7 blocks/SM — NOT occupancy-neutral** |" \
  -- $(sess good)
emits "row 3 is labelled as the BUNDLED envelope delta, which it cannot decompose" \
  "the pure envelope delta — occupancy + twiddle remat BUNDLED: the unbounded body collapses the remat AND gains a block, and this row cannot separate them" \
  -- $(sess good)
emits "row 4 is the reordered machinery floor, against the bound-matched control" \
  "| 4 | \`reorder-cache0@128\` − \`control_lb@128\` | \`control_lb@128\` | **+0.671** | +0.651 … +0.679 | +4.09 % | 96/96 | **LOSS** |" \
  -- $(sess good)
emits "row 5 is capture under the reorder, against that floor" \
  "| 5 | \`reorder-hot16@128\` − \`reorder-cache0@128\` | \`reorder-cache0@128\` | **-2.436** | -2.454 … -2.417 | -14.27 % | 96/96 | **WIN** |" \
  -- $(sess good)
emits "the R4-frozen band is the HARD gate and reports IN" \
  "| \`control@256\` | 16.624 | 16.624 | -0.00 % | **IN** |" -- $(sess good)
emits "the flank is computed per anchor lane against the scaled threshold" \
  "| \`hot16@128\` | 14.840 | 14.842 | 0.002 | 0.074 | **PASS** |" -- $(sess good)
# The reorder bodies are what the rung is testing; a drift sentinel that is itself under test
# would absorb the drift it exists to report.
absent "the bodies under test are not flank sentinels" \
  "^\| .reorder-hot16@128. \| 14\.6" -- $(sess good)
emits "the static register facts are read off the log, not written in the emitter" \
  "\`hot16@128\` 72 regs / 7 blocks/SM, \`reorder-hot16@128\` 70 / 7, \`reorder-hot16-free@128\` 64 / 8" \
  -- $(sess good)

echo "### the verdict row's preregistered gate and the outcome matrix"
emits "a WIN in both orders clears wash-or-better" \
  "⇒ the preregistered gate is **MET** — the gate-first body costs no time at the incumbent's plan, and wins it in both orders." \
  -- $(sess good)
emits "a register cut plus wash-or-better funds R10" \
  "| reduced | wash-or-better | **funds R10** — the register cut is real and costs no time | **⇐ SELECTED** |" \
  -- $(sess good)
emits "a WASH on the verdict row still clears the gate — it is wash-OR-better" \
  "⇒ the preregistered gate is **MET** — the gate-first body costs no time at the incumbent's plan." \
  -- $(sess verdict-wash)
emits "and a wash still selects the R10-funding cell" \
  "| reduced | wash-or-better | **funds R10** — the register cut is real and costs no time | **⇐ SELECTED** |" \
  -- $(sess verdict-wash)
emits "a LOSS on the verdict row fails the gate" \
  "⇒ the preregistered gate is **NOT met** — the gate-first body LOSES time at the incumbent's plan." \
  -- $(sess verdict-loss)
emits "and the register cut does not rescue it" \
  "| reduced | LOSS | **does NOT fund R10** — the cut is paid for in time | **⇐ SELECTED** |" \
  -- $(sess verdict-loss)
emits "one order's win cannot carry a gate preregistered on BOTH" \
  "| \`census\` | **+0.252** | 96/96 | **LOSS** | NO |" -- $(sess verdict-split)
emits "so a split session fails the gate" \
  "| reduced | LOSS | **does NOT fund R10** — the cut is paid for in time | **⇐ SELECTED** |" \
  -- $(sess verdict-split)
emits "unchanged registers with a time win is performance-only" \
  "| unchanged | WIN | **performance-only, does NOT fund R10** — a time win with no register headroom to spend | **⇐ SELECTED** |" \
  -- $(sess regs-unchanged)
emits "neither a register cut nor a time win records nothing" \
  "| unchanged | wash or LOSS | **nothing to record** — neither a register cut nor a time win | **⇐ SELECTED** |" \
  -- $(sess regs-unchanged-loss)

echo "### the signed threshold, at it and one below it"
emits "87/96 negative is a signed WIN" "| \`locality\` | **-0.100** | 87/96 | **WIN** | yes |" \
  -- $(sess sign-at-threshold)
emits "86/96 negative is a WASH, in the same direction" \
  "| \`locality\` | **-0.100** | 86/96 | **WASH** | yes |" -- $(sess sign-below-threshold)

echo "### the ncu capture manifest"
emits "the incumbent is captured" \
  "NCU-CAPTURE lane=hot16@128 orders=census,locality roles=incumbent body=eval_lsb_pair_cached_128_lb regs=72" \
  -- $(sess good)
emits "the bounded gate-first body is captured, with its own register count" \
  "NCU-CAPTURE lane=reorder-hot16@128 orders=census,locality roles=bounded-reorder body=eval_lsb_pair_cached_reorder_128_lb regs=70" \
  -- $(sess good)
emits "the unbounded gate-first body is captured, with its own register count" \
  "NCU-CAPTURE lane=reorder-hot16-free@128 orders=census,locality roles=unbounded-reorder body=eval_lsb_pair_cached_reorder_128 regs=64" \
  -- $(sess good)
# The set is FIXED (amendment A7): no timing outcome may add a lane to it or take one away, which
# is exactly what a manifest derived from the verdict would do.
absent "the machinery floor and the controls are not in the capture set" \
  "NCU-CAPTURE lane=(reorder-cache0|control)" -- $(sess good)
emits "a LOSING session captures the same three lanes" \
  "NCU-CAPTURE lane=reorder-hot16@128 orders=census,locality roles=bounded-reorder body=eval_lsb_pair_cached_reorder_128_lb regs=70" \
  -- $(sess verdict-loss)

echo "### the session-validity rules"
rejects "an out-of-band R4-frozen anchor invalidates the session" \
  "session invalid" -- $(sess anchor-out-of-band)
invalidated "the invalid session prints its tables and selects no capture set" \
  "**NOT AUTHORITATIVE**" "NCU-CAPTURE" -- $(sess anchor-out-of-band)
emits "a drifting anchor lane trips the flank rule" \
  "| \`hot16@128\` | 14.840 | 15.142 | 0.302 | 0.074 | **TRIP** |" -- $(sess flank-tripped)
emits "a tripped flank says what it calls for" "**FLANK TRIPPED**" -- $(sess flank-tripped)
absent "a held session raises neither banner" "FLANK TRIPPED|SESSION INVALID" -- $(sess good)

echo "### the carveout grammar (the hinted SET is part of the accepted grammar)"
rejects "a missing per-symbol echo" \
  "the percent and the SET are the configuration under test" -- $(sess echo-missing)
rejects "an echo for a symbol the rotation does not hint" \
  "the percent and the SET are the configuration under test" -- $(sess echo-extra)
rejects "one symbol steered to another percent" \
  "'33%:eval_lsb_pair_cached_reorder_128_lb'" -- $(sess echo-wrong-pct)
rejects "the echoes in another order" \
  "the percent and the SET are the configuration under test" -- $(sess echo-reordered)
rejects "one symbol echoed twice" \
  "the percent and the SET are the configuration under test" -- $(sess echo-duplicated)
rejects "no carveout-symbols line at all" \
  "carries 0 \`carveout symbols\` lines, expected exactly one" -- $(sess symbols-missing)
rejects "two carveout-symbols lines" \
  "carries 2 \`carveout symbols\` lines, expected exactly one" -- $(sess symbols-twice)
rejects "the carveout-symbols count disagreeing with its own list" \
  "\`carveout symbols    2 local (" -- $(sess symbols-count-wrong)
rejects "the carveout-symbols list disagreeing with the per-symbol echoes" \
  "the set line and the per-symbol echoes must describe one configuration" -- $(sess symbols-disagree)
rejects "a carveout line that is neither grammar" \
  "is not the harness's carveout grammar" -- $(sess echo-malformed)

echo "### the log contract, fail-closed"
rejects "one order alone decides nothing" \
  "preregistered on EXACTLY both term orders" -- "$TMP/good-locality.log"
rejects "--order cannot narrow the reorder path" \
  "\`--order\` cannot narrow it" -- --order locality $(sess good)
rejects "an order nobody preregistered" \
  "this log set carries census, reverse" -- $(half unknown-order)
rejects "both term orders in one log" \
  "one log is one process and one process runs one term order" -- "$TMP/two-orders-locality.log"
rejects "a session recorded at another --log-trace" \
  "preregistered at \`--log-trace 24\`" -- $(sess wrong-trace)
rejects "a session at another warmup" \
  "preregistered at 96 rounds / 6 warmup" -- $(sess wrong-warmup)
rejects "a session at another round count" \
  "preregistered at 96 rounds / 6 warmup" -- $(sess wrong-rounds)
rejects "a lane the rotation does not name" \
  "lane set is not the reorder rotation — missing ['reorder-hot16@128'], unexpected ['reorder-hot17@128']" \
  -- $(half lane-unknown)
# The BODY pin. Every count is unchanged and the three cached lanes share one plan, so this is the
# only gate that can see a lane launched on the incumbent's body under a reorder label.
rejects "a reorder lane declaring the incumbent's body" \
  "the three cached lanes carry ONE plan, so nothing but this pin can see a swapped body" \
  -- $(sess body-forged)
rejects "a reorder lane pricing a different plan from the incumbent it is contrasted against" \
  "the verdict row contrasts BODIES at one plan" -- $(sess plan-mismatch)
rejects "a reversal among two equal-ref sources" \
  "the admitted prefix is not the canonical one" -- $(sess ids-reversed)
rejects "two lanes carrying one lane's data" \
  "BIT-IDENTICAL samples in every round" -- $(half lane-aliased)
rejects "a lane whose samples name another body" \
  "ran \`eval_lsb_pair_cached_reorder_128_lb\` but its ARM line declares" -- $(half kernel-forged)
rejects "one lane's register count moving between the two orders' logs" \
  "these two logs are two builds" -- $(half regs-cross-order)
rejects "an ARM line without its admitted-id list" \
  "the two grammars are not interchangeable" -- $(half arm-without-ids)
rejects "the lanes ran in a fixed order every round" \
  "the rotation is not balanced" -- $(sess rotation-fixed)
rejects "no done trailer" "the run did not finish, or the log is truncated" -- $(half no-trailer)
rejects "renumbered rounds" "expected the consecutive run 6…101" -- $(half renumbered)
rejects "one lane is one sample short" "incomplete rounds are not droppable" -- $(half sample-dropped)
rejects "a duplicated (round, lane) sample" \
  "duplicate sample for order=locality round=20 lane=reorder-hot16@128" -- $(half sample-duplicated)
rejects "one log relabelled as another rotation" \
  "carries FRONTIER-INTERIOR and ['REORDER']" -- $(half wrong-tag)
rejects "both logs relabelled: they are then judged under the interior rules, which reject them" \
  "lane set is not the interior rotation" -- $(sess wrong-tag)
rejects "an R4 factorial log in the set" \
  "carries REORDER and ['CACHE-FACTORIAL']" -- $(sess good) "$TMP/not-r9.log"

printf 'fixture matrix: %d passed, %d failed, %d skipped\n' "$pass" "$fail" "$skip"
exit $(( fail > 0 ))
