#!/usr/bin/env bash
# v3 R6 carveout-probe fixture matrix. Every row states the RULE or the GUARD it exercises;
# a fixture that stops behaving the way it does here means the emitter's preregistered
# decision surface moved.
#
# SELF-GENERATING: the logs are derived data, so `make_fixtures.py` writes them into a
# mktemp dir at run time and they are removed on exit. Nothing here needs a file that is not
# in the tracked tree — except the ACCEPTED-GRAMMAR row, which replays the real session logs
# if they are present and prints a SKIP note if they are not (a clean checkout has no
# `.agents/` tree; that row is the only thing in the suite that can be skipped, and it never
# fails the lane).
#
# Run from anywhere:  bash gpu/gkr_uniskip_bench/tools/r6_fixtures/check.sh
set -uo pipefail

DIR=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$DIR/../../../.." && pwd)
E=${E:-"python3 $ROOT/gpu/gkr_uniskip_bench/tools/r6_probe_table.py"}
# Overridable so the clean-checkout SKIP path is itself testable.
SESSION=${SESSION:-$ROOT/.agents/sdd/2026-08-10-v3-r6}
pass=0
fail=0
skip=0

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
python3 "$DIR/make_fixtures.py" "$TMP" || { echo "FAIL: fixture generation"; exit 1; }

# rejects <name> <expected-substring> -- <logs...>
rejects() {
  local name=$1 want=$2; shift 3
  local out rc
  out=$($E "$@" 2>&1 >/dev/null); rc=$?
  if [ "$rc" = 0 ]; then printf 'FAIL(accepted) %s\n' "$name"; fail=$((fail+1)); return; fi
  if printf '%s' "$out" | grep -qF -- "$want"; then pass=$((pass+1));
  else printf 'FAIL(message) %s\n  want: %s\n  got:  %s\n' "$name" "$want" "$out"; fail=$((fail+1)); fi
}

# emits <name> <expected-substring> -- <logs...>
emits() {
  local name=$1 want=$2; shift 3
  local out rc
  out=$($E "$@" 2>&1); rc=$?
  if [ "$rc" != 0 ]; then printf 'FAIL(rejected) %s\n  %s\n' "$name" "$(printf '%s' "$out" | tail -1)"; fail=$((fail+1)); return; fi
  if printf '%s' "$out" | grep -qF -- "$want"; then pass=$((pass+1));
  else printf 'FAIL(outcome) %s\n  want: %s\n' "$name" "$want"; fail=$((fail+1)); fi
}

# absent <name> <forbidden-extended-regex> -- <logs...>
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

sess() { echo "$TMP/$1-off1.log $TMP/$1-on1.log $TMP/$1-on2.log $TMP/$1-off2.log"; }

echo "### the real grammar"
# The one row that reads outside the tracked tree. It decides nothing — it proves the
# emitter accepts what the runner actually writes (the applied-hint echo line, the ARM id
# lists, the rotation, the trailer) at the pinned configuration.
if [ -r "$SESSION/session-off1.log" ] && [ -r "$SESSION/session-on1.log" ] \
   && [ -r "$SESSION/session-on2.log" ] && [ -r "$SESSION/session-off2.log" ]; then
  emits "the real session logs are accepted under the pinned contract" \
    "| \`control@256\` | \`eval_lsb_pair\` |" \
    -- "$SESSION/session-off1.log" "$SESSION/session-on1.log" \
       "$SESSION/session-on2.log" "$SESSION/session-off2.log"
else
  echo "  SKIP accepted-grammar row: no session logs at $SESSION (clean checkout)"
  skip=$((skip+1))
fi

echo "### P1 decision edges"
emits "k32 wins in BOTH hinted processes ⇒ (a)" \
  "FRONTIER MOVED" -- $(sess frontier-moved)
emits "(a) sizes the moved frontier from the ARM lines" \
  "frontier position = **C = 44**" -- $(sess frontier-moved)
emits "(a) ⇒ the manifest carries the winning lane, hinted" \
  "NCU-CAPTURE lane=k32@128 hint=on carveout-hint=16 order=locality" -- $(sess frontier-moved)
emits "(a) ⇒ the manifest carries the winning lane, unhinted" \
  "NCU-CAPTURE lane=k32@128 hint=off carveout-hint=default order=locality" -- $(sess frontier-moved)
emits "(a) ⇒ the manifest carries hot16 as well" \
  "NCU-CAPTURE lane=hot16@128 hint=on" -- $(sess frontier-moved)
# The 90 % literal, pinned from both sides: same negative median, one round of on-sign
# apart. Nothing else in the matrix would notice the threshold moving.
emits "90/100 on-sign is a win (the signed threshold, met)" \
  "| on1 | 16 | \`k32@128\` | 44 | **-0.020** | 90/100 | **win** |" -- $(sess sign-threshold-met)
emits "90/100 on-sign moves the frontier" \
  "FRONTIER MOVED" -- $(sess sign-threshold-met)
emits "89/100 on-sign is a wash (the signed threshold, missed)" \
  "| on1 | 16 | \`k32@128\` | 44 | **-0.020** | 89/100 | **wash** |" -- $(sess sign-threshold-miss)
absent "89/100 on-sign does not move the frontier" \
  "FRONTIER MOVED" -- $(sess sign-threshold-miss)
emits "the top lane wins too ⇒ right-censored" \
  "right-censored at k40" -- $(sess right-censored)
emits "right-censored frontier is sized at k40's C" \
  "frontier position = **C = 52**" -- $(sess right-censored)
emits "no win, Δk24 halves against both adjacent offs ⇒ (b)" \
  "CAPACITY-PRICED CONFIRMED — the knee is carveout-sensitive" -- $(sess capacity-priced)
emits "half-shrink boundary, just inside ⇒ (b)" \
  "CAPACITY-PRICED CONFIRMED" -- $(sess half-shrink-in)
emits "half-shrink boundary, just outside ⇒ (c)" \
  "carveout is not the binding capacity term" -- $(sess half-shrink-out)
emits "half-shrink is PAIRWISE: one pair shrinking is not enough" \
  "carveout is not the binding capacity term" -- $(sess half-shrink-split)
absent "the split pair cannot claim (b)" "CAPACITY-PRICED" -- $(sess half-shrink-split)
emits "deltas unchanged ⇒ (c)" \
  "carveout is not the binding capacity term" -- $(sess wash)
absent "(c) must not also claim a moved frontier" \
  "FRONTIER MOVED|CAPACITY-PRICED" -- $(sess wash)
emits "a win in ONE hinted process is MIXED, not (a)" \
  "**MIXED** — \`k32@128\` wins over \`hot16@128\` in on1 only" -- $(sess mixed-on)
emits "MIXED falls through to (b)/(c)" \
  "carveout is not the binding capacity term" -- $(sess mixed-on)
absent "MIXED does not satisfy (a)" \
  "FRONTIER MOVED" -- $(sess mixed-on)
# The manifest is (a)-only: an unmoved frontier has nothing to capture.
absent "no manifest without (a)" "NCU-CAPTURE" -- $(sess wash)

echo "### the stability precondition"
emits "k24 WASH in an off process ⇒ no verdict" \
  "PROBE UNSTABLE — off processes do not reproduce the R5 frontier; no verdict" \
  -- $(sess unstable-off)
absent "an unstable probe suppresses P1 and P2" \
  "FRONTIER MOVED|CAPACITY-PRICED|not the binding capacity term|^### P2" \
  -- $(sess unstable-off)
emits "the tables still print under an unstable probe" \
  "### Paired deltas vs \`hot16@128\`" -- $(sess unstable-off)

echo "### P2"
emits "both pairs stable and both δ negative ⇒ improvement" \
  "hot16 improves under the hint (control-bridged, in-rotation)" -- $(sess wash)
emits "P2 always states its scope" \
  "locality/shipping order only; NOT comparable to the R5 bar layers." -- $(sess wash)
emits "a 0.2 ms flank disagreement makes that pair unstable" \
  "| off1/on1 | 16.624 | 16.824 | 0.200 | **unstable** |" -- $(sess flank-fail)
emits "an unstable pair withholds the P2 verdict" \
  "P2 verdict withheld" -- $(sess flank-fail)
absent "an unstable pair cannot claim the improvement" \
  "hot16 improves under the hint" -- $(sess flank-fail)

echo "### sanity"
emits "control@256 3 % off the anchor ⇒ banner" \
  "SANITY: anchor out of band — absolutes are session-scoped" -- $(sess sanity-out)
emits "the banner is NON-fatal: the decision still prints" \
  "carveout is not the binding capacity term" -- $(sess sanity-out)
absent "an in-band session prints no banner" \
  "SANITY: anchor out of band" -- $(sess frontier-moved)

echo "### the pinned contract"
PIN="a log outside the pinned contract is a different experiment"
rejects "one process ran the census order" "$PIN" -- $(sess mixed-order)
rejects "the whole session ran the census order" "$PIN" -- $(sess census-order)
rejects "the hinted processes ran a hint other than 16" "$PIN" -- $(sess hint-not-16)
rejects "the session ran a round count other than 100" "$PIN" -- $(sess rounds-not-100)

echo "### the applied-hint corroboration"
rejects "schedule says 16, the process applied 25" \
  "the schedule line and the applied hint disagree" -- $(sess echo-mismatch)
rejects "a hinted process carries no applied-hint echo" \
  "carries no applied-hint echo line" -- $(sess echo-missing)
rejects "an unhinted process echoes an applied hint" \
  "the schedule line and the applied hint disagree" -- $(sess echo-spurious)

echo "### fail-closed"
rejects "hint sequence on/off/on/off" \
  "expected [default, 16, 16, default] with the SAME N" -- $(sess bad-sequence)
rejects "on2 ran unhinted" \
  "expected [default, 16, 16, default] with the SAME N" -- $(sess on2-unhinted)
rejects "one lane is one sample short" \
  "expected the 5 probe lanes" -- $(sess short-lane)
rejects "three logs" \
  "expects exactly 4 logs in session order" \
  -- "$TMP/wash-off1.log" "$TMP/wash-on1.log" "$TMP/wash-on2.log"
rejects "five logs" \
  "expects exactly 4 logs in session order" -- $(sess wash) "$TMP/wash-off1.log"
rejects "another rotation's log (the R5 frontier grammar)" \
  "before the schedule line — the lane facts cannot be bound" \
  -- "$TMP/not-a-probe.log" "$TMP/not-a-probe.log" "$TMP/not-a-probe.log" \
     "$TMP/not-a-probe.log"

printf 'fixture matrix: %d passed, %d failed, %d skipped\n' "$pass" "$fail" "$skip"
exit $(( fail > 0 ))
