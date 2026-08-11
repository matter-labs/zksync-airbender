#!/usr/bin/env bash
# v3 R7 segmented-pair fixture matrix. Every row states the RULE or the GUARD it exercises; a
# fixture that stops behaving the way it does here means the emitter's decision surface moved.
#
# SELF-GENERATING: the logs are derived data, so `make_fixtures.py` writes them into a mktemp
# dir at run time and they are removed on exit. Nothing here needs a file that is not in the
# tracked tree — except the ACCEPTED-GRAMMAR row, which replays the real session logs if they
# are present and prints a SKIP note if they are not (a clean checkout has no `.agents/` tree;
# that row is the only thing in the suite that can be skipped, and it never fails the lane).
#
# Run from anywhere:  bash gpu/gkr_uniskip_bench/tools/r7_fixtures/check.sh
set -uo pipefail

DIR=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$DIR/../../../.." && pwd)
E=${E:-"python3 $ROOT/gpu/gkr_uniskip_bench/tools/r7_table.py"}
# Overridable so the clean-checkout SKIP path is itself testable.
SESSION=${SESSION:-$ROOT/.agents/sdd/2026-08-10-v3-r7}
pass=0
fail=0
skip=0

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
python3 "$DIR/make_fixtures.py" "$TMP" || { echo "FAIL: fixture generation"; exit 1; }

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

# with_oracle <oracle-path> <rejects-args...> — the oracle override is exported explicitly
# rather than prefixed onto the call, so it cannot leak into a later row.
with_oracle() {
  local path=$1; shift
  export R7_SEG_ORACLE=$path
  rejects "$@"
  unset R7_SEG_ORACLE
}

# The eight logs of one fixture session, in POSITIONAL order.
sess() {
  local n=$1 p
  for p in reanchor-census reanchor-locality smem-locality smem-census gmem-locality \
           gmem-census attr-cv64 attr-cv100; do
    printf '%s ' "$TMP/$n-$p.log"
  done
}

echo "### the real grammar"
# The one row that reads outside the tracked tree. It decides nothing — it proves the emitter
# accepts what the runner actually writes.
have_real=1
for p in reanchor-census reanchor-locality smem-locality smem-census gmem-locality \
         gmem-census attr-cv64 attr-cv100; do
  [ -r "$SESSION/session-$p.log" ] || have_real=0
done
if [ "$have_real" = 1 ]; then
  emits "the real session logs are accepted" "### Carrier A/B" \
    -- "$SESSION/session-reanchor-census.log" "$SESSION/session-reanchor-locality.log" \
       "$SESSION/session-smem-locality.log" "$SESSION/session-smem-census.log" \
       "$SESSION/session-gmem-locality.log" "$SESSION/session-gmem-census.log" \
       "$SESSION/session-attr-cv64.log" "$SESSION/session-attr-cv100.log"
else
  echo "  SKIP accepted-grammar row: no session logs at $SESSION (not measured yet)"
  skip=$((skip+1))
fi

echo "### the oracle is the plan's single source of truth"
emits "--seg-line renders the committed locality plan" \
  "SEG list_offset=0,46,89,132,175 cost=759,713,772,744 owners=e4:1,1,1,1;bf:3,3,3,3 hash=02dbf4b0cd52aae9 stripe=hot16" \
  -- --seg-line locality
emits "--seg-line renders the committed census plan" \
  "SEG list_offset=0,49,87,137,175 cost=783,731,749,725 owners=e4:1,1,1,1;bf:3,3,3,3 hash=e10a9e26dbf0b75d stripe=hot16" \
  -- --seg-line census
rejects "--seg-line names an order the oracle does not deal" \
  "the committed oracle carries no \`bogus\` block" -- --seg-line bogus
with_oracle "$TMP/nonexistent.json" "a missing oracle is not a pass" \
  "the committed dealer oracle is unreadable" -- $(sess good)
with_oracle "$TMP/oracle-wrong-algo.json" "an oracle with another hash algorithm" \
  "program_hash_algo is 'sha256'" -- $(sess good)
with_oracle "$TMP/oracle-no-locality.json" "an oracle missing the log's own order" \
  "the committed oracle carries no \`locality\` block, so this log's dealt plan has nothing" \
  -- $(sess good)

echo "### the emitted decision surface"
emits "the inventory states every position's pinned contract" \
  "| 5 | gmem-locality | SEG-GMEM | \`locality\` | 99 | 9 | 16% |" -- $(sess good)
emits "the dealt plan is stated per order, with the logs that carried it" \
  "| \`locality\` | smem-locality, gmem-locality | 0,46,89,132,175 | 759,713,772,744 | 1,1,1,1 | 3,3,3,3 | \`02dbf4b0cd52aae9\` |" \
  -- $(sess good)
emits "the anchor processes are named as dealing nothing" \
  "SEG-ANCHOR processes carry no dealt plan and no SEG line, as required: reanchor-census, reanchor-locality, attr-cv64, attr-cv100." \
  -- $(sess good)
emits "lane facts come off the ARM lines" \
  "| SEG-GMEM | \`seg-allrepeat-g@128\` | \`eval_lsb_seg_g\` | 72 | 7 | 128 | 65536 | 88 | 234 | 55 |" \
  -- $(sess good)
emits "per-lane medians carry eval, finalize and the sum" \
  "| smem-locality | \`seg-k40-s@128\` | 14.692 | 0.008 | **14.700** |" -- $(sess good)
emits "paired delta vs the incumbent, with C and removals from the log" \
  "| smem-locality | \`seg-k40-s@128\` | 52 | 193 | **-0.046** | 100/100 neg (≥ 90) |" \
  -- $(sess good)
emits "paired delta vs the carrier's own seg-cache0" \
  "| gmem-locality | \`seg-hot16-g@128\` | \`seg-cache0-g@128\` | **-1.300** |" -- $(sess good)
emits "machinery decomposition: publish machinery at zero capture" \
  "| gmem-locality | \`seg-cache0-g@128\` − \`seg-recompute@128\` | \`eval_lsb_seg_g\` − \`eval_lsb_seg_recompute\` | publish machinery at zero capture | **+0.400** |" \
  -- $(sess good)
emits "machinery decomposition: the accumulator-first A/B" \
  "accumulator-first reduction A/B | **+0.100** |" -- $(sess good)
emits "capture slope divides by the removals delta off the ARM lines" \
  "| smem-locality | \`seg-k40-s@128\` − \`seg-hot16-s100@128\` | 48 | **-0.350** | -7.29 |" \
  -- $(sess good)
emits "the carrier A/B is bridged over a shared anchor" \
  "| k40 | \`seg-k40-s@128\` | \`seg-k40-g@128\` | \`control@256\` | 0.000 | **stable** | 14.700 | 14.650 | **+0.050** |" \
  -- $(sess good)
emits "the census carrier row is labelled never-pooled" \
  "dealing-damage diagnostic — NEVER pooled with the locality row" -- $(sess good)
emits "the attribution contrast is the paired (hot16 - control) across hints" \
  "| attr-cv64 | 32% | **-1.924** | 100/100 neg (≥ 90) | **-0.046** |" -- $(sess good)
emits "the re-anchor row prices control@256 against its frozen median" \
  "| reanchor-locality | \`control@256\` | 16.624 | 16.624 | +0.00 % | **IN** |" -- $(sess good)
emits "R7 preregisters no closure threshold, so nothing declares a winner" \
  "Nothing here declares a winner." -- $(sess good)

echo "### the reported sign-stability count"
emits "90/100 on-sign is reported AT the ceil(0.9 N) threshold" \
  "| smem-locality | \`seg-k40-s@128\` | 52 | 193 | **-0.046** | 90/100 neg (≥ 90) |" \
  -- $(sess sign-at-threshold)
emits "89/100 on-sign is reported BELOW it" \
  "| smem-locality | \`seg-k40-s@128\` | 52 | 193 | **-0.046** | 89/100 neg (< 90) |" \
  -- $(sess sign-below-threshold)
absent "neither count is turned into a verdict" \
  "WINS|LOSES|FRONTIER MOVED" -- $(sess sign-at-threshold)

echo "### the non-fatal bands and the mechanical triggers"
emits "control@256 3 % off its frozen median ⇒ banner" \
  "ANCHOR OUT OF BAND — absolutes are session-scoped" -- $(sess anchor-out-of-band)
emits "the banner is NON-fatal: the tables still print" \
  "### Carrier A/B" -- $(sess anchor-out-of-band)
absent "an in-band session prints no banner" \
  "ANCHOR OUT OF BAND" -- $(sess good)
emits "a 0.2 ms anchor disagreement makes the bridged row unstable" \
  "| k40 | \`seg-k40-s@128\` | \`seg-k40-g@128\` | \`control@256\` | 0.200 | **unstable** |" \
  -- $(sess bridge-flank-unstable)
emits "a drifting anchor fires the Step 7 repeat trigger" \
  "REPEAT TRIGGER FIRED" -- $(sess repeat-trigger-fired)
absent "a held session fires no repeat trigger" \
  "REPEAT TRIGGER FIRED" -- $(sess good)
emits "a held session says so" \
  "no repeat trigger: every anchor lane held within 0.05 ms" -- $(sess good)

echo "### the applied carveout, per symbol"
ECHOMSG="the percent IS the configuration under test"
rejects "cv64 echoed at 16 instead of 32" "$ECHOMSG" -- $(sess echo-cv64-wrong)
rejects "cv100 echoed at 32 instead of 100" "$ECHOMSG" -- $(sess echo-cv100-wrong)
rejects "the acc symbol echoed at 100 instead of 32" "$ECHOMSG" -- $(sess echo-acc-wrong)
rejects "the machinery floor echoed at 32 instead of 16" "$ECHOMSG" -- $(sess echo-recompute-wrong)
rejects "carrier G echoed at 32 instead of 16" "$ECHOMSG" -- $(sess echo-g-wrong)
rejects "the local incumbent echoed at 32 on a rotation" "$ECHOMSG" -- $(sess echo-incumbent-wrong)
rejects "a used symbol carries no echo at all" "$ECHOMSG" -- $(sess echo-cv100-missing)
rejects "the local incumbent carries no echo" "$ECHOMSG" -- $(sess echo-incumbent-missing)
rejects "an anchor log echoes a seg symbol it never launched" "$ECHOMSG" -- $(sess echo-spurious-seg)
rejects "a rotation echoes a symbol no lane uses" "$ECHOMSG" -- $(sess echo-unused-symbol)
rejects "the attribution log at hint 32 echoed 16" "$ECHOMSG" -- $(sess echo-attr-not-32)
rejects "the attribution log at hint 100 echoed 32" "$ECHOMSG" -- $(sess echo-attr-not-100)
rejects "a second echo for one symbol" \
  "a second applied-hint echo for \`eval_lsb_seg_g\`" -- $(sess echo-doubled)
rejects "an echo line outside the harness's literal" \
  "is not the harness's applied-hint echo line" -- $(sess echo-malformed)

echo "### the dealt plan, against the committed oracle"
rejects "a seg rotation with no SEG line" \
  "no \`SEG\` line — a SEG-SMEM rotation deals a program" -- $(sess seg-missing)
rejects "an anchor log carrying a SEG line" \
  "a SEG-ANCHOR log carries a \`SEG\` line" -- $(sess seg-on-anchor)
rejects "a SEG line without the stripe token" \
  "the trailing stripe token is required" -- $(sess seg-no-stripe-token)
rejects "a SEG line naming another stripe" \
  "the SEG line names stripe=k40" -- $(sess seg-wrong-stripe)
rejects "a program hash that drifts from the oracle" \
  "program hashes to 02dbf4b0cd52aae9" -- $(sess seg-hash-drift)
rejects "a forgery both rotation logs AGREE on" \
  "agreement between logs is not accepted in its place" -- $(sess seg-hash-forged-consistently)
rejects "list offsets off the dealt atom boundaries" \
  "the dealt plan is not the one Task 2 pinned" -- $(sess seg-offsets-off-atom)
rejects "a predicted cost that drifts" \
  "predicted costs are [999" -- $(sess seg-cost-drift)
rejects "an owner census that drifts from the reference stripe" \
  "E4 owner census are [2, 0, 1, 1]" -- $(sess seg-owners-drift)
rejects "a malformed SEG line" "malformed \`SEG\` line" -- $(sess seg-malformed)
rejects "the census log carrying the locality plan" \
  "the dealt plan is not the one Task 2 pinned" -- $(sess seg-order-swapped)

echo "### the positional pins"
rejects "a SEG-SMEM log in the gmem slot" \
  "this position is preregistered as SEG-GMEM at \`--term-order locality\`" \
  -- $(sess pos-smem-in-gmem-slot)
rejects "the two smem orders swapped" \
  "this position is preregistered as SEG-SMEM at \`--term-order locality\`" \
  -- $(sess pos-orders-swapped)
rejects "the two attribution logs swapped" "$ECHOMSG" -- $(sess pos-attr-swapped)
rejects "an anchor log in the headline slot" \
  "this position is preregistered as SEG-SMEM at" -- $(sess pos-anchor-in-headline)
rejects "seven logs" "expects exactly 8 logs in session order" \
  -- $(sess good | tr ' ' '\n' | head -7 | tr '\n' ' ')
rejects "nine logs" "expects exactly 8 logs in session order" \
  -- $(sess good) "$TMP/good-attr-cv100.log"

echo "### the round pins and the rotation"
rejects "the smem session ran 50 rounds" \
  "SEG-SMEM is preregistered at 100 rounds / 10 warmup" -- $(sess rounds-not-100)
rejects "the gmem session ran 90 rounds" \
  "SEG-GMEM is preregistered at 99 rounds / 9 warmup" -- $(sess rounds-not-99)
rejects "the smem session ran 5 warmup rounds" \
  "SEG-SMEM is preregistered at 100 rounds / 10 warmup" -- $(sess warmup-not-10)
rejects "the lanes ran in a fixed order every round" \
  "the rotation is not balanced" -- $(sess rotation-fixed)

echo "### mixed, truncated and aliased logs"
rejects "the samples declare another term order" \
  "sample declares order=census inside the order=locality section" \
  -- $(sess order-forged-in-samples)
rejects "no done trailer" "the run did not finish, or the log is truncated" \
  -- $(sess no-done-trailer)
rejects "one lane is one sample short" \
  "incomplete rounds are not droppable" -- $(sess sample-dropped)
rejects "a duplicated (round, lane) sample" \
  "duplicate sample for round=15 lane=seg-k24-s@128" -- $(sess sample-duplicated)
rejects "a lane is missing from the rotation" \
  "lane set is not the SEG-SMEM rotation" -- $(sess lane-missing)
rejects "a lane declares another body" \
  "rotation runs it on \`eval_lsb_seg_s_cv64\`" -- $(sess lane-symbol-forged)
rejects "one lane's plan differs between two logs" \
  "declares a different plan than" -- $(sess lane-facts-drift)
rejects "an admitted count that does not match the id list" \
  "admitted sources but lists 4 ids" -- $(sess lane-ids-short)
rejects "two lanes carrying one lane's data" \
  "BIT-IDENTICAL samples in every round" -- $(sess lane-aliased)
rejects "another rung's log (the R6 probe grammar)" \
  "before the schedule line — the lane facts cannot be bound" \
  -- "$TMP/not-r7.log" "$TMP/not-r7.log" "$TMP/not-r7.log" "$TMP/not-r7.log" \
     "$TMP/not-r7.log" "$TMP/not-r7.log" "$TMP/not-r7.log" "$TMP/not-r7.log"

printf 'fixture matrix: %d passed, %d failed, %d skipped\n' "$pass" "$fail" "$skip"
exit $(( fail > 0 ))
