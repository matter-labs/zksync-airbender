#!/usr/bin/env bash
# v3 R7 segmented-pair gates, executable rather than transcribed.
#
#   sass        the nine frozen bodies (by INVOKING r5_gates.sh sass, so that table lives in
#               one place) plus the eight seg symbols: symbol set, per-symbol normalized
#               instruction counts AND body digests, `_cv64` normalized-IDENTICAL to `_cv100`,
#               and the shipped resource usage (72 regs, no stack, no local) — SHIPPED build
#               only, and it says so instead of comparing the wrong binary. It also pins the two
#               v3 R9 gate-first symbols in the pair TU (counts, digests, their OWN register
#               counts). `all` runs this lane FIRST and again LAST, so the binary the tree ends
#               on is the gated one.
#   matrix      Task 5's validation matrix, scripted: q parity over the 12 pinned carrier x arm
#               pairs against the LOCAL control128 and over R7b's five segb pairs, the
#               self-product cells (also against the local reference), the CPU-oracle cells,
#               the dealt-plan SEG line against the committed oracle, the per-symbol carveout
#               echoes, the ARM lane facts and the four rotations end to end
#   counts      the diagnostic chain counter per cohort, over every pinned pair and both term
#               orders, plus R7b's per-BLOCK counter (no cohort divisor) and the 4x grid the
#               transplant's four-row block implies — needs the diagnostic binary, which this
#               lane builds
#   r9          the v3 R9 gate-first reorder validation, promoted from the rung's working cells:
#               q bit-identity of both reorder bodies against the IN-SESSION incumbent at three
#               arms and both orders, the self-product duplicate rule, the CPU oracle, the
#               per-symbol carveout echoes and the `carveout symbols` set line per surface, the
#               rotation end to end against the pinned ARM lines, and the flag-rejection matrix
#   r9diag      the R9 diagnostic-build cells: chain executions per warp-program walk (reorder ==
#               incumbent == the pinned count), the per-walk plan line, and the frame-poison
#               divergence — needs the diagnostic binary, which this lane builds
#   cpu         the crate's GPU-free unit tests (cpu_*)
#   fixtures    the emitter fixture matrices — every decision row and every fail-closed guard of
#               tools/r7_table.py and of r4_table.py's R9 reorder path, self-generating, GPU-free
#   regression  tools/r5_gates.sh all, which itself chains r3 + r4
#   all         sass; matrix; r9; counts; r9diag; cpu; fixtures; regression; sass — sequenced so
#               `sass` sees the shipped build, the shipped-build cells run before `counts` swaps
#               the binary, the diagnostic cells run while it is up, every later lane that needs
#               the shipped one gets it back, and the final re-gate lands on the binary the run
#               leaves behind
#
# Usage, from the repo root:
#   cargo build --release -p gpu_gkr_uniskip_bench
#   .agents/bin/with_gpu_lock.sh gpu/gkr_uniskip_bench/tools/r7_gates.sh all
#
# `counts` and `regression` need GPU_GKR_UNISKIP_BENCH_WINDOW_DIAG=1. This script builds that
# binary ITSELF and rebuilds the shipped one before any lane that needs it and on exit —
# whatever it was handed and however it exits. The diagnostic build USED to spill 8 B on the
# seg-S symbols (Task 3) until 87b5df89 hoisted the eq scaling pre-publish; it no longer does,
# but a diagnostic binary left behind still carries the counters, and the next thing anyone runs
# here is a measurement.
#
# `9>&-` on every cargo invocation is load-bearing, not hygiene: this script runs under
# `.agents/bin/with_gpu_lock.sh`, which holds the GPU lock on fd 9, and a `cargo build` spawns
# the sccache SERVER — a long-lived daemon that inherits every open fd, including that one. The
# lock would then outlive the script and the next `with_gpu_lock.sh` would wait forever.
#
# Exit status is the gate verdict: non-zero if any cell fails.
set -uo pipefail

B=${B:-target/release/gpu_gkr_uniskip_bench}
export B
DIR=$(cd "$(dirname "$0")" && pwd)
EMITTER="python3 $DIR/r7_table.py"
FIXTURES=$DIR/r7_fixtures/check.sh
R9FIXTURES=$DIR/r9_fixtures/check.sh
fail=0
diag_built=0
note() { printf '%s\n' "$*"; }
bad() { printf 'FAIL: %s\n' "$*"; fail=1; }

TMP=$(mktemp -d)

# lane arm -> chains per cohort, and (C, removals) for the lane-facts cells. The seg body walks
# the whole program once per cohort, so `chains` is a property of the ARM alone: the machinery
# floor and cache0 execute all 326, and an admitted set removes uncached references from that
# count. Task 5 measured every one of these; the R5 count oracle derives them.
ARM_FACTS="cache0 326 0 0
hot16 181 28 145
k24 165 36 161
k40 133 52 193
allrepeat 92 88 234"

# THE support matrix, one line per pinned (carrier, arm) pair — the same twelve the lane-set
# validator and the `--carrier` surface enforce.
PAIRS="seg-recompute cache0
seg-s-acc hot16
seg-s cache0
seg-s hot16
seg-s100 hot16
seg-s100 k24
seg-s100 k40
seg-g cache0
seg-g hot16
seg-g k24
seg-g k40
seg-g allrepeat"

# R7b's support matrix, the five pinned (carrier, arm) pairs the transplant lanes name: the
# floor at cache0, carrier G's transplant at three capture points, and the slotted-slab
# variant at the incumbent capture point only.
SEGB_PAIRS="segb-recompute cache0
segb-g cache0
segb-g hot16
segb-g k40
segb-g-slotted hot16"

# The eight seg symbols: fn|normalized instruction count|shared bytes|12-hex sha256 of the
# NORMALIZED body. Task 3 and Task 4 measured the R7 counts on the shipped build and R7b Task 1
# the three `segb` ones; the digest closes the gap an instruction count leaves open — a body can
# be rewritten at a constant count, and these eight are the kernels the sessions measure. The
# digests are taken over the same normalized text `norm_dump` produces here, and they survive a
# rebuild: the diagnostic round-trip recompiles this TU twice and reproduces all eight. `_cv64`
# and `_cv100` are ONE body under two symbols, so they share a digest as well as a count.
SEG_SYMBOLS="ab_gkr_uniskip_eval_lsb_seg_recompute_kernel|8336|2048|dc7e31370bb1
ab_gkr_uniskip_eval_lsb_seg_g_kernel|9560|2048|5e330b3f2dff
ab_gkr_uniskip_eval_lsb_seg_s_acc_kernel|10088|0|7ef3be21eec9
ab_gkr_uniskip_eval_lsb_seg_s_cv100_kernel|9784|0|2ef383967d12
ab_gkr_uniskip_eval_lsb_seg_s_cv64_kernel|9784|0|2ef383967d12
ab_gkr_uniskip_eval_lsb_segb_recompute_kernel|8368|0|8d0c0350ba2c
ab_gkr_uniskip_eval_lsb_segb_g_kernel|9696|0|cb905a5c1a37
ab_gkr_uniskip_eval_lsb_segb_g_slotted_kernel|9768|8|d716d4052268"
SEG_TU=uniskip_lsb_seg.cu.o

# The two v3 R9 gate-first symbols, which live in the PAIR TU beside the nine frozen bodies:
# fn|normalized instruction count|registers|shared bytes|12-hex sha256 of the NORMALIZED body.
# Their own table rather than rows in `SEG_SYMBOLS`: that one pins REG:72 for every row, and
# the reorder's whole claim is that its register count is NOT the incumbent's. The nine frozen
# bodies of this TU stay r5_gates.sh's, artifact-compared there and untouched here.
REORDER_SYMBOLS="ab_gkr_uniskip_eval_lsb_pair_cached_reorder_128_lb_kernel|5984|70|2048|10ee133c66ec
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_128_kernel|5888|64|2048|0b9ed0dcf3dc"
# The v3 R9b grid: the four corrected grouped-path bodies at three register budgets each, plus
# the two reference bodies at the relaxed floor. Its own table rather than rows in
# REORDER_SYMBOLS, which pins the two R9 bodies this grid is measured against — those two must
# stay untouched and separately readable.
R9B_SYMBOLS="ab_gkr_uniskip_eval_lsb_pair_cached_128_lb6_kernel|5968|80|2048|d7cc6a60a4d8
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_128_lb6_kernel|5880|75|2048|5cf874cc4d33
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_c_128_lb_kernel|5904|70|2048|facb5cc6a62a
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_c_128_lb6_kernel|5800|75|2048|670930476c80
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_c_128_kernel|5808|64|2048|d586579fe2fb
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_ck_128_lb_kernel|5904|70|2048|7f5e403a6ec8
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_ck_128_lb6_kernel|5800|75|2048|b11657068c04
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_ck_128_kernel|5808|64|2048|9e2e45ad729d
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_128_lb_kernel|6512|72|2048|d6ab3cc52e0c
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_128_lb6_kernel|6424|79|2048|b77a01644bba
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_128_kernel|6472|59|2048|d41856bfc6eb
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_b_128_lb_kernel|6104|70|2048|16cbe71a87f7
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_b_128_lb6_kernel|5968|78|2048|6d56cc8556db
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_b_128_kernel|5992|64|2048|8f841984d5a1
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_bk_128_lb_kernel|6088|72|2048|412b90a6e41f
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_bk_128_lb6_kernel|5960|78|2048|adcb0acffd55
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_bk_128_kernel|5984|64|2048|648ea71c706d
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_bd_128_lb_kernel|6928|72|2048|98d40c54f396
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_bd_128_lb6_kernel|6832|79|2048|dee91b732ac0
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_bd_128_kernel|6872|59|2048|d4126598930c"
PAIR_TU=uniskip_lsb_pair.cu.o

build_bench() { # build_bench <diag-env-value-or-empty>
  if [ -n "$1" ]; then
    GPU_GKR_UNISKIP_BENCH_WINDOW_DIAG=$1 cargo build --release -p gpu_gkr_uniskip_bench 9>&-
  else
    cargo build --release -p gpu_gkr_uniskip_bench 9>&-
  fi
}

# The shipped build is restored on EVERY exit path, including a failed lane and a signal.
# `bad` cannot be used here: the verdict has already been read by the time this runs, so a
# failed restore has to set the status itself.
restore_shipped() {
  local status=$?
  if [ "$diag_built" = 1 ]; then
    note "### restoring the SHIPPED build (no diagnostic define)"
    if ! build_bench "" >"$TMP/build-shipped.log" 2>&1; then
      printf 'FAIL: shipped rebuild failed — the tree is left on the DIAGNOSTIC build\n'
      tail -20 "$TMP/build-shipped.log"
      rm -rf "$TMP"
      exit 1
    fi
  fi
  rm -rf "$TMP"
  exit "$status"
}
trap restore_shipped EXIT

ensure_diag() {
  [ "$diag_built" = 1 ] && return 0
  note "### building the DIAGNOSTIC binary (GPU_GKR_UNISKIP_BENCH_WINDOW_DIAG=1)"
  if ! build_bench 1 >"$TMP/build-diag.log" 2>&1; then
    bad "diagnostic build failed"
    tail -20 "$TMP/build-diag.log"
    return 1
  fi
  diag_built=1
  return 0
}

# Restores the shipped build MID-RUN, for a lane that needs it after `counts` swapped it. Not
# the same thing as the exit trap: a lane that runs `cargo test` or r5's own gates would
# otherwise silently see the diagnostic archive.
ensure_shipped() {
  [ "$diag_built" = 0 ] && return 0
  note "### rebuilding the SHIPPED binary before this lane"
  if ! build_bench "" >"$TMP/build-shipped-mid.log" 2>&1; then
    bad "shipped rebuild failed"
    tail -20 "$TMP/build-shipped-mid.log"
    return 1
  fi
  diag_built=0
  return 0
}

newest_archive() {
  # shellcheck disable=SC2012  # cargo's build dirs are hash-suffixed; -t is the point here
  ls -1t target/release/build/gpu_gkr_uniskip_bench-*/out/libgpu_gkr_uniskip_bench_native.a \
    2>/dev/null | head -1
}

# ON | OFF | unknown for the archive the current binary links. build.rs ALWAYS passes the
# define, so the CMake cache is truthful about the flavor.
build_flavor() {
  local ar=$1 v
  [ -n "$ar" ] || { echo unknown; return; }
  v=$(awk -F= '/^AB_UNISKIP_WINDOW_DIAG:/ {print $2}' \
        "${ar%/libgpu_gkr_uniskip_bench_native.a}/build/CMakeCache.txt" 2>/dev/null | head -1)
  echo "${v:-unknown}"
}

ARCHIVE=""
require_shipped() { # require_shipped <lane name>
  ARCHIVE=$(newest_archive)
  if [ -z "$ARCHIVE" ]; then
    bad "$1: no native archive under target/release/build — build the crate first"
    return 1
  fi
  local flavor; flavor=$(build_flavor "$ARCHIVE")
  note "  archive: $ARCHIVE (AB_UNISKIP_WINDOW_DIAG=$flavor)"
  if [ "$diag_built" = 1 ] || [ "$flavor" != OFF ]; then
    bad "$1 needs the SHIPPED build (AB_UNISKIP_WINDOW_DIAG=$flavor); run 'all', which orders the lanes, or rebuild without the diagnostic define"
    return 1
  fi
  return 0
}

# The q lanes read either build, but the transcript must say which one produced the hashes.
note_flavor() {
  local ar; ar=$(newest_archive)
  note "  archive: ${ar:-<none>} (AB_UNISKIP_WINDOW_DIAG=$(build_flavor "$ar"))"
}

# ---------------------------------------------------------------- matrix

# Empty input hashes to a fixed digest, so a missing binary or a failed run would make BOTH
# sides of a parity comparison equal. qhash runs inside a command substitution and must never
# call bad() — the assignment to `fail` would be lost with the subshell. Diagnostics go to
# stderr, INVALID comes back on stdout, and usable() in the parent sets `fail`.
EMPTY_SHA=e3b0c44298fc
qhash() {
  local out rc lines
  out=$("$B" --log-trace 12 --iterations 0 --dump-q --mode lsb-pair "$@" 2>/dev/null)
  rc=$?
  if [ "$rc" != 0 ]; then echo "  qhash: run failed (exit $rc): $*" >&2; echo INVALID; return; fi
  out=$(printf '%s\n' "$out" | grep '^q\[')
  lines=$(printf '%s\n' "$out" | grep -c '^q\[')
  if [ "$lines" != 32 ]; then echo "  qhash: expected 32 q lines, got $lines: $*" >&2; echo INVALID; return; fi
  printf '%s\n' "$out" | sha256sum | cut -c1-12
}

usable() {
  case "$1" in
    INVALID | "$EMPTY_SHA" | "") bad "unusable digest '$1' for: ${2:-}"; return 1 ;;
    *) return 0 ;;
  esac
}

# The carveout echoes a run applied, as `pct:symbol` pairs in emission order.
echoes_of() {
  "$B" --log-trace 12 --mode lsb-pair --warmup 0 --iterations 0 "$@" 2>/dev/null \
    | sed -n 's/^  carveout hint  *\([0-9]*\)% (\(.*\))$/\1:\2/p' | tr '\n' ' ' \
    | sed 's/ $//'
}

q_parity() {
  note "### q parity: the 12 pinned carrier x arm pairs, both orders, vs the LOCAL control128"
  local cells=0 pass=0 order carrier arm
  for order in census locality; do
    local ref; ref=$(qhash --block-threads 128 --term-order "$order")
    usable "$ref" "local control128 order=$order" || continue
    note "  reference control128 $order = $ref"
    while read -r carrier arm; do
      [ -n "$carrier" ] || continue
      cells=$((cells + 1))
      local got
      got=$(qhash --block-threads 128 --cache-arm "$arm" --carrier "$carrier" \
                  --term-order "$order")
      usable "$got" "$carrier/$arm order=$order" || continue
      if [ "$got" = "$ref" ]; then pass=$((pass + 1))
      else bad "q parity $carrier/$arm order=$order ($got vs $ref)"; fi
    done <<< "$PAIRS"
  done
  note "  cells=$cells passed=$pass"
  [ "$cells" = 24 ] || bad "expected 24 q-parity cells, ran $cells — a pair or an order is missing"
  [ "$cells" = "$pass" ] || bad "q parity incomplete"

  # E4 SELF-PRODUCT CELL. `--self-products 60` is the program's maximum and the only way to
  # exercise the duplicate rule. The LOCAL reference is printed and compared here too: four
  # seg carriers agreeing with each other proves only that they agree. R7b's two published
  # bodies run it as well — the transplant publishes one slot per WARP, so the duplicate rule
  # meets a different reduction there and is a separate claim from carrier G's.
  note "### self-products 60: the S and G pairs plus R7b's two segb pairs, both orders, vs the LOCAL reference"
  local scells=0 spass=0
  for order in census locality; do
    local sref; sref=$(qhash --block-threads 128 --self-products 60 --term-order "$order")
    usable "$sref" "local control128 sp60 order=$order" || continue
    note "  reference control128 sp60 $order = $sref"
    for carrier in seg-s seg-g segb-g segb-g-slotted; do
      scells=$((scells + 1))
      local sgot
      sgot=$(qhash --block-threads 128 --cache-arm hot16 --carrier "$carrier" \
                   --self-products 60 --term-order "$order")
      usable "$sgot" "$carrier/hot16 sp60 order=$order" || continue
      if [ "$sgot" = "$sref" ]; then spass=$((spass + 1))
      else bad "sp60 parity $carrier/hot16 order=$order ($sgot vs $sref)"; fi
    done
  done
  note "  cells=$scells passed=$spass"
  [ "$scells" = 8 ] || bad "expected 8 self-product cells, ran $scells"
  [ "$scells" = "$spass" ] || bad "self-product matrix incomplete"

  # CPU oracle — the only leg that does not go through `q` alone.
  note "### CPU oracle (--validate), one cell per carrier family and order"
  local oks=0 runs=0
  for order in census locality; do
    for carrier in seg-s seg-g segb-g; do
      runs=$((runs + 1))
      if "$B" --log-trace 12 --warmup 0 --iterations 1 --mode lsb-pair --block-threads 128 \
           --cache-arm hot16 --carrier "$carrier" --term-order "$order" --validate 2>/dev/null \
           | grep -q '^q validate: OK (32/32)'; then
        oks=$((oks + 1))
      else bad "CPU oracle $carrier/hot16 order=$order"; fi
    done
  done
  note "  oracle cells=$runs passed=$oks"
  [ "$runs" = 6 ] || bad "expected 6 oracle cells, ran $runs"
  [ "$runs" = "$oks" ] || bad "CPU oracle incomplete"
}

# R7b's five pairs, against the SAME local reference: the transplant is a different geometry
# (four rows per block, one published slot per warp) computing the same q, so nothing about
# it is allowed to move a single hash.
segb_q_parity() {
  note "### q parity: R7b's 5 pinned segb pairs, both orders, vs the LOCAL control128"
  local cells=0 pass=0 order carrier arm ref got
  for order in census locality; do
    ref=$(qhash --block-threads 128 --term-order "$order")
    usable "$ref" "local control128 order=$order" || continue
    note "  reference control128 $order = $ref"
    while read -r carrier arm; do
      [ -n "$carrier" ] || continue
      cells=$((cells + 1))
      got=$(qhash --block-threads 128 --cache-arm "$arm" --carrier "$carrier" \
                  --term-order "$order")
      usable "$got" "$carrier/$arm order=$order" || continue
      if [ "$got" = "$ref" ]; then pass=$((pass + 1))
      else bad "q parity $carrier/$arm order=$order ($got vs $ref)"; fi
    done <<< "$SEGB_PAIRS"
  done
  note "  cells=$cells passed=$pass"
  [ "$cells" = 10 ] || bad "expected 10 segb q-parity cells, ran $cells — a pair or an order is missing"
  [ "$cells" = "$pass" ] || bad "segb q parity incomplete"
}

seg_line_cells() {
  note "### the dealt-plan SEG line, against the COMMITTED oracle (r7_table.py --seg-line)"
  local cells=0 pass=0 order flag want log n got
  for order in census locality; do
    want=$($EMITTER --seg-line "$order")
    if [ -z "$want" ]; then bad "the emitter rendered no oracle SEG line for $order"; continue; fi
    note "  oracle $order: $want"
    # A rotation owns both block sizes internally, so only the single-arm surface names one.
    for flag in --seg-smem-factorial --seg-gmem-factorial --segb-factorial \
                "--block-threads 128 --cache-arm hot16 --carrier seg-s"; do
      cells=$((cells + 1))
      log="$TMP/seg-line-$order-$(echo "$flag" | tr -c 'a-z0-9' '-').log"
      # shellcheck disable=SC2086
      if ! "$B" --log-trace 12 --mode lsb-pair --warmup 0 --iterations 0 \
             --term-order "$order" $flag >"$log" 2>&1; then
        bad "[$flag] order=$order run failed"; tail -3 "$log"; continue
      fi
      n=$(grep -c '^SEG ' "$log")
      if [ "$n" != 1 ]; then bad "[$flag] order=$order printed $n SEG lines, expected 1"; continue; fi
      got=$(grep '^SEG ' "$log")
      if [ "$got" = "$want" ]; then pass=$((pass + 1))
      else
        bad "[$flag] order=$order SEG line differs from the committed oracle"
        note "    got  $got"
        note "    want $want"
      fi
    done
    # The anchor rotation deals nothing, and the emitter REJECTS an anchor log carrying the
    # line — so the runner must not print one.
    cells=$((cells + 1))
    log="$TMP/seg-line-$order-anchor.log"
    if ! "$B" --log-trace 12 --mode lsb-pair --warmup 0 --iterations 0 --seg-anchor \
           --term-order "$order" >"$log" 2>&1; then
      bad "--seg-anchor order=$order run failed"; tail -3 "$log"
    elif [ "$(grep -c '^SEG ' "$log")" = 0 ]; then pass=$((pass + 1))
    else bad "--seg-anchor order=$order printed a SEG line; the anchor rotation deals nothing"; fi
  done
  note "  cells=$cells passed=$pass"
  [ "$cells" = 10 ] || bad "expected 10 SEG-line cells, ran $cells"
  [ "$cells" = "$pass" ] || bad "SEG-line cells incomplete"
}

echo_cells() {
  note "### the applied carveout, one echo per USED symbol (the emitter cross-checks these)"
  local cached=eval_lsb_pair_cached_128_lb
  local rows="--seg-smem-factorial|16:$cached 33:eval_lsb_seg_s_cv64 100:eval_lsb_seg_s_cv100 33:eval_lsb_seg_s_acc 16:eval_lsb_seg_recompute
--seg-gmem-factorial|16:$cached 16:eval_lsb_seg_g 16:eval_lsb_seg_recompute
--seg-anchor|16:$cached
--seg-anchor --carveout-hint 32|32:$cached
--seg-anchor --carveout-hint 100|100:$cached
--block-threads 128 --cache-arm hot16 --carrier seg-s|33:eval_lsb_seg_s_cv64
--block-threads 128 --cache-arm k40 --carrier seg-s100|100:eval_lsb_seg_s_cv100
--block-threads 128 --cache-arm hot16 --carrier seg-s-acc|33:eval_lsb_seg_s_acc
--block-threads 128 --cache-arm hot16 --carrier seg-g|16:eval_lsb_seg_g
--block-threads 128 --cache-arm cache0 --carrier seg-recompute|16:eval_lsb_seg_recompute
--block-threads 128 --cache-arm hot16 --carrier seg-s --carveout-hint 40 --profile|40:eval_lsb_seg_s_cv64
--block-threads 128 --cache-arm hot16 --carrier seg-s100 --carveout-hint 33 --profile|33:eval_lsb_seg_s_cv100
--segb-factorial|16:$cached 16:eval_lsb_segb_g 16:eval_lsb_segb_recompute 2:eval_lsb_segb_g_slotted
--block-threads 128 --cache-arm hot16 --carrier segb-g|16:eval_lsb_segb_g
--block-threads 128 --cache-arm cache0 --carrier segb-recompute|16:eval_lsb_segb_recompute
--block-threads 128 --cache-arm hot16 --carrier segb-g-slotted|2:eval_lsb_segb_g_slotted"
  local cells=0 pass=0 args want got
  while IFS='|' read -r args want; do
    [ -n "$args" ] || continue
    cells=$((cells + 1))
    # shellcheck disable=SC2086
    got=$(echoes_of --term-order locality $args)
    if [ "$got" = "$want" ]; then
      pass=$((pass + 1))
      note "  $args -> $got"
    else
      bad "carveout echoes for [$args]"
      note "    got  $got"
      note "    want $want"
    fi
  done <<< "$rows"
  note "  cells=$cells passed=$pass"
  [ "$cells" = 16 ] || bad "expected 16 echo cells, ran $cells"
  [ "$cells" = "$pass" ] || bad "echo cells incomplete"
}

lane_facts() {
  note "### ARM lane facts: C and removals per arm, off the rotations' own lines"
  local cells=0 pass=0 flag log lane c removals arm want_c want_rem chains
  for flag in --seg-smem-factorial --seg-gmem-factorial --seg-anchor --segb-factorial; do
    log="$TMP/facts-$flag.log"
    if ! "$B" --log-trace 12 --mode lsb-pair --warmup 0 --iterations 0 --term-order locality \
           "$flag" >"$log" 2>&1; then
      bad "$flag run failed"; tail -3 "$log"; continue
    fi
    while read -r _ lane _ _ _ _ _ c removals _; do
      # The arm a lane names is the token between the label's dashes: seg-k40-s@128 -> k40,
      # hot16@128 -> hot16, and the two controls admit nothing by design.
      case "$lane" in
        control@256 | control_lb@128) arm=control ;;
        seg-recompute@128) arm=cache0 ;;
        seg-*) arm=$(printf '%s' "${lane#seg-}" | cut -d- -f1) ;;
        # R7b's labels carry the carrier BEFORE the arm as well, but under the `segb-` stem:
        # `${lane#seg-}` would read the `b` as the arm.
        segb-recompute@128) arm=cache0 ;;
        segb-*) arm=$(printf '%s' "${lane#segb-}" | cut -d- -f1) ;;
        *) arm=${lane%@*} ;;
      esac
      if [ "$arm" = control ]; then
        cells=$((cells + 1))
        if [ "$c" = 0 ] && [ "$removals" = 0 ]; then pass=$((pass + 1))
        else bad "$lane declares C=$c removals=$removals; a no-cache control admits nothing"; fi
        continue
      fi
      read -r chains want_c want_rem <<< "$(awk -v a="$arm" '$1==a {print $2, $3, $4}' <<< "$ARM_FACTS")"
      cells=$((cells + 1))
      if [ -z "$chains" ]; then bad "$lane names arm $arm, which has no pinned facts"; continue; fi
      if [ "$c" = "$want_c" ] && [ "$removals" = "$want_rem" ]; then pass=$((pass + 1))
      else bad "$lane ($arm) declares C=$c removals=$removals, want $want_c / $want_rem"; fi
    done < <(grep '^ARM ' "$log")
  done
  note "  cells=$cells passed=$pass"
  [ "$cells" = 29 ] || bad "expected 29 lane-fact cells (10 + 9 + 2 + 8), ran $cells"
  [ "$cells" = "$pass" ] || bad "lane facts incomplete"
}

rotations() {
  note "### the four rotations end to end (one sample per lane per round)"
  local cells=0 pass=0 spec flag rounds lanes log n
  for spec in "--seg-smem-factorial:10:10" "--seg-gmem-factorial:9:9" "--seg-anchor:10:2" \
              "--segb-factorial:8:8"; do
    flag=${spec%%:*}; rounds=$(echo "$spec" | cut -d: -f2); lanes=$(echo "$spec" | cut -d: -f3)
    cells=$((cells + 1))
    log="$TMP/rotation-$flag.log"
    if ! "$B" --log-trace 12 --mode lsb-pair --warmup 0 --iterations "$rounds" \
           --term-order locality "$flag" >"$log" 2>&1; then
      bad "$flag run failed"; tail -3 "$log"; continue
    fi
    n=$(grep -c '^SAMPLE ' "$log")
    if [ "$n" != $((rounds * lanes)) ]; then
      bad "$flag emitted $n samples, expected $((rounds * lanes)) ($rounds rounds x $lanes lanes)"
      continue
    fi
    if ! grep -q " done order=locality warmup=0 rounds=$rounds lanes=$lanes\$" "$log"; then
      bad "$flag emitted no matching trailer — a truncated log is not a pass"; continue
    fi
    pass=$((pass + 1))
    note "  $flag: $n samples over $lanes lanes"
  done
  note "  cells=$cells passed=$pass"
  [ "$cells" = 4 ] || bad "expected 4 rotation cells, ran $cells"
  [ "$cells" = "$pass" ] || bad "rotation cells incomplete"
}

matrix() {
  if [ ! -x "$B" ]; then
    bad "matrix: no binary at $B — cargo build --release -p gpu_gkr_uniskip_bench"
    return
  fi
  note_flavor
  q_parity
  segb_q_parity
  seg_line_cells
  echo_cells
  lane_facts
  rotations
}

# ---------------------------------------------------------------- counts

# Chain executions per COHORT: a seg block's four warps split one program, so the whole block
# executes the arm's chain count once per cohort (`counts.chains` already includes the
# prologue). One pass, so the printed total must be exactly blocks x cohorts x chains.
chain_line() {
  "$B" --log-trace 12 --warmup 0 --iterations 1 --mode lsb-pair --block-threads 128 \
       --window-count "$@" 2>/dev/null \
    | sed -n 's|^chain executions  *\([0-9]*\) total / \([0-9]*\) blocks / \([0-9]*\) cohorts = \([0-9]*\) per cohort$|\1 \2 \3 \4|p'
}

# The transplant's block IS the cohort — four rows, no cohort loop — so its counter line
# carries no cohort divisor at all. Parsed separately rather than made optional: a per-cohort
# line read as a per-block one would silently divide the expectation by four.
chain_line_block() {
  "$B" --log-trace 12 --warmup 0 --iterations 1 --mode lsb-pair --block-threads 128 \
       --window-count "$@" 2>/dev/null \
    | sed -n 's|^chain executions  *\([0-9]*\) total / \([0-9]*\) blocks = \([0-9]*\) per block$|\1 \2 \3|p'
}

counts() {
  ensure_diag || return
  note "### chain-count gate: per-cohort chains for every pinned pair, both term orders"
  local cells=0 pass=0 order carrier arm calls blocks cohorts per want
  local seg_blocks="" segb_blocks=""
  for order in census locality; do
    while read -r carrier arm; do
      [ -n "$carrier" ] || continue
      cells=$((cells + 1))
      read -r calls blocks cohorts per <<< "$(chain_line --cache-arm "$arm" \
        --carrier "$carrier" --term-order "$order")"
      if [ -z "${per:-}" ]; then
        bad "$carrier/$arm order=$order printed no chain-count line"; continue
      fi
      want=$(awk -v a="$arm" '$1==a {print $2}' <<< "$ARM_FACTS")
      if [ -z "$want" ]; then bad "$arm has no pinned chain count"; continue; fi
      if [ "$cohorts" != 4 ]; then
        bad "$carrier/$arm order=$order reports $cohorts cohorts, the geometry is K = 4"; continue
      fi
      if [ "$calls" != $((blocks * cohorts * per)) ]; then
        bad "$carrier/$arm order=$order: $calls total is not $blocks x $cohorts x $per"; continue
      fi
      if [ "$per" != "$want" ]; then
        bad "$carrier/$arm order=$order: $per chains per cohort, want $want"; continue
      fi
      pass=$((pass + 1))
      seg_blocks=$blocks
      note "  $carrier/$arm/$order: $calls total / $blocks blocks / $cohorts cohorts = $per per cohort"
    done <<< "$PAIRS"
  done
  note "  cells=$cells passed=$pass"
  [ "$cells" = 24 ] || bad "expected 24 chain cells, ran $cells"
  [ "$cells" = "$pass" ] || bad "chain-count gate incomplete"

  note "### chain-count gate, R7b: per-BLOCK chains, no cohort divisor, both term orders"
  local bcells=0 bpass=0
  for order in census locality; do
    while read -r carrier arm; do
      [ -n "$carrier" ] || continue
      bcells=$((bcells + 1))
      read -r calls blocks per <<< "$(chain_line_block --cache-arm "$arm" \
        --carrier "$carrier" --term-order "$order")"
      if [ -z "${per:-}" ]; then
        bad "$carrier/$arm order=$order printed no per-block chain-count line"; continue
      fi
      want=$(awk -v a="$arm" '$1==a {print $2}' <<< "$ARM_FACTS")
      if [ -z "$want" ]; then bad "$arm has no pinned chain count"; continue; fi
      if [ "$calls" != $((blocks * per)) ]; then
        bad "$carrier/$arm order=$order: $calls total is not $blocks x $per"; continue
      fi
      if [ "$per" != "$want" ]; then
        bad "$carrier/$arm order=$order: $per chains per block, want $want"; continue
      fi
      bpass=$((bpass + 1))
      segb_blocks=$blocks
      note "  $carrier/$arm/$order: $calls total / $blocks blocks = $per per block"
    done <<< "$SEGB_PAIRS"
  done
  note "  cells=$bcells passed=$bpass"
  [ "$bcells" = 10 ] || bad "expected 10 segb chain cells, ran $bcells"
  [ "$bcells" = "$bpass" ] || bad "segb chain-count gate incomplete"

  # THE GRID ITSELF, read off the two counter lines rather than pinned: a transplant block
  # covers four rows where an R7 seg block covers sixteen, so `eval_blocks(4)` is exactly 4x
  # `eval_blocks(16)` at one trace. Same binary, same --log-trace, so the ratio is the claim.
  if [ -n "$seg_blocks" ] && [ -n "$segb_blocks" ]; then
    if [ "$segb_blocks" = $((seg_blocks * 4)) ]; then
      note "  grid: $segb_blocks segb blocks = 4 x $seg_blocks seg blocks (eval_blocks(4) vs eval_blocks(16))"
    else
      bad "the transplant launched $segb_blocks blocks against the seg rotation's $seg_blocks; a four-row block is 4x the grid"
    fi
  else
    bad "no block counts to compare — one of the chain-count sections printed nothing"
  fi
}

# ---------------------------------------------------------------- r9 (gate-first reorder)

# The three arms the reorder bodies are validated at: the incumbent capture point, the machinery
# floor, and one deeper plan (k40) that neither Task 1's smoke nor the rung's brief required.
R9_ARMS="hot16 cache0 k40"

# The rotation's six lanes at `--log-trace 12`:
#   label|regs blocks/SM threads grid kernel C removals admitted ids
# The three cached lanes carry ONE plan on three bodies — same C, same removals, the same ordered
# admitted list — which is what makes the body contrast a contrast; the emitter gates that premise
# and this table is where the runner's side of it is pinned. The grid is a function of the trace,
# so the table belongs to the trace these cells run at.
R9_IDS=0,1,2,3,4,5,48,49,50,51,6,7,8,9,10,11
R9_LANE_FACTS="control@256|72 3 256 8 eval_lsb_pair 0 0 0 -
control_lb@128|72 7 128 16 eval_lsb_pair_128_lb 0 0 0 -
hot16@128|72 7 128 16 eval_lsb_pair_cached_128_lb 28 145 16 $R9_IDS
reorder-hot16@128|70 7 128 16 eval_lsb_pair_cached_reorder_128_lb 28 145 16 $R9_IDS
reorder-cache0@128|70 7 128 16 eval_lsb_pair_cached_reorder_128_lb 0 0 0 -
reorder-hot16-free@128|64 8 128 16 eval_lsb_pair_cached_reorder_128 28 145 16 $R9_IDS"

# The `carveout symbols` set line a run printed, without its indent. New R9 grammar: it states the
# whole hinted set, so a MISSING symbol is distinguishable from an unhinted one, and r4_table.py's
# reorder path rejects a log whose set line and per-symbol echoes disagree.
symbols_of() {
  "$B" --log-trace 12 --mode lsb-pair --warmup 0 --iterations 0 "$@" 2>/dev/null \
    | sed -n 's/^  carveout symbols  *//p' | tr '\n' ' ' | sed 's/ $//'
}

# The reorder bodies compute the INCUMBENT's q, so every cell recomputes the incumbent's hash in
# the SAME session against the same binary — the rung's archived digest is a cross-check, never the
# reference.
r9_q_parity() {
  note "### R9 q bit-identity: both reorder bodies vs the IN-SESSION incumbent, 3 arms x 2 orders"
  local cells=0 pass=0 order arm ctl inc reo unb
  for order in census locality; do
    ctl=$(qhash --block-threads 128 --term-order "$order")
    usable "$ctl" "local control128 order=$order" || continue
    note "  reference control128 $order = $ctl"
    for arm in $R9_ARMS; do
      inc=$(qhash --block-threads 128 --cache-arm "$arm" --term-order "$order")
      reo=$(qhash --block-threads 128 --cache-arm "$arm" --reorder --term-order "$order")
      unb=$(qhash --block-threads 128 --cache-arm "$arm" --reorder-free --term-order "$order")
      usable "$inc" "incumbent $arm order=$order" || continue
      usable "$reo" "reorder $arm order=$order" || continue
      usable "$unb" "reorder-free $arm order=$order" || continue
      cells=$((cells + 1))
      if [ "$reo" = "$inc" ]; then pass=$((pass + 1))
      else bad "R9 bit-identity reorder/$arm order=$order ($reo vs incumbent $inc)"; fi
      cells=$((cells + 1))
      if [ "$unb" = "$inc" ]; then pass=$((pass + 1))
      else bad "R9 bit-identity reorder-free/$arm order=$order ($unb vs incumbent $inc)"; fi
      cells=$((cells + 1))
      if [ "$inc" = "$ctl" ]; then pass=$((pass + 1))
      else bad "R9 q parity incumbent/$arm order=$order ($inc vs control $ctl)"; fi
      cells=$((cells + 1))
      if [ "$reo" = "$ctl" ]; then pass=$((pass + 1))
      else bad "R9 q parity reorder/$arm order=$order ($reo vs control $ctl)"; fi
      note "  $arm/$order: incumbent $inc reorder $reo reorder-free $unb"
    done
  done
  note "  cells=$cells passed=$pass"
  [ "$cells" = 24 ] || bad "expected 24 R9 q cells, ran $cells — an arm or an order is missing"
  [ "$cells" = "$pass" ] || bad "R9 q bit-identity incomplete"

  # E4 SELF-PRODUCT CELL. `--self-products 60` is the program's maximum and the only way to reach
  # the W = 0 duplicate rule including E4 self-products: the reordered walk squares H after one
  # load and squares C after one chain, so the duplicate rule meets the reduction in a different
  # order there and is a separate claim from the incumbent's.
  note "### R9 self-products 60: both reorder bodies at three arms, vs the LOCAL reference"
  local scells=0 spass=0 sref sinc sgot flag
  for order in census locality; do
    sref=$(qhash --block-threads 128 --self-products 60 --term-order "$order")
    usable "$sref" "local control128 sp60 order=$order" || continue
    note "  reference control128 sp60 $order = $sref"
    for arm in $R9_ARMS; do
      sinc=$(qhash --block-threads 128 --cache-arm "$arm" --self-products 60 \
                   --term-order "$order")
      usable "$sinc" "incumbent $arm sp60 order=$order" || continue
      for flag in --reorder --reorder-free; do
        sgot=$(qhash --block-threads 128 --cache-arm "$arm" "$flag" --self-products 60 \
                     --term-order "$order")
        usable "$sgot" "$arm $flag sp60 order=$order" || continue
        scells=$((scells + 1))
        if [ "$sgot" = "$sinc" ]; then spass=$((spass + 1))
        else bad "R9 sp60 $arm $flag order=$order ($sgot vs incumbent $sinc)"; fi
        scells=$((scells + 1))
        if [ "$sgot" = "$sref" ]; then spass=$((spass + 1))
        else bad "R9 sp60 $arm $flag order=$order ($sgot vs control $sref)"; fi
      done
      note "  $arm/$order sp60: incumbent $sinc"
    done
  done
  note "  cells=$scells passed=$spass"
  [ "$scells" = 24 ] || bad "expected 24 R9 self-product cells, ran $scells"
  [ "$scells" = "$spass" ] || bad "R9 self-product matrix incomplete"

  # CPU oracle — the only leg that does not go through `q` alone.
  note "### R9 CPU oracle (--validate), one cell per body and order"
  local oks=0 runs=0
  for order in census locality; do
    for arm in $R9_ARMS; do
      for flag in --reorder --reorder-free; do
        runs=$((runs + 1))
        if "$B" --log-trace 12 --warmup 0 --iterations 1 --mode lsb-pair --block-threads 128 \
             --cache-arm "$arm" "$flag" --term-order "$order" --validate 2>/dev/null \
             | grep -q '^q validate: OK (32/32)'; then
          oks=$((oks + 1))
        else bad "R9 CPU oracle $arm $flag order=$order"; fi
      done
    done
  done
  note "  oracle cells=$runs passed=$oks"
  [ "$runs" = 12 ] || bad "expected 12 R9 oracle cells, ran $runs"
  [ "$runs" = "$oks" ] || bad "R9 CPU oracle incomplete"
}

# The applied carveout per R9 surface: one echo per hinted local symbol AND the set line. The
# rotation carries all three hinted bodies at ONE percent — that is what makes its headline contrast
# a single-L1-configuration claim (amendment A3). The `16:` literals below are THIS script's own, on
# purpose: they gate what the SHIPPED binary applies today, which is a different claim from the
# emitter's — that one reads the tier off the log and holds no expected value, so a re-pin moves
# these rows and nothing in `r4_table.py`.
r9_echo_cells() {
  note '### R9 applied carveout: the per-symbol echoes and the "carveout symbols" set line'
  local cached=eval_lsb_pair_cached_128_lb
  local lb=eval_lsb_pair_cached_reorder_128_lb
  local free=eval_lsb_pair_cached_reorder_128
  local rows="--reorder-factorial|16:$cached 16:$lb 16:$free|3 local ($cached, $lb, $free)
--block-threads 128 --cache-arm hot16|16:$cached|1 local ($cached)
--block-threads 128 --cache-arm hot16 --reorder|16:$lb|1 local ($lb)
--block-threads 128 --cache-arm hot16 --reorder-free|16:$free|1 local ($free)
--block-threads 128 --cache-arm cache0 --reorder|16:$lb|1 local ($lb)
--block-threads 128 --cache-arm k40 --reorder-free|16:$free|1 local ($free)
--block-threads 128 --cache-arm hot16 --reorder --carveout-hint 33 --profile|33:$lb|1 local ($lb)
--block-threads 128 --cache-arm hot16 --reorder-free --carveout-hint 33 --profile|33:$free|1 local ($free)"
  local cells=0 pass=0 args want set_want got
  while IFS='|' read -r args want set_want; do
    [ -n "$args" ] || continue
    cells=$((cells + 1))
    # shellcheck disable=SC2086
    got=$(echoes_of --term-order locality $args)
    if [ "$got" = "$want" ]; then pass=$((pass + 1))
    else
      bad "R9 carveout echoes for [$args]"
      note "    got  $got"
      note "    want $want"
    fi
    cells=$((cells + 1))
    # shellcheck disable=SC2086
    got=$(symbols_of --term-order locality $args)
    if [ "$got" = "$set_want" ]; then pass=$((pass + 1)); note "  $args -> $want | $set_want"
    else
      bad "R9 carveout set line for [$args]"
      note "    got  $got"
      note "    want $set_want"
    fi
  done <<< "$rows"
  note "  cells=$cells passed=$pass"
  [ "$cells" = 16 ] || bad "expected 16 R9 echo cells, ran $cells"
  [ "$cells" = "$pass" ] || bad "R9 echo cells incomplete"
}

# The rotation end to end, both orders: the sample/ARM/trailer shape AND every lane's ARM line
# against the pinned table. The emitter reads its whole lane inventory off these lines, so this is
# where the two sides of the R9 grammar meet.
r9_rotation() {
  note "### the R9 rotation end to end, both orders, against the pinned ARM lines"
  local cells=0 pass=0 order log n a lane want got
  for order in census locality; do
    log="$TMP/r9-rotation-$order.log"
    cells=$((cells + 1))
    if ! "$B" --log-trace 12 --mode lsb-pair --warmup 0 --iterations 6 --term-order "$order" \
           --reorder-factorial >"$log" 2>&1; then
      bad "--reorder-factorial order=$order run failed"; tail -3 "$log"; continue
    fi
    n=$(grep -c '^SAMPLE ' "$log")
    a=$(grep -c '^ARM ' "$log")
    if [ "$n" != 36 ] || [ "$a" != 6 ]; then
      bad "--reorder-factorial order=$order emitted $n samples / $a ARM lines, expected 36 / 6"
      continue
    fi
    if ! grep -q "^REORDER schedule order=$order lanes=6 rounds=6 warmup=0\$" "$log"; then
      bad "--reorder-factorial order=$order printed no matching REORDER schedule line"; continue
    fi
    if ! grep -q "^REORDER done order=$order warmup=0 rounds=6 lanes=6\$" "$log"; then
      bad "--reorder-factorial order=$order printed no matching trailer"; continue
    fi
    pass=$((pass + 1))
    note "  $order: 36 samples / 6 ARM lines / schedule + trailer OK"
    while IFS='|' read -r lane want; do
      [ -n "$lane" ] || continue
      cells=$((cells + 1))
      got=$(awk -v l="$lane" '$1=="ARM" && $2==l {$1=""; $2=""; sub(/^  /, ""); print}' "$log")
      if [ "$got" = "$want" ]; then pass=$((pass + 1))
      else
        bad "R9 ARM line for $lane order=$order"
        note "    got  $got"
        note "    want $want"
      fi
    done <<< "$R9_LANE_FACTS"
  done
  note "  cells=$cells passed=$pass"
  [ "$cells" = 14 ] || bad "expected 14 R9 rotation cells (2 shapes + 12 ARM lines), ran $cells"
  [ "$cells" = "$pass" ] || bad "R9 rotation cells incomplete"
}

# The body selector's rejection matrix. Each row is a configuration the flags cannot describe, and
# the CLI must say so rather than silently launch a different body.
r9_rejects() {
  note "### the R9 body-selector rejection matrix (fail closed)"
  local cells=0 pass=0 want out rc
  reject() { # reject <expected substring> <args...>
    want=$1; shift
    cells=$((cells + 1))
    out=$("$B" --log-trace 12 "$@" 2>&1); rc=$?
    if [ "$rc" = 0 ]; then bad "R9 accepted [$*]"; return; fi
    if printf '%s' "$out" | grep -q -- "$want"; then pass=$((pass + 1))
    else bad "R9 wrong rejection for [$*]: $(printf '%s' "$out" | head -3 | tr '\n' ' ')"; fi
  }
  local P="--mode lsb-pair --iterations 0"
  # shellcheck disable=SC2086
  {
  reject "pick one" $P --block-threads 128 --cache-arm hot16 --reorder --reorder-free
  reject "spelled --reorder-free" $P --block-threads 128 --cache-arm hot16 --reorder \
         --no-cache-launch-bounds
  reject "spelled --reorder-free" $P --block-threads 128 --cache-arm hot16 --reorder-free \
         --no-cache-launch-bounds
  reject "needs --mode lsb-pair" $P --block-threads 128 --reorder
  reject "needs --mode lsb-pair" $P --block-threads 128 --cache-arm control --reorder
  reject "needs --mode lsb-pair" $P --cache-arm hot16 --reorder
  reject "needs --mode lsb-pair" --mode lsb-recompute --iterations 0 --reorder
  reject "would change what the rotation runs" $P --reorder-factorial --reorder
  reject "would change what the rotation runs" $P --frontier-interior --reorder
  reject "would change what the rotation runs" $P --segb-factorial --reorder-free
  reject "describe a configuration the run does not have" $P --block-threads 128 \
         --cache-arm hot16 --carrier seg-g --reorder
  reject "each own the whole rotation" $P --reorder-factorial --frontier-interior
  reject "multiple of 6" --mode lsb-pair --reorder-factorial --iterations 7
  reject "use --cache-arm" $P --reorder-factorial --validate
  reject "steers the bounded 128-thread cached kernel" $P --reorder-factorial --carveout-hint 50
  }
  note "  cells=$cells passed=$pass"
  [ "$cells" = 15 ] || bad "expected 15 R9 rejection cells, ran $cells"
  [ "$cells" = "$pass" ] || bad "R9 rejection matrix incomplete"
}

r9() {
  if [ ! -x "$B" ]; then
    bad "r9: no binary at $B — cargo build --release -p gpu_gkr_uniskip_bench"
    return
  fi
  # ENFORCED, not just documented: `r9_rotation` pins the two reorder bodies' register counts
  # (70 / 64), which the diagnostic build's counters move — run against it, the lane would fail for
  # the wrong reason. The `all` chain already orders this lane before `counts`; this is what makes
  # the standalone invocation safe too.
  require_shipped "the R9 lane" || return
  r9_q_parity
  r9_echo_cells
  r9_rotation
  r9_rejects
}

# ---------------------------------------------------------------- r9diag

# The LOCAL bodies' counter line: one warp runs the whole program, so the count is per
# warp-program walk and carries no cohort divisor. Parsed separately from the seg lines above for
# the same reason those two are separate — a count read under the wrong geometry is off by the
# geometry.
r9_walk_chains() {
  "$B" --log-trace 9 --warmup 0 --iterations 1 --mode lsb-pair --block-threads 128 \
       --window-count "$@" 2>/dev/null \
    | sed -n 's|^chain executions .*= \([0-9]*\) per warp-program walk$|\1|p'
}

r9_per_walk() {
  "$B" --log-trace 9 --warmup 0 --iterations 0 --mode lsb-pair --block-threads 128 "$@" \
       2>/dev/null | sed -n 's/^  per walk *//p'
}

r9diag() {
  ensure_diag || return
  note "### R9 chain executions per warp-program walk: reorder == incumbent == the pinned count"
  local cells=0 pass=0 order arm want inc reo unb
  for order in census locality; do
    for arm in $R9_ARMS; do
      want=$(awk -v a="$arm" '$1==a {print $2}' <<< "$ARM_FACTS")
      inc=$(r9_walk_chains --cache-arm "$arm" --term-order "$order")
      reo=$(r9_walk_chains --cache-arm "$arm" --reorder --term-order "$order")
      unb=$(r9_walk_chains --cache-arm "$arm" --reorder-free --term-order "$order")
      if [ -z "$want" ]; then bad "$arm has no pinned chain count"; continue; fi
      if [ -z "$inc" ]; then
        bad "$arm order=$order printed no per-walk chain-count line (diagnostic build?)"; continue
      fi
      cells=$((cells + 1))
      if [ "$inc" = "$want" ]; then pass=$((pass + 1))
      else bad "R9 chains incumbent/$arm order=$order: $inc per walk, want $want"; fi
      cells=$((cells + 1))
      if [ "$reo" = "$inc" ]; then pass=$((pass + 1))
      else bad "R9 chains reorder/$arm order=$order: $reo vs incumbent $inc"; fi
      cells=$((cells + 1))
      if [ "$unb" = "$inc" ]; then pass=$((pass + 1))
      else bad "R9 chains reorder-free/$arm order=$order: $unb vs incumbent $inc"; fi
      note "  $arm/$order: incumbent=$inc reorder=$reo reorder-free=$unb (pinned $want)"
    done
  done
  note "  cells=$cells passed=$pass"
  [ "$cells" = 18 ] || bad "expected 18 R9 chain cells, ran $cells"
  [ "$cells" = "$pass" ] || bad "R9 chain-count gate incomplete"

  # The prologue executes a PLAN; the reorder moves where the chain runs, never what the plan is.
  note "### the per-walk plan line is the same plan on all three bodies"
  local pcells=0 ppass=0
  for order in census locality; do
    for arm in $R9_ARMS; do
      inc=$(r9_per_walk --cache-arm "$arm" --term-order "$order")
      reo=$(r9_per_walk --cache-arm "$arm" --reorder --term-order "$order")
      unb=$(r9_per_walk --cache-arm "$arm" --reorder-free --term-order "$order")
      if [ -z "$inc" ]; then
        bad "$arm order=$order printed no per-walk plan line (diagnostic build?)"; continue
      fi
      pcells=$((pcells + 1))
      if [ "$reo" = "$inc" ]; then ppass=$((ppass + 1))
      else bad "R9 per-walk reorder/$arm order=$order: '$reo' vs '$inc'"; fi
      pcells=$((pcells + 1))
      if [ "$unb" = "$inc" ]; then ppass=$((ppass + 1))
      else bad "R9 per-walk reorder-free/$arm order=$order: '$unb' vs '$inc'"; fi
      note "  $arm/$order per walk: $inc"
    done
  done
  note "  cells=$pcells passed=$ppass"
  [ "$pcells" = 12 ] || bad "expected 12 R9 per-walk cells, ran $pcells"
  [ "$pcells" = "$ppass" ] || bad "R9 per-walk cells incomplete"

  # POISON THE FRAME after the prologue: only an arm with reuses may change q, and the reorder must
  # diverge exactly where the incumbent does. Equal POISONED hashes are stronger than divergence —
  # the two bodies read one corrupted frame in one order.
  note "### frame poison after the prologue: the reorder diverges exactly where the incumbent does"
  local ccells=0 cpass=0 want got igot iref ipoi ref poi flag
  for order in census locality; do
    for arm in $R9_ARMS; do
      iref=$(qhash --block-threads 128 --cache-arm "$arm" --term-order "$order")
      ipoi=$(qhash --block-threads 128 --cache-arm "$arm" --window-poison --term-order "$order")
      usable "$iref" "incumbent $arm order=$order" || continue
      usable "$ipoi" "incumbent poisoned $arm order=$order" || continue
      if [ "$arm" = cache0 ]; then want=same; else want=differ; fi
      igot=same; [ "$iref" != "$ipoi" ] && igot=differ
      ccells=$((ccells + 1))
      if [ "$igot" = "$want" ]; then cpass=$((cpass + 1))
      else bad "R9 poison incumbent/$arm order=$order: $igot, want $want"; fi
      for flag in --reorder --reorder-free; do
        ref=$(qhash --block-threads 128 --cache-arm "$arm" "$flag" --term-order "$order")
        poi=$(qhash --block-threads 128 --cache-arm "$arm" "$flag" --window-poison \
                    --term-order "$order")
        usable "$ref" "$arm $flag order=$order" || continue
        usable "$poi" "$arm $flag poisoned order=$order" || continue
        got=same; [ "$ref" != "$poi" ] && got=differ
        ccells=$((ccells + 1))
        if [ "$got" = "$igot" ]; then cpass=$((cpass + 1))
        else bad "R9 poison $arm $flag order=$order: reorder $got but incumbent $igot"; fi
        ccells=$((ccells + 1))
        if [ "$poi" = "$ipoi" ]; then cpass=$((cpass + 1))
        else bad "R9 poisoned q $arm $flag order=$order: $poi vs incumbent $ipoi"; fi
      done
      note "  $arm/$order: incumbent $igot under poison (want $want), both reorder bodies alike"
    done
  done
  # The uncached control has no frame to poison, on either body's session.
  ref=$(qhash --block-threads 128 --term-order locality)
  poi=$(qhash --block-threads 128 --window-poison --term-order locality)
  if usable "$ref" "control128 locality" && usable "$poi" "control128 poisoned locality"; then
    ccells=$((ccells + 1))
    if [ "$ref" = "$poi" ]; then cpass=$((cpass + 1))
    else bad "R9 poison changed the uncached control ($ref vs $poi)"; fi
  fi
  note "  cells=$ccells passed=$cpass"
  [ "$ccells" = 31 ] || bad "expected 31 R9 poison cells, ran $ccells"
  [ "$ccells" = "$cpass" ] || bad "R9 poison cells incomplete"
}

# ---------------------------------------------------------------- sass

# One normalizer for the live dump, the same one r5_gates.sh uses. TRAP: the address comment is
# 4 OR 5 hex digits — a `{4}` regex truncates every body at instruction 4096 and mismatched
# functions then compare equal.
norm_dump() { # norm_dump <cuobjdump-text> <outdir>
  mkdir -p "$2"
  awk -v dir="$2" '
    /Function : / {
      if (out != "") close(out);
      fn = $0; sub(/^.*Function : /, "", fn); sub(/[ \t\r]+$/, "", fn);
      out = dir "/" fn; printf "" > out; next
    }
    out == "" { next }
    match($0, /^[ \t]*\/\*[0-9a-f]+\*\/[ \t]*/) {
      rest = substr($0, RSTART + RLENGTH); i = index(rest, ";"); if (i == 0) next;
      s = substr(rest, 1, i - 1); gsub(/[ \t]+/, " ", s); sub(/^ /, "", s); sub(/ +$/, "", s);
      print s > out
    }
  ' "$1"
}

# The pinned identity of one normalized body: 12 hex of its sha256, the same width the frozen
# artifacts' hashes are quoted at elsewhere in this suite.
body_digest() { sha256sum "$1" | cut -c1-12; }

seg_sass() {
  note "### the eight seg symbols: symbol set, instruction counts, cv64 = cv100, resources"
  local ar=$ARCHIVE work="$TMP/sass" ar_abs
  ar_abs=$(readlink -f "$ar")
  mkdir -p "$work"
  # The seg TU's OWN fatbin: the device-linked copy differs in relocated MOV/UMOV immediates.
  ( cd "$work" && ar x "$ar_abs" "$SEG_TU" ) 2>/dev/null
  if [ ! -f "$work/$SEG_TU" ]; then bad "could not extract $SEG_TU from $ar"; return; fi
  if ! cuobjdump -sass "$work/$SEG_TU" >"$work/dump.txt" 2>"$work/dump.err"; then
    bad "cuobjdump -sass failed on the seg TU"; tail -3 "$work/dump.err"; return
  fi
  if ! cuobjdump -res-usage "$work/$SEG_TU" >"$work/res.txt" 2>&1; then
    bad "cuobjdump -res-usage failed on the seg TU"; tail -3 "$work/res.txt"; return
  fi
  norm_dump "$work/dump.txt" "$work/live"
  local live; live=$(ls -1 "$work/live" | sort | tr '\n' ' ')
  local want_set; want_set=$(cut -d'|' -f1 <<< "$SEG_SYMBOLS" | sort | tr '\n' ' ')
  if [ "$live" != "$want_set" ]; then
    bad "the seg TU exports [$live], the pinned symbol set is [$want_set]"
  fi
  local rows=0 ok=0 fn want shared digest got res dig
  while IFS='|' read -r fn want shared digest; do
    [ -n "$fn" ] || continue
    rows=$((rows + 1))
    if [ ! -f "$work/live/$fn" ]; then bad "$fn is missing from the built archive"; continue; fi
    got=$(wc -l <"$work/live/$fn")
    dig=$(body_digest "$work/live/$fn")
    # Resource usage is the SPILL gate: the diagnostic build spilled 8 B on the S symbols until
    # 87b5df89, so the shipped one saying STACK:0 LOCAL:0 at 72 registers is what makes a timing
    # comparable — the pin stays because it is what would catch the next such regression.
    res=$(awk -v fn="$fn:" '$2 == fn {getline; print $0}' "$work/res.txt" \
          | tr -s ' ' | sed 's/^ //')
    if [ "$got" != "$want" ]; then
      bad "$fn has $got normalized instructions, the record pins $want"
      continue
    fi
    if [ "$dig" != "$digest" ]; then
      bad "$fn body digest is $dig, the record pins $digest — the body changed at a constant instruction count"
      continue
    fi
    case "$res" in
      "REG:72 STACK:0 SHARED:$shared LOCAL:0 CONSTANT[0]:"*) ;;
      *) bad "$fn resource usage is [$res]; want REG:72 STACK:0 SHARED:$shared LOCAL:0"; continue ;;
    esac
    ok=$((ok + 1))
    note "  $fn: $got instrs, digest $dig, $res"
  done <<< "$SEG_SYMBOLS"
  note "  seg bodies $ok/$rows pinned"
  # NEGATIVE CONTROL for the digest pin, on a DOCTORED normalized body: one instruction
  # rewritten, the instruction count untouched. That is exactly the drift a count cannot see, so
  # the row proves the digest is what catches it — a pin table that is never compared, or a
  # digest taken over something other than the body, would pass every row above.
  local one="$work/live/ab_gkr_uniskip_eval_lsb_seg_s_cv64_kernel"
  local doctored="$work/doctored"
  sed '1s/.*/NOP/' "$one" >"$doctored"
  local n_one n_doc
  n_one=$(wc -l <"$one"); n_doc=$(wc -l <"$doctored")
  if [ "$n_one" != "$n_doc" ]; then
    bad "the digest negative control changed the instruction count ($n_one vs $n_doc); it no longer tests what a count cannot see"
  elif [ "$(body_digest "$doctored")" = "$(body_digest "$one")" ]; then
    bad "a one-instruction edit did not change the body digest — the digest pin is not a pin"
  else
    note "  negative control: 1 instruction rewritten at $n_doc instructions changes the digest"
  fi
  [ "$rows" = 8 ] || bad "expected 8 seg symbols, checked $rows"
  [ "$ok" = 8 ] || bad "the seg symbol table is not 8/8"
  # cv64 and cv100 are ONE body under two symbols — the carveout attribute is per function and
  # sticky, which is the only reason both exist. If they ever diverge, the S contrast is
  # measuring two bodies.
  if cmp -s "$work/live/ab_gkr_uniskip_eval_lsb_seg_s_cv64_kernel" \
            "$work/live/ab_gkr_uniskip_eval_lsb_seg_s_cv100_kernel"; then
    note "  IDENTICAL _cv64 = _cv100 (normalized)"
  else
    bad "_cv64 and _cv100 are not the same body — they exist only to carry two carveouts"
  fi
}

reorder_sass() {
  note "### the two R9 gate-first symbols: instruction counts, digests, registers"
  local ar=$ARCHIVE work="$TMP/sass-reorder" ar_abs
  ar_abs=$(readlink -f "$ar")
  mkdir -p "$work"
  ( cd "$work" && ar x "$ar_abs" "$PAIR_TU" ) 2>/dev/null
  if [ ! -f "$work/$PAIR_TU" ]; then bad "could not extract $PAIR_TU from $ar"; return; fi
  if ! cuobjdump -sass "$work/$PAIR_TU" >"$work/dump.txt" 2>"$work/dump.err"; then
    bad "cuobjdump -sass failed on the pair TU"; tail -3 "$work/dump.err"; return
  fi
  if ! cuobjdump -res-usage "$work/$PAIR_TU" >"$work/res.txt" 2>&1; then
    bad "cuobjdump -res-usage failed on the pair TU"; tail -3 "$work/res.txt"; return
  fi
  norm_dump "$work/dump.txt" "$work/live"
  local rows=0 ok=0 fn want reg shared digest got dig res
  while IFS='|' read -r fn want reg shared digest; do
    [ -n "$fn" ] || continue
    rows=$((rows + 1))
    if [ ! -f "$work/live/$fn" ]; then bad "$fn is missing from the built archive"; continue; fi
    got=$(wc -l <"$work/live/$fn")
    dig=$(body_digest "$work/live/$fn")
    res=$(awk -v fn="$fn:" '$2 == fn {getline; print $0}' "$work/res.txt" \
          | tr -s ' ' | sed 's/^ //')
    if [ "$got" != "$want" ]; then
      bad "$fn has $got normalized instructions, the record pins $want"
      continue
    fi
    if [ "$dig" != "$digest" ]; then
      bad "$fn body digest is $dig, the record pins $digest — the body changed at a constant instruction count"
      continue
    fi
    case "$res" in
      "REG:$reg STACK:0 SHARED:$shared LOCAL:0 CONSTANT[0]:"*) ;;
      *) bad "$fn resource usage is [$res]; want REG:$reg STACK:0 SHARED:$shared LOCAL:0"; continue ;;
    esac
    ok=$((ok + 1))
    note "  $fn: $got instrs, digest $dig, $res"
  done <<< "$REORDER_SYMBOLS"
  note "  reorder bodies $ok/$rows pinned"
  [ "$rows" = 2 ] || bad "expected 2 reorder symbols, checked $rows"
  [ "$ok" = 2 ] || bad "the reorder symbol table is not 2/2"
}

r9b_sass() {
  note "### the R9b grid: body shape x register budget, instruction counts, digests, registers"
  local ar=$ARCHIVE work="$TMP/sass-r9b" ar_abs
  ar_abs=$(readlink -f "$ar")
  mkdir -p "$work"
  ( cd "$work" && ar x "$ar_abs" "$PAIR_TU" ) 2>/dev/null
  if [ ! -f "$work/$PAIR_TU" ]; then bad "could not extract $PAIR_TU from $ar"; return; fi
  if ! cuobjdump -sass "$work/$PAIR_TU" >"$work/dump.txt" 2>"$work/dump.err"; then
    bad "cuobjdump -sass failed on the pair TU"; tail -3 "$work/dump.err"; return
  fi
  if ! cuobjdump -res-usage "$work/$PAIR_TU" >"$work/res.txt" 2>&1; then
    bad "cuobjdump -res-usage failed on the pair TU"; tail -3 "$work/res.txt"; return
  fi
  norm_dump "$work/dump.txt" "$work/live"
  local rows=0 ok=0 fn want reg shared digest got dig res
  while IFS='|' read -r fn want reg shared digest; do
    [ -n "$fn" ] || continue
    rows=$((rows + 1))
    if [ ! -f "$work/live/$fn" ]; then bad "$fn is missing from the built archive"; continue; fi
    got=$(wc -l <"$work/live/$fn")
    dig=$(body_digest "$work/live/$fn")
    res=$(awk -v fn="$fn:" '$2 == fn {getline; print $0}' "$work/res.txt" \
          | tr -s ' ' | sed 's/^ //')
    if [ "$got" != "$want" ]; then
      bad "$fn has $got normalized instructions, the record pins $want"
      continue
    fi
    if [ "$dig" != "$digest" ]; then
      bad "$fn body digest is $dig, the record pins $digest — the body changed at a constant instruction count"
      continue
    fi
    case "$res" in
      "REG:$reg STACK:0 SHARED:$shared LOCAL:0 CONSTANT[0]:"*) ;;
      *) bad "$fn resource usage is [$res]; want REG:$reg STACK:0 SHARED:$shared LOCAL:0"; continue ;;
    esac
    ok=$((ok + 1))
    note "  $fn: $got instrs, digest $dig, $res"
  done <<< "$R9B_SYMBOLS"
  note "  R9b grid bodies $ok/$rows pinned"
  [ "$rows" = 20 ] || bad "expected 20 R9b grid symbols, checked $rows"
  [ "$ok" = 20 ] || bad "the R9b grid symbol table is not 20/20"
}

sass() {
  note "### frozen SASS: r5_gates.sh sass, the nine R3/R4 bodies (one table, one owner)"
  require_shipped "the SASS lane" || return
  local out rc
  out=$("$DIR/r5_gates.sh" sass 2>&1); rc=$?
  printf '%s\n' "$out" | grep -E '^(  archive:|  IDENTICAL|  frozen bodies|FAIL: )' \
    | awk '{print "    " $0}'
  [ "$rc" = 0 ] || bad "r5_gates.sh sass exited $rc"
  printf '%s\n' "$out" | grep -q '^  frozen bodies 9/9 identical' \
    || bad "r5_gates.sh sass did not report 9/9 identical frozen bodies"
  seg_sass
  reorder_sass
  r9b_sass
}

# ---------------------------------------------------------------- cpu / fixtures / regression

cpu() {
  ensure_shipped || return
  note "### GPU-free unit tests (cpu_*)"
  if RUSTFLAGS=-Awarnings cargo test -p gpu_gkr_uniskip_bench --lib --release cpu_ \
       > "$TMP/cpu.log" 2>&1 9>&-; then
    note "  $(grep -E '^test result:' "$TMP/cpu.log" | tail -1)"
  else
    bad "cpu tests"
    grep -E 'FAILED|panicked|^error|^test result:' "$TMP/cpu.log" | tail -20
  fi
}

fixtures() {
  note "### emitter fixture matrix (tools/r7_table.py)"
  if bash "$FIXTURES" > "$TMP/fixtures.log" 2>&1; then
    note "  $(tail -1 "$TMP/fixtures.log")"
  else
    bad "fixture matrix"
    cat "$TMP/fixtures.log"
  fi
  # The R9 rung rides r4_table.py, whose R5/R8 paths r5_gates.sh owns; its OWN fixture matrix is
  # gated here, beside the rest of R9.
  note "### emitter fixture matrix (tools/r4_table.py, R9 reorder path)"
  if bash "$R9FIXTURES" > "$TMP/r9-fixtures.log" 2>&1; then
    note "  $(tail -1 "$TMP/r9-fixtures.log")"
  else
    bad "R9 fixture matrix"
    cat "$TMP/r9-fixtures.log"
  fi
}

regression() {
  # r5_gates.sh all starts with its OWN sass lane, which require_shipped rejects on a
  # diagnostic archive; it then builds and restores its own diagnostic binary.
  ensure_shipped || return
  note "### regression: r5_gates.sh all (chains r3 + r4)"
  local out rc
  out=$("$DIR/r5_gates.sh" all 2>&1); rc=$?
  printf '%s\n' "$out" | grep -E '^(  cells=|  oracle cells=|  gated lanes=|  frozen bodies|  ARM lines|ALL GATES PASS|FAIL: )' \
    | awk '{print "    " $0}'
  [ "$rc" = 0 ] || bad "r5_gates.sh all exited $rc"
  printf '%s\n' "$out" | grep -q '^ALL GATES PASS' || bad "r5_gates.sh all did not print ALL GATES PASS"
}

case "${1:-all}" in
  matrix) matrix ;;
  counts) counts ;;
  r9) r9 ;;
  r9diag) r9diag ;;
  sass) sass ;;
  cpu) cpu ;;
  fixtures) fixtures ;;
  regression) regression ;;
  # `sass` first: it is the only lane that must see the shipped build, and `counts` swaps the
  # binary underneath everything after it — the lanes that need it back ask for it themselves.
  # `sass` LAST as well, and that is not belt-and-braces: the diagnostic round-trip recompiles
  # the seg TU twice, and r5's own sass lane (which `regression` inherits) covers the frozen
  # NINE only. Without this the binary the tree ends on — the one Task 7 measures — would never
  # have had the eight seg bodies verified. No lane may be appended after it that can rebuild.
  all)
    # `r9` before `counts` for the same reason `sass` is first — it reads the shipped build — and
    # `r9diag` immediately after it, while the diagnostic binary `counts` built is still up.
    sass; matrix; r9; counts; r9diag; cpu; fixtures; regression
    note ""
    note "### RE-GATE after the diagnostic round-trip: the binary the tree ENDS on"
    sass
    ;;
  *) echo "usage: $0 {sass|matrix|counts|r9|r9diag|cpu|fixtures|regression|all}" >&2; exit 2 ;;
esac
[ "$fail" = 0 ] && note "ALL GATES PASS"
exit "$fail"
