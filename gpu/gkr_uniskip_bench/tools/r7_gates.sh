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
#   r9b         the v3 R9b corrected-grouped-path validation, promoted from the rung's working
#               cells: q bit-identity of all NINE timed grid cells against the IN-SESSION incumbent
#               at two arms and both orders, the self-product duplicate rule on the two D bodies and
#               once over the whole set, the CPU oracle, the per-symbol carveout echoes and set line
#               per surface (including the concern-1 pin that --no-cache-launch-bounds is HINTED now,
#               and its --carveout-hint none route), BOTH rotations end to end against their pinned
#               ARM lines, and the body/budget rejection matrix
#   r9bdiag     the R9b diagnostic-build cells: chain executions per warp-program walk, the per-walk
#               plan line and the frame-poison divergence, for every timed cell at three arms —
#               needs the diagnostic binary, which this lane builds
#   identity    the device IDENTITY READING (runs inside `r9b` as well), report-only: it prints the
#               live GPU's identity and the one r4_table.py's re-based anchor baseline was measured
#               on, and says whether they are the same machine. A different machine means the
#               emitter's anchor deltas are CROSS-MACHINE and RR should re-base before reading them —
#               a reading for RR, never a rejection. tools/gpu_identity.sh is the helper every future
#               session driver should take telemetry from, so the provenance gap cannot reopen
#   cpu         the crate's GPU-free unit tests (cpu_*)
#   fixtures    the emitter fixture matrices — every decision row and every fail-closed guard of
#               tools/r7_table.py and of r4_table.py's R9 reorder and R9b two-rotation paths,
#               self-generating, GPU-free
#   regression  tools/r5_gates.sh all, which itself chains r3 + r4
#   all         sass; matrix; r9; r9b; counts; r9diag; r9bdiag; cpu; fixtures; regression; sass —
#               reaches its LAST lane every run: no lane's mismatch stops a later one, and the final
#               report is the full cell matrix plus the MISMATCHES block —
#               sequenced so `sass` sees the shipped build, the shipped-build cells run before
#               `counts` swaps the binary, the diagnostic cells run while it is up, every later lane
#               that needs the shipped one gets it back, and the final re-gate lands on the binary
#               the run leaves behind
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
# THE WHOLE MATRIX, NEVER AN EARLY REJECTION (RR, 2026-08-13: "regarding any gates, as i said
# earlier, i do not want to reject anything based on a gate prematurely, i want to see the whole
# picture and then decide"). So a run of this script ALWAYS produces the complete board: every check
# is computed, every outcome is printed, a mismatch is RECORDED and the run carries straight on, and
# the last thing printed is the full cell matrix plus a MISMATCHES block. One lane's mismatch never
# stops a later lane, and one cell's never masks the cells behind it.
#
# THE ONE CARVE-OUT, unchanged: a check that cannot COMPUTE its answer has nothing to report. No
# binary, a run that printed nothing, an archive that will not extract, the wrong build flavour
# underneath — those stop the CELL, are listed in a NOT RUN block with the reason, and never stop the
# run. Everything that computes an answer and finds it wrong is a recorded mismatch.
#
# Exit status is INFORMATION FOR AUTOMATION — non-zero when something mismatched — and nothing in this
# file is conditional on it. The report is printed either way.
set -uo pipefail

B=${B:-target/release/gpu_gkr_uniskip_bench}
export B
DIR=$(cd "$(dirname "$0")" && pwd)
EMITTER="python3 $DIR/r7_table.py"
FIXTURES=$DIR/r7_fixtures/check.sh
R9FIXTURES=$DIR/r9_fixtures/check.sh
R9BFIXTURES=$DIR/r9b_fixtures/check.sh
# The whole-matrix reporting layer is shared by every gate script here — one definition, one contract.
# shellcheck source=gate_report.sh
. "$DIR/gate_report.sh"
diag_built=0

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
# The v3 R10 lazy accumulator grid: two accumulator states (`w96` / `a64`) x two LEVELS (`w96` =
# the grouped member sums, `ow96` = the walk's four outer `e4` accumulators) x two parent walks
# (no tag = the incumbent, `reorder_cd` = R9b's `C+D`) x three register budgets. Its own table for
# R9B_SYMBOLS' reason: that one pins the parents these are measured against, and a parent row must
# stay untouched and separately readable.
R10_SYMBOLS="ab_gkr_uniskip_eval_lsb_pair_cached_w96_128_lb_kernel|6128|72|2048|59cb8068db42
ab_gkr_uniskip_eval_lsb_pair_cached_w96_128_lb6_kernel|6104|80|2048|12a838edcb5d
ab_gkr_uniskip_eval_lsb_pair_cached_w96_128_kernel|6048|75|2048|ded6128e0ef3
ab_gkr_uniskip_eval_lsb_pair_cached_a64_128_lb_kernel|6056|72|2048|d14f93ffb9b8
ab_gkr_uniskip_eval_lsb_pair_cached_a64_128_lb6_kernel|6040|80|2048|999dc403bc40
ab_gkr_uniskip_eval_lsb_pair_cached_a64_128_kernel|6040|75|2048|27617ae137cc
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_w96_128_lb_kernel|6600|70|2048|5509a3f2b66c
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_w96_128_lb6_kernel|6512|77|2048|3c8cc9b45590
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_w96_128_kernel|6480|64|2048|8e3ed784cc5a
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_a64_128_lb_kernel|6544|70|2048|d1c9d3337684
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_a64_128_lb6_kernel|6432|80|2048|ca970ed4e17d
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_a64_128_kernel|6480|65|2048|c16a07733d8a
ab_gkr_uniskip_eval_lsb_pair_cached_ow96_128_lb_kernel|6456|72|2048|fee6c5565742
ab_gkr_uniskip_eval_lsb_pair_cached_ow96_128_lb6_kernel|6344|80|2048|fe864a75f9d8
ab_gkr_uniskip_eval_lsb_pair_cached_ow96_128_kernel|5784|128|2048|f9be3f38c552
ab_gkr_uniskip_eval_lsb_pair_cached_oa64_128_lb_kernel|5984|72|2048|866c7034fbb0
ab_gkr_uniskip_eval_lsb_pair_cached_oa64_128_lb6_kernel|5864|80|2048|74b9fd94efdf
ab_gkr_uniskip_eval_lsb_pair_cached_oa64_128_kernel|5824|96|2048|de9255ef34fe
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_ow96_128_lb_kernel|6840|72|2048|d2caa5bb7267
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_ow96_128_lb6_kernel|6576|80|2048|77fb8861b480
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_ow96_128_kernel|6272|94|2048|d52a14756e59
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_oa64_128_lb_kernel|6360|72|2048|6a2ca919d222
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_oa64_128_lb6_kernel|6392|80|2048|f2bedb40e09f
ab_gkr_uniskip_eval_lsb_pair_cached_reorder_cd_oa64_128_kernel|6400|76|2048|08ce2533db72"
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
    notrun "the diagnostic build" "cargo failed — see the tail below"
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
    notrun "the shipped rebuild" "cargo failed — see the tail below"
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
    notrun "$1" "no native archive under target/release/build — build the crate first"
    return 1
  fi
  local flavor; flavor=$(build_flavor "$ARCHIVE")
  note "  archive: $ARCHIVE (AB_UNISKIP_WINDOW_DIAG=$flavor)"
  if [ "$diag_built" = 1 ] || [ "$flavor" != OFF ]; then
    note "  BUILD-ORDER: $1 needs the SHIPPED build (AB_UNISKIP_WINDOW_DIAG=$flavor); run 'all', which orders the lanes, or rebuild without the diagnostic define"
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
      else bad "q parity $carrier/$arm order=$order" "$ref" "$got"; fi
    done <<< "$PAIRS"
  done
  note "  cells=$cells passed=$pass"
  cellrow "q parity (12 carrier x arm pairs)" "$cells" "$pass"
  [ "$cells" = 24 ] || bad "q-parity cell count — a pair or an order is missing; cells that never ran are not a verdict either way" "24" "${cells}"

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
      else bad "sp60 parity $carrier/hot16 order=$order" "$sref" "$sgot"; fi
    done
  done
  note "  cells=$scells passed=$spass"
  cellrow "self-products 60" "$scells" "$spass"
  [ "$scells" = 8 ] || bad "self-product cell count — cells that never ran are not a verdict either way" "8" "${scells}"

  # CPU oracle — the only leg that does not go through `q` alone.
  # THE FLAKE THESE CELLS USED TO HAVE, and its cause — recorded because a gate that fails for a
  # HARNESS reason is worse than one that fails loudly. On 2026-08-13 one `all` run failed exactly two
  # of these six (`seg-s/hot16 order=census`, `segb-g/hot16 order=census`) and nothing else, then
  # passed standalone and did not reproduce. It was not the oracle: it was `"$B" … | grep -q` under
  # `set -o pipefail`. `grep -q` exits on the first match, the still-running CUDA process takes
  # SIGPIPE, and the PIPELINE's status becomes its 141 even though the match succeeded — reproduced
  # 200/200 with a writer that keeps writing past the match line, and measured at 4 % of runs on the
  # R9b fixture suite's 39 KB output. Every match in this file now CAPTURES first and reads a
  # here-string, so only grep's own status reaches the `if`. A failure here now means the oracle.
  note "### CPU oracle (--validate), one cell per carrier family and order"
  local oks=0 runs=0 out
  for order in census locality; do
    for carrier in seg-s seg-g segb-g; do
      runs=$((runs + 1))
      out=$("$B" --log-trace 12 --warmup 0 --iterations 1 --mode lsb-pair --block-threads 128 \
                 --cache-arm hot16 --carrier "$carrier" --term-order "$order" --validate 2>/dev/null)
      if grep -q '^q validate: OK (32/32)' <<< "$out"; then
        oks=$((oks + 1))
      else bad "CPU oracle $carrier/hot16 order=$order"; fi
    done
  done
  note "  oracle cells=$runs passed=$oks"
  cellrow "CPU oracle (carriers)" "$runs" "$oks"
  [ "$runs" = 6 ] || bad "oracle cell count — cells that never ran are not a verdict either way" "6" "${runs}"
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
      else bad "q parity $carrier/$arm order=$order" "$ref" "$got"; fi
    done <<< "$SEGB_PAIRS"
  done
  note "  cells=$cells passed=$pass"
  cellrow "q parity (R7b segb pairs)" "$cells" "$pass"
  [ "$cells" = 10 ] || bad "segb q-parity cell count — a pair or an order is missing; cells that never ran are not a verdict either way" "10" "${cells}"
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
      # Count AND content: a doubled SEG line used to hide whether either of them was the oracle's.
      local seg_ok=1
      n=$(grep -c '^SEG ' "$log")
      if [ "$n" != 1 ]; then
        bad "[$flag] order=$order SEG line count" "1" "$n"; seg_ok=0
      fi
      got=$(grep -m1 '^SEG ' "$log")
      if [ "$got" != "$want" ]; then
        bad "[$flag] order=$order SEG line differs from the committed oracle" "$want" "${got:-<none>}"
        seg_ok=0
      fi
      [ "$seg_ok" = 1 ] && pass=$((pass + 1))
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
  cellrow "dealt-plan SEG line" "$cells" "$pass"
  [ "$cells" = 10 ] || bad "SEG-line cell count — cells that never ran are not a verdict either way" "10" "${cells}"
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
      bad "carveout echoes for [$args]" "$want" "$got"
    fi
  done <<< "$rows"
  note "  cells=$cells passed=$pass"
  cellrow "applied carveout echoes" "$cells" "$pass"
  [ "$cells" = 16 ] || bad "echo cell count — cells that never ran are not a verdict either way" "16" "${cells}"
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
  cellrow "ARM lane facts" "$cells" "$pass"
  [ "$cells" = 29 ] || bad "lane-fact cell count (10 + 9 + 2 + 8) — a cell that never ran is not a verdict either way" "29" "$cells"
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
    # Sample count AND trailer, both read, whatever the other said: a short log used to hide a
    # missing trailer behind it, and a truncated run shows up in both.
    local rot_ok=1
    n=$(grep -c '^SAMPLE ' "$log")
    if [ "$n" != $((rounds * lanes)) ]; then
      bad "$flag sample count" "$((rounds * lanes)) ($rounds rounds x $lanes lanes)" "$n"
      rot_ok=0
    fi
    if ! grep -q " done order=locality warmup=0 rounds=$rounds lanes=$lanes\$" "$log"; then
      bad "$flag trailer — a truncated log is not a pass" \
          "done order=locality warmup=0 rounds=$rounds lanes=$lanes" "absent"
      rot_ok=0
    fi
    [ "$rot_ok" = 1 ] && pass=$((pass + 1))
    note "  $flag: $n samples over $lanes lanes"
  done
  note "  cells=$cells passed=$pass"
  cellrow "the four rotations end to end" "$cells" "$pass"
  [ "$cells" = 4 ] || bad "rotation cell count — cells that never ran are not a verdict either way" "4" "${cells}"
}

matrix() {
  lane_is matrix
  if [ ! -x "$B" ]; then
    notrun "the whole matrix lane" "no binary at $B — cargo build --release -p gpu_gkr_uniskip_bench"
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
  lane_is counts
  if ! ensure_diag; then
    notrun "the whole counts lane" "the diagnostic build did not complete, so no counter line exists"
    return
  fi
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
      # Geometry, arithmetic and the pinned count are three readings of one counter line: all three
      # are taken, whatever the others said, so a cohort count off by one no longer hides the chain
      # count behind it.
      local cnt_ok=1
      if [ "$cohorts" != 4 ]; then
        bad "$carrier/$arm order=$order cohort count (the geometry is K = 4)" "4" "$cohorts"
        cnt_ok=0
      fi
      if [ "$calls" != $((blocks * cohorts * per)) ]; then
        bad "$carrier/$arm order=$order counter arithmetic" \
            "$blocks blocks x $cohorts cohorts x $per per cohort = $((blocks * cohorts * per))" \
            "$calls total"
        cnt_ok=0
      fi
      if [ "$per" != "$want" ]; then
        bad "$carrier/$arm order=$order chains per cohort" "$want" "$per"; cnt_ok=0
      fi
      [ "$cnt_ok" = 1 ] && pass=$((pass + 1))
      seg_blocks=$blocks
      note "  $carrier/$arm/$order: $calls total / $blocks blocks / $cohorts cohorts = $per per cohort"
    done <<< "$PAIRS"
  done
  note "  cells=$cells passed=$pass"
  cellrow "chain counters per cohort" "$cells" "$pass"
  [ "$cells" = 24 ] || bad "chain cell count — cells that never ran are not a verdict either way" "24" "${cells}"

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
      # Both readings, as above: no cohort divisor here, so it is arithmetic and the pinned count.
      local cnt_ok=1
      if [ "$calls" != $((blocks * per)) ]; then
        bad "$carrier/$arm order=$order counter arithmetic" \
            "$blocks blocks x $per per block = $((blocks * per))" "$calls total"
        cnt_ok=0
      fi
      if [ "$per" != "$want" ]; then
        bad "$carrier/$arm order=$order chains per block" "$want" "$per"; cnt_ok=0
      fi
      [ "$cnt_ok" = 1 ] && bpass=$((bpass + 1))
      segb_blocks=$blocks
      note "  $carrier/$arm/$order: $calls total / $blocks blocks = $per per block"
    done <<< "$SEGB_PAIRS"
  done
  note "  cells=$bcells passed=$bpass"
  cellrow "chain counters per block (R7b)" "$bcells" "$bpass"
  [ "$bcells" = 10 ] || bad "segb chain cell count — cells that never ran are not a verdict either way" "10" "${bcells}"

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
      else bad "R9 bit-identity reorder/$arm order=$order (against the incumbent)" "$inc" "$reo"; fi
      cells=$((cells + 1))
      if [ "$unb" = "$inc" ]; then pass=$((pass + 1))
      else bad "R9 bit-identity reorder-free/$arm order=$order (against the incumbent)" "$inc" "$unb"; fi
      cells=$((cells + 1))
      if [ "$inc" = "$ctl" ]; then pass=$((pass + 1))
      else bad "R9 q parity incumbent/$arm order=$order (against the control)" "$ctl" "$inc"; fi
      cells=$((cells + 1))
      if [ "$reo" = "$ctl" ]; then pass=$((pass + 1))
      else bad "R9 q parity reorder/$arm order=$order (against the control)" "$ctl" "$reo"; fi
      note "  $arm/$order: incumbent $inc reorder $reo reorder-free $unb"
    done
  done
  note "  cells=$cells passed=$pass"
  cellrow "R9 q bit-identity" "$cells" "$pass"
  [ "$cells" = 24 ] || bad "R9 q cell count — an arm or an order is missing; cells that never ran are not a verdict either way" "24" "${cells}"

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
        else bad "R9 sp60 $arm $flag order=$order (against the incumbent)" "$sinc" "$sgot"; fi
        scells=$((scells + 1))
        if [ "$sgot" = "$sref" ]; then spass=$((spass + 1))
        else bad "R9 sp60 $arm $flag order=$order (against the control)" "$sref" "$sgot"; fi
      done
      note "  $arm/$order sp60: incumbent $sinc"
    done
  done
  note "  cells=$scells passed=$spass"
  cellrow "R9 self-products 60" "$scells" "$spass"
  [ "$scells" = 24 ] || bad "R9 self-product cell count — cells that never ran are not a verdict either way" "24" "${scells}"

  # CPU oracle — the only leg that does not go through `q` alone.
  note "### R9 CPU oracle (--validate), one cell per body and order"
  local oks=0 runs=0 out
  for order in census locality; do
    for arm in $R9_ARMS; do
      for flag in --reorder --reorder-free; do
        runs=$((runs + 1))
        out=$("$B" --log-trace 12 --warmup 0 --iterations 1 --mode lsb-pair \
                   --block-threads 128 --cache-arm "$arm" "$flag" --term-order "$order" \
                   --validate 2>/dev/null)
        if grep -q '^q validate: OK (32/32)' <<< "$out"; then
          oks=$((oks + 1))
        else bad "R9 CPU oracle $arm $flag order=$order"; fi
      done
    done
  done
  note "  oracle cells=$runs passed=$oks"
  cellrow "R9 CPU oracle" "$runs" "$oks"
  [ "$runs" = 12 ] || bad "R9 oracle cell count — cells that never ran are not a verdict either way" "12" "${runs}"
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
      bad "R9 carveout echoes for [$args]" "$want" "$got"
    fi
    cells=$((cells + 1))
    # shellcheck disable=SC2086
    got=$(symbols_of --term-order locality $args)
    if [ "$got" = "$set_want" ]; then pass=$((pass + 1)); note "  $args -> $want | $set_want"
    else
      bad "R9 carveout set line for [$args]" "$set_want" "$got"
    fi
  done <<< "$rows"
  note "  cells=$cells passed=$pass"
  cellrow "R9 applied carveout" "$cells" "$pass"
  [ "$cells" = 16 ] || bad "R9 echo cell count — cells that never ran are not a verdict either way" "16" "${cells}"
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
    # Shape AND schedule AND trailer, all read — and the SIX ARM lines below run regardless, which
    # they used to be skipped for: a shape wobble is not a reason to stop reading the lane facts.
    local shape_ok=1
    n=$(grep -c '^SAMPLE ' "$log")
    a=$(grep -c '^ARM ' "$log")
    if [ "$n" != 36 ] || [ "$a" != 6 ]; then
      bad "--reorder-factorial order=$order log shape" "36 samples / 6 ARM lines" \
          "$n samples / $a ARM lines"
      shape_ok=0
    fi
    if ! grep -q "^REORDER schedule order=$order lanes=6 rounds=6 warmup=0\$" "$log"; then
      bad "--reorder-factorial order=$order schedule line" \
          "REORDER schedule order=$order lanes=6 rounds=6 warmup=0" "absent"
      shape_ok=0
    fi
    if ! grep -q "^REORDER done order=$order warmup=0 rounds=6 lanes=6\$" "$log"; then
      bad "--reorder-factorial order=$order trailer" \
          "REORDER done order=$order warmup=0 rounds=6 lanes=6" "absent"
      shape_ok=0
    fi
    [ "$shape_ok" = 1 ] && pass=$((pass + 1))
    note "  $order: $n samples / $a ARM lines / schedule + trailer read"
    while IFS='|' read -r lane want; do
      [ -n "$lane" ] || continue
      cells=$((cells + 1))
      got=$(awk -v l="$lane" '$1=="ARM" && $2==l {$1=""; $2=""; sub(/^  /, ""); print}' "$log")
      if [ "$got" = "$want" ]; then pass=$((pass + 1))
      else
        bad "R9 ARM line for $lane order=$order" "$want" "$got"
      fi
    done <<< "$R9_LANE_FACTS"
  done
  note "  cells=$cells passed=$pass"
  cellrow "R9 rotation end to end" "$cells" "$pass"
  [ "$cells" = 14 ] || bad "R9 rotation cell count (2 shapes + 12 ARM lines) — a cell that never ran is not a verdict either way" "14" "$cells"
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
    if grep -q -- "$want" <<< "$out"; then pass=$((pass + 1))
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
  cellrow "R9 rejection matrix" "$cells" "$pass"
  [ "$cells" = 15 ] || bad "R9 rejection cell count — cells that never ran are not a verdict either way" "15" "${cells}"
}

r9() {
  lane_is r9
  if [ ! -x "$B" ]; then
    notrun "the whole r9 lane" "no binary at $B — cargo build --release -p gpu_gkr_uniskip_bench"
    return
  fi
  # ENFORCED, not just documented: `r9_rotation` pins the two reorder bodies' register counts
  # (70 / 64), which the diagnostic build's counters move — run against it, the lane would fail for
  # the wrong reason. The `all` chain already orders this lane before `counts`; this is what makes
  # the standalone invocation safe too.
  if ! require_shipped "the R9 lane"; then
    notrun "the whole r9 lane" "BUILD-ORDER: the archive under it is not the SHIPPED build, so its pinned register counts would read another build's numbers"
    return
  fi
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
  lane_is r9diag
  if ! ensure_diag; then
    notrun "the whole r9diag lane" "the diagnostic build did not complete, so no counter line exists"
    return
  fi
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
  cellrow "R9 chain executions per walk" "$cells" "$pass"
  [ "$cells" = 18 ] || bad "R9 chain cell count — cells that never ran are not a verdict either way" "18" "${cells}"

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
  cellrow "R9 per-walk plan line" "$pcells" "$ppass"
  [ "$pcells" = 12 ] || bad "R9 per-walk cell count — cells that never ran are not a verdict either way" "12" "${pcells}"

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
    else bad "R9 poison changed the uncached control" "$poi" "$ref"; fi
  fi
  note "  cells=$ccells passed=$cpass"
  cellrow "R9 frame poison" "$ccells" "$cpass"
  [ "$ccells" = 31 ] || bad "R9 poison cell count — cells that never ran are not a verdict either way" "31" "${ccells}"
}

# ---------------------------------------------------------------- r9b (corrected grouped path)

# The nine TIMED cells of the v3 R9b grid as `<label>|<flags>`, promoted from the rung's working
# validation scripts. Every one is compared against the IN-SESSION incumbent at the same arm and the
# same term order: the repair moves DECODE and interleaving, never a factor and never a term order, so
# `q` must be BIT-IDENTICAL rather than merely parity-equal (`ed3bead0bce8` is a cross-check, not the
# reference). The grid is 6 bodies x 3 budgets and these nine are the cells that can enter a timing.
R9B_CELLS="C@7|--regroup c
C@6|--regroup c --pair-budget lb6
C@unb|--regroup c --pair-budget free
B@7|--regroup b
C+D@7|--regroup cd
B+D@7|--regroup bd
inc@6|--pair-budget lb6
inc@unb|--no-cache-launch-bounds
R9@7|--reorder"
# The two D bodies. `--self-products 60` is the program's maximum and the only way to reach the W = 0
# duplicate rule including E4 self-products; the D bodies carry the member's whole sequence in each of
# three runtime arms, so the rule appears three times per class shape (Task 1 concern 5).
R9B_D_CELLS="C+D@7|--regroup cd
B+D@7|--regroup bd"
# The arms every timed cell is validated at. The diagnostic lane adds one deeper plan.
R9B_ARMS="hot16 cache0"
R9B_DIAG_ARMS="hot16 cache0 k40"

# The two rotations' lanes at `--log-trace 12`, same grammar as `R9_LANE_FACTS`:
#   label|regs blocks/SM threads grid kernel C removals admitted ids
# The blocks/SM figure is ARITHMETIC, derived in Rust from the static register line — R9 measured a
# body whose static 70 was ALLOCATED as 72, so the realized tier is Task 4's ncu G0 and appears
# nowhere here. NOTE the register column is NOT monotone in the budget: `(128,6)` is the
# maximum-register cell (incumbent 72 / 80 / 75, C 70 / 75 / 64).
R9B_CLASS_FACTS="control@256|72 3 256 8 eval_lsb_pair 0 0 0 -
control_lb@128|72 7 128 16 eval_lsb_pair_128_lb 0 0 0 -
hot16@128|72 7 128 16 eval_lsb_pair_cached_128_lb 28 145 16 $R9_IDS
reorder-hot16@128|70 7 128 16 eval_lsb_pair_cached_reorder_128_lb 28 145 16 $R9_IDS
c-hot16@128|70 7 128 16 eval_lsb_pair_cached_reorder_c_128_lb 28 145 16 $R9_IDS
b-hot16@128|70 7 128 16 eval_lsb_pair_cached_reorder_b_128_lb 28 145 16 $R9_IDS
cd-hot16@128|72 7 128 16 eval_lsb_pair_cached_reorder_cd_128_lb 28 145 16 $R9_IDS
bd-hot16@128|72 7 128 16 eval_lsb_pair_cached_reorder_bd_128_lb 28 145 16 $R9_IDS"
R9B_BUDGET_FACTS="control@256|72 3 256 8 eval_lsb_pair 0 0 0 -
control_lb@128|72 7 128 16 eval_lsb_pair_128_lb 0 0 0 -
hot16@128|72 7 128 16 eval_lsb_pair_cached_128_lb 28 145 16 $R9_IDS
hot16-lb6@128|80 6 128 16 eval_lsb_pair_cached_128_lb6 28 145 16 $R9_IDS
hot16-free@128|75 6 128 16 eval_lsb_pair_cached_128 28 145 16 $R9_IDS
c-hot16@128|70 7 128 16 eval_lsb_pair_cached_reorder_c_128_lb 28 145 16 $R9_IDS
c-hot16-lb6@128|75 6 128 16 eval_lsb_pair_cached_reorder_c_128_lb6 28 145 16 $R9_IDS
c-hot16-free@128|64 8 128 16 eval_lsb_pair_cached_reorder_c_128 28 145 16 $R9_IDS"

r9b_q_parity() {
  note "### R9b q bit-identity: all nine timed cells vs the IN-SESSION incumbent, 2 arms x 2 orders"
  local cells=0 pass=0 order arm ctl inc got label flags
  for order in census locality; do
    ctl=$(qhash --block-threads 128 --term-order "$order")
    usable "$ctl" "local control128 order=$order" || continue
    note "  reference control128 $order = $ctl"
    for arm in $R9B_ARMS; do
      inc=$(qhash --block-threads 128 --cache-arm "$arm" --term-order "$order")
      usable "$inc" "incumbent $arm order=$order" || continue
      cells=$((cells + 1))
      if [ "$inc" = "$ctl" ]; then pass=$((pass + 1))
      else bad "R9b q parity incumbent/$arm order=$order (against the control)" "$ctl" "$inc"; fi
      while IFS='|' read -r label flags; do
        [ -n "$label" ] || continue
        # shellcheck disable=SC2086
        got=$(qhash --block-threads 128 --cache-arm "$arm" $flags --term-order "$order")
        usable "$got" "$label $arm order=$order" || continue
        cells=$((cells + 1))
        if [ "$got" = "$inc" ]; then pass=$((pass + 1))
        else bad "R9b bit-identity $label/$arm order=$order (against the incumbent)" "$inc" "$got"; fi
      done <<< "$R9B_CELLS"
      note "  $arm/$order: incumbent $inc, all nine timed cells bit-identical"
    done
  done
  note "  cells=$cells passed=$pass"
  cellrow "R9b q bit-identity" "$cells" "$pass"
  [ "$cells" = 40 ] || bad "R9b q cell count — a cell, an arm or an order is missing; cells that never ran are not a verdict either way" "40" "${cells}"

  note "### R9b self-products 60: the D bodies at both arms, then every timed cell at hot16"
  local scells=0 spass=0 sref sinc sgot
  for order in census locality; do
    sref=$(qhash --block-threads 128 --self-products 60 --term-order "$order")
    usable "$sref" "local control128 sp60 order=$order" || continue
    note "  reference control128 sp60 $order = $sref"
    for arm in $R9B_ARMS; do
      sinc=$(qhash --block-threads 128 --cache-arm "$arm" --self-products 60 --term-order "$order")
      usable "$sinc" "incumbent $arm sp60 order=$order" || continue
      while IFS='|' read -r label flags; do
        [ -n "$label" ] || continue
        # shellcheck disable=SC2086
        sgot=$(qhash --block-threads 128 --cache-arm "$arm" $flags --self-products 60 \
                     --term-order "$order")
        usable "$sgot" "$label $arm sp60 order=$order" || continue
        scells=$((scells + 1))
        if [ "$sgot" = "$sinc" ]; then spass=$((spass + 1))
        else bad "R9b sp60 $label/$arm order=$order (against the incumbent)" "$sinc" "$sgot"; fi
        scells=$((scells + 1))
        if [ "$sgot" = "$sref" ]; then spass=$((spass + 1))
        else bad "R9b sp60 $label/$arm order=$order (against the control)" "$sref" "$sgot"; fi
      done <<< "$R9B_D_CELLS"
      note "  $arm/$order sp60: incumbent $sinc, both D bodies match it and the control"
    done
  done
  # And the whole timed set once, so no cell is left unexercised under the duplicate rule.
  sinc=$(qhash --block-threads 128 --cache-arm hot16 --self-products 60 --term-order locality)
  if usable "$sinc" "incumbent hot16 sp60 order=locality"; then
    while IFS='|' read -r label flags; do
      [ -n "$label" ] || continue
      # shellcheck disable=SC2086
      sgot=$(qhash --block-threads 128 --cache-arm hot16 $flags --self-products 60 \
                   --term-order locality)
      usable "$sgot" "$label hot16 sp60 order=locality" || continue
      scells=$((scells + 1))
      if [ "$sgot" = "$sinc" ]; then spass=$((spass + 1))
      else bad "R9b sp60 $label/hot16 order=locality (against the incumbent)" "$sinc" "$sgot"; fi
    done <<< "$R9B_CELLS"
  fi
  note "  cells=$scells passed=$spass"
  cellrow "R9b self-products 60" "$scells" "$spass"
  [ "$scells" = 25 ] || bad "R9b self-product cell count — cells that never ran are not a verdict either way" "25" "${scells}"

  # CPU oracle — the only leg that does not go through `q` alone.
  note "### R9b CPU oracle (--validate), one cell per timed cell, arm and order"
  local runs=0 oks=0 out
  for order in census locality; do
    for arm in $R9B_ARMS; do
      while IFS='|' read -r label flags; do
        [ -n "$label" ] || continue
        runs=$((runs + 1))
        # shellcheck disable=SC2086
        out=$("$B" --log-trace 12 --warmup 0 --iterations 1 --mode lsb-pair \
                   --block-threads 128 --cache-arm "$arm" $flags --term-order "$order" \
                   --validate 2>/dev/null)
        if grep -q '^q validate: OK (32/32)' <<< "$out"; then
          oks=$((oks + 1))
        else bad "R9b CPU oracle $label $arm order=$order"; fi
      done <<< "$R9B_CELLS"
    done
  done
  note "  oracle cells=$runs passed=$oks"
  cellrow "R9b CPU oracle" "$runs" "$oks"
  [ "$runs" = 36 ] || bad "R9b oracle cell count — cells that never ran are not a verdict either way" "36" "${runs}"
}

# The applied carveout per R9b surface. Both rotations hint SIX local symbols, and the CLASS
# rotation's echo ORDER is `LaneKernel::HINTED`'s — `cd` BEFORE `b` — not its lane order, which is why
# these rows pin the set as a SEQUENCE. The `16:` literals are THIS script's own, as in the R9 lane:
# they gate what the SHIPPED binary applies today, which is a different claim from the emitter's.
r9b_echo_cells() {
  note '### R9b applied carveout: the per-symbol echoes and the "carveout symbols" set line'
  local lb=eval_lsb_pair_cached_128_lb
  local lb6=eval_lsb_pair_cached_128_lb6
  local free=eval_lsb_pair_cached_128
  local c=eval_lsb_pair_cached_reorder_c_128_lb
  local c6=eval_lsb_pair_cached_reorder_c_128_lb6
  local cf=eval_lsb_pair_cached_reorder_c_128
  local r=eval_lsb_pair_cached_reorder_128_lb
  local bb=eval_lsb_pair_cached_reorder_b_128_lb
  local cdk=eval_lsb_pair_cached_reorder_cd_128_lb
  local bdk=eval_lsb_pair_cached_reorder_bd_128_lb
  local A="--block-threads 128 --cache-arm hot16"
  local rows="--r9b-class|16:$lb 16:$r 16:$c 16:$cdk 16:$bb 16:$bdk|6 local ($lb, $r, $c, $cdk, $bb, $bdk)
--r9b-budget|16:$lb 16:$lb6 16:$free 16:$c 16:$c6 16:$cf|6 local ($lb, $lb6, $free, $c, $c6, $cf)
$A|16:$lb|1 local ($lb)
$A --regroup c|16:$c|1 local ($c)
$A --regroup c --pair-budget lb6|16:$c6|1 local ($c6)
$A --regroup c --pair-budget free|16:$cf|1 local ($cf)
$A --regroup b|16:$bb|1 local ($bb)
$A --regroup cd|16:$cdk|1 local ($cdk)
$A --regroup bd|16:$bdk|1 local ($bdk)
$A --pair-budget lb6|16:$lb6|1 local ($lb6)
$A --no-cache-launch-bounds|16:$free|1 local ($free)
$A --reorder|16:$r|1 local ($r)"
  local cells=0 pass=0 args want set_want got
  while IFS='|' read -r args want set_want; do
    [ -n "$args" ] || continue
    cells=$((cells + 1))
    # shellcheck disable=SC2086
    got=$(echoes_of --term-order locality $args)
    if [ "$got" = "$want" ]; then pass=$((pass + 1))
    else
      bad "R9b carveout echoes for [$args]" "$want" "$got"
    fi
    cells=$((cells + 1))
    # shellcheck disable=SC2086
    got=$(symbols_of --term-order locality $args)
    if [ "$got" = "$set_want" ]; then pass=$((pass + 1)); note "  $args -> $want"
    else
      bad "R9b carveout set line for [$args]" "$set_want" "$got"
    fi
  done <<< "$rows"

  # TASK 2 CONCERN 1, pinned. `--no-cache-launch-bounds` is HINTED now where it used to run at the
  # driver's own sizing — it had to be, because R9b times that cell — and the row above is what keeps
  # that behaviour change from drifting back silently. `--carveout-hint none` is its only other-tier
  # route (an explicit percent is rejected on this surface by a pinned r6 cell), and there the run
  # must print NO carveout line at all. The occupancy line is checked in the same breath: without it,
  # an empty echo set would also be what a failed run produces.
  local out
  out=$("$B" --log-trace 12 --mode lsb-pair --warmup 0 --iterations 0 --block-threads 128 \
             --cache-arm hot16 --no-cache-launch-bounds --carveout-hint none \
             --term-order locality 2>/dev/null)
  cells=$((cells + 1))
  if [ -n "$out" ] && ! grep -q '^  carveout ' <<< "$out"; then pass=$((pass + 1))
  else bad "R9b --carveout-hint none on --no-cache-launch-bounds still echoed a carveout line"; fi
  cells=$((cells + 1))
  if grep -q "^  occupancy .*($free," <<< "$out"; then
    pass=$((pass + 1)); note "  --no-cache-launch-bounds --carveout-hint none -> unhinted, $free launched"
  else bad "R9b --carveout-hint none on --no-cache-launch-bounds did not reach $free"; fi

  note "  cells=$cells passed=$pass"
  cellrow "R9b applied carveout" "$cells" "$pass"
  [ "$cells" = 26 ] || bad "R9b echo cell count — cells that never ran are not a verdict either way" "26" "${cells}"
}

# Both rotations end to end, both orders: the sample/ARM/schedule/trailer shape AND every lane's ARM
# line against the pinned table. The two rotations share the tag `R9B`, so the LANE SET is the only
# thing that says which one ran — which is exactly what the emitter keys on, and these rows are where
# the runner's side of it is pinned.
r9b_rotation() {
  note "### the two R9b rotations end to end, both orders, against the pinned ARM lines"
  local cells=0 pass=0 flag order log n a lane want got facts
  for flag in r9b-class r9b-budget; do
    if [ "$flag" = r9b-class ]; then facts=$R9B_CLASS_FACTS; else facts=$R9B_BUDGET_FACTS; fi
    for order in census locality; do
      log="$TMP/$flag-$order.log"
      cells=$((cells + 1))
      if ! "$B" --log-trace 12 --mode lsb-pair --warmup 0 --iterations 8 --term-order "$order" \
             "--$flag" >"$log" 2>&1; then
        bad "--$flag order=$order run failed"; tail -3 "$log"; continue
      fi
      # Shape AND schedule AND trailer, all read — and the EIGHT ARM lines below run regardless.
      local shape_ok=1
      n=$(grep -c '^SAMPLE ' "$log")
      a=$(grep -c '^ARM ' "$log")
      if [ "$n" != 64 ] || [ "$a" != 8 ]; then
        bad "--$flag order=$order log shape" "64 samples / 8 ARM lines" \
            "$n samples / $a ARM lines"
        shape_ok=0
      fi
      if ! grep -q "^R9B schedule order=$order lanes=8 rounds=8 warmup=0\$" "$log"; then
        bad "--$flag order=$order schedule line" \
            "R9B schedule order=$order lanes=8 rounds=8 warmup=0" "absent"
        shape_ok=0
      fi
      if ! grep -q "^R9B done order=$order warmup=0 rounds=8 lanes=8\$" "$log"; then
        bad "--$flag order=$order trailer" "R9B done order=$order warmup=0 rounds=8 lanes=8" \
            "absent"
        shape_ok=0
      fi
      [ "$shape_ok" = 1 ] && pass=$((pass + 1))
      note "  --$flag $order: $n samples / $a ARM lines / schedule + trailer read"
      while IFS='|' read -r lane want; do
        [ -n "$lane" ] || continue
        cells=$((cells + 1))
        got=$(awk -v l="$lane" '$1=="ARM" && $2==l {$1=""; $2=""; sub(/^  /, ""); print}' "$log")
        if [ "$got" = "$want" ]; then pass=$((pass + 1))
        else
          bad "R9b ARM line for $lane under --$flag order=$order" "$want" "$got"
        fi
      done <<< "$facts"
    done
  done
  note "  cells=$cells passed=$pass"
  cellrow "R9b rotations end to end" "$cells" "$pass"
  [ "$cells" = 36 ] || bad "R9b rotation cell count (4 shapes + 32 ARM lines) — a cell that never ran is not a verdict either way" "36" "$cells"
}

# The body/budget selector's rejection matrix. Each row is a configuration the flags cannot describe,
# and the CLI must say so rather than silently launch another cell of the grid.
r9b_rejects() {
  note "### the R9b body/budget selector rejection matrix (fail closed)"
  local cells=0 pass=0 want out rc
  reject() { # reject <expected substring> <args...>
    want=$1; shift
    cells=$((cells + 1))
    out=$("$B" --log-trace 12 "$@" 2>&1); rc=$?
    if [ "$rc" = 0 ]; then bad "R9b accepted [$*]"; return; fi
    if grep -q -- "$want" <<< "$out"; then pass=$((pass + 1))
    else bad "R9b wrong rejection for [$*]: $(printf '%s' "$out" | head -3 | tr '\n' ' ')"; fi
  }
  local P="--mode lsb-pair --iterations 0"
  local A="--block-threads 128 --cache-arm hot16"
  # shellcheck disable=SC2086
  {
  reject "pick one" $P $A --regroup c --reorder
  reject "pick one" $P $A --regroup c --reorder-free
  reject "spelled --reorder-free" $P $A --regroup c --no-cache-launch-bounds
  reject "already name the unbounded budget" $P $A --reorder-free --pair-budget lb6
  reject "already name the unbounded budget" $P $A --no-cache-launch-bounds --pair-budget lb6
  reject "it needs --regroup" $P $A --pair-budget free
  reject "it needs --regroup" $P $A --reorder --pair-budget free
  reject "needs --mode lsb-pair" $P --block-threads 128 --regroup c
  reject "needs --mode lsb-pair" $P --block-threads 128 --cache-arm control --regroup c
  reject "needs --mode lsb-pair" $P --cache-arm hot16 --regroup c
  reject "needs --mode lsb-pair" $P --block-threads 256 --cache-arm hot16 --regroup c
  reject "needs --mode lsb-pair" $P --block-threads 256 --cache-arm hot16 --pair-budget lb6
  reject "needs --mode lsb-pair" --mode lsb-recompute --iterations 0 --regroup c
  reject "needs --mode lsb-pair" $P --block-threads 128 --pair-budget lb6
  reject "needs --mode lsb-pair" $P --block-threads 128 --cache-arm control --pair-budget lb6
  reject "would change what the rotation runs" $P --r9b-class --regroup c
  reject "would change what the rotation runs" $P --r9b-budget --pair-budget lb6
  reject "would change what the rotation runs" $P --reorder-factorial --regroup c
  reject "would change what the rotation runs" $P --frontier-interior --pair-budget lb6
  reject "describe a configuration the run does not have" $P $A --carrier seg-g --regroup c
  reject "describe a configuration the run does not have" $P $A --carrier seg-g --pair-budget lb6
  reject "each own the whole rotation" $P --r9b-class --r9b-budget
  reject "each own the whole rotation" $P --r9b-class --reorder-factorial
  reject "multiple of 8" --mode lsb-pair --r9b-class --iterations 7
  reject "multiple of 8" --mode lsb-pair --r9b-budget --iterations 9
  reject "use --cache-arm" $P --r9b-class --validate
  reject "steers the bounded 128-thread cached kernel" $P --r9b-budget --carveout-hint 50
  reject "rotates lanes" $P --r9b-class --profile
  }
  note "  cells=$cells passed=$pass"
  cellrow "R9b rejection matrix" "$cells" "$pass"
  [ "$cells" = 28 ] || bad "R9b rejection cell count — cells that never ran are not a verdict either way" "28" "${cells}"
}

# ---------------------------------------------------------------- identity
#
# THE MACHINE THE REFERENCES CAME FROM — REPORTED, NEVER GATED (RR, 2026-08-13). Up to R9 every
# archived telemetry sidecar in this campaign recorded device STATE and never device IDENTITY, so no
# frozen anchor literal could be tied to a GPU; RR re-based the references on the R9b session precisely
# because that session recorded it. This cell closes the loop from the other side by PRINTING both
# identities — the live device's and the one committed inside `r4_table.py`'s baseline block — and
# saying plainly whether they are the same machine.
#
# It records NOTHING as a mismatch, not even a different GPU. A different GPU is not a wrong answer, it
# is a fact about where you are standing: it means the emitter's anchor deltas are CROSS-MACHINE and
# RR should re-base before reading them, which is a decision for RR on the whole picture and not a
# reason for this script to stop. Every future session driver should take its telemetry from
# `tools/gpu_identity.sh` (its header says so), so the gap cannot reopen in a per-rung script.
# THE ACCEPTED TRADE, recorded here so the next reader sees a choice and not an oversight: because this
# cell reports and never fails, a run on the WRONG MACHINE exits 0. The READING below is boxed and the
# matrix carries its row, but automation keying on the exit status alone will not see it. That is the
# direct consequence of RR's ruling that no gate rejects prematurely, and it is deliberate: a different
# GPU is not a wrong answer, it is a fact about where you are standing, and what to do about it is RR's
# call on the whole picture. If a machine check ever has to be enforceable, it belongs in the session
# driver that records the sidecar, not here.
identity() {
  local prev=$LANE
  lane_is identity
  note "### device IDENTITY (REPORT-ONLY — nothing here is a gate)"
  local live want field value missing=""
  if ! command -v nvidia-smi >/dev/null; then
    notrun "device identity" "no nvidia-smi on PATH, so the live device cannot be named"
    lane_is "$prev"
    return
  fi
  note "  query:    $(bash "$DIR/gpu_identity.sh" header)"
  note "  live:     $(bash "$DIR/gpu_identity.sh" identity)"
  # Every field the reference block declares. A hole here means a sidecar recorded from this helper
  # would carry a hole where the provenance is — reported, and still not a gate.
  for field in uuid serial driver_version vbios_version name compute_mode mig.mode.current; do
    value=$(bash "$DIR/gpu_identity.sh" field "$field")
    case "$value" in "" | "[N/A]" | "[Not Supported]") missing="$missing $field" ;; esac
  done
  [ -z "$missing" ] || note "  NOTE: the driver returns nothing for:$missing — a sidecar taken from this helper would have that hole in its provenance"
  # The committed uuid, read straight out of the emitter's baseline block — one literal, one owner.
  want=$(sed -n 's/^ *"uuid": "\(GPU-[0-9a-f-]*\)".*/\1/p' "$DIR/r4_table.py" | head -1)
  live=$(bash "$DIR/gpu_identity.sh" field uuid)
  note "  baseline: ${want:-<r4_table.py declares no uuid>}"
  if [ -z "$want" ]; then
    note "  READING:  r4_table.py's baseline block declares no uuid, so this run cannot say which machine its anchor references came from."
  elif [ "$live" = "$want" ]; then
    note "  READING:  SAME MACHINE — the live GPU is the one the committed anchor baseline was measured on, so the emitter's anchor deltas are same-machine."
  else
    note ""
    note "  ****************************************************************************"
    note "  READING:  DIFFERENT MACHINE. Live GPU is $live; the committed anchor baseline"
    note "            was measured on $want. Every anchor delta the emitter prints against"
    note "            that baseline is therefore CROSS-MACHINE and cannot be read as drift"
    note "            or as a change in the code. RR should re-base the reference block"
    note "            (the R9b Task 4 procedure) before reading any of them."
    note "            This is a READING, not a gate: nothing is rejected on it."
    note "  ****************************************************************************"
    note ""
  fi
  # A row on the board so the reading is visibly present, with zero cells because it gates nothing.
  cellrow "device identity (READING — 0 cells, nothing gated)" 0 0
  lane_is "$prev"
}

r9b() {
  lane_is r9b
  if [ ! -x "$B" ]; then
    notrun "the whole r9b lane" "no binary at $B — cargo build --release -p gpu_gkr_uniskip_bench"
    return
  fi
  # ENFORCED, as in the R9 lane: `r9b_rotation` pins every grid cell's static register count, which
  # the diagnostic build's counters move — run against it, the lane would fail for the wrong reason.
  if ! require_shipped "the R9b lane"; then
    notrun "the R9b cell groups" "BUILD-ORDER: the archive under it is not the SHIPPED build, so its pinned register counts would read another build's numbers"
    identity
    lane_is r9b
    return
  fi
  identity
  lane_is r9b
  r9b_q_parity
  r9b_echo_cells
  r9b_rotation
  r9b_rejects
}

# ---------------------------------------------------------------- r9bdiag

r9bdiag() {
  lane_is r9bdiag
  if ! ensure_diag; then
    notrun "the whole r9bdiag lane" "the diagnostic build did not complete, so no counter line exists"
    return
  fi
  note "### R9b chain executions per warp-program walk: every timed cell == the incumbent, per arm"
  local cells=0 pass=0 order arm inc got label flags
  for order in census locality; do
    for arm in $R9B_DIAG_ARMS; do
      inc=$(r9_walk_chains --cache-arm "$arm" --term-order "$order")
      if [ -z "$inc" ]; then
        bad "$arm order=$order printed no per-walk chain-count line (diagnostic build?)"; continue
      fi
      while IFS='|' read -r label flags; do
        [ -n "$label" ] || continue
        # shellcheck disable=SC2086
        got=$(r9_walk_chains --cache-arm "$arm" $flags --term-order "$order")
        cells=$((cells + 1))
        if [ "$got" = "$inc" ]; then pass=$((pass + 1))
        else bad "R9b chains $label/$arm order=$order: $got vs incumbent $inc"; fi
      done <<< "$R9B_CELLS"
      note "  $arm/$order: incumbent=$inc, all nine timed cells equal"
    done
  done
  note "  cells=$cells passed=$pass"
  cellrow "R9b chain executions per walk" "$cells" "$pass"
  [ "$cells" = 54 ] || bad "R9b chain cell count — cells that never ran are not a verdict either way" "54" "${cells}"

  # The prologue executes a PLAN; the repair moves decode, never what the plan is.
  note "### the per-walk plan line is the same plan on every timed cell"
  local pcells=0 ppass=0
  for order in census locality; do
    for arm in $R9B_DIAG_ARMS; do
      inc=$(r9_per_walk --cache-arm "$arm" --term-order "$order")
      if [ -z "$inc" ]; then
        bad "$arm order=$order printed no per-walk plan line (diagnostic build?)"; continue
      fi
      while IFS='|' read -r label flags; do
        [ -n "$label" ] || continue
        # shellcheck disable=SC2086
        got=$(r9_per_walk --cache-arm "$arm" $flags --term-order "$order")
        pcells=$((pcells + 1))
        if [ "$got" = "$inc" ]; then ppass=$((ppass + 1))
        else bad "R9b per-walk $label/$arm order=$order: '$got' vs '$inc'"; fi
      done <<< "$R9B_CELLS"
      note "  $arm/$order per walk: $inc"
    done
  done
  note "  cells=$pcells passed=$ppass"
  cellrow "R9b per-walk plan line" "$pcells" "$ppass"
  [ "$pcells" = 54 ] || bad "R9b per-walk cell count — cells that never ran are not a verdict either way" "54" "${pcells}"

  # POISON THE FRAME after the prologue: only an arm with reuses may change q, and every timed cell
  # must diverge exactly where the incumbent does. Equal POISONED hashes are stronger than
  # divergence — every cell reads one corrupted frame in one order.
  note "### frame poison after the prologue: every timed cell diverges where the incumbent does"
  local ccells=0 cpass=0 want igot iref ipoi ref poi
  for order in census locality; do
    for arm in $R9B_DIAG_ARMS; do
      iref=$(qhash --block-threads 128 --cache-arm "$arm" --term-order "$order")
      ipoi=$(qhash --block-threads 128 --cache-arm "$arm" --window-poison --term-order "$order")
      usable "$iref" "incumbent $arm order=$order" || continue
      usable "$ipoi" "incumbent poisoned $arm order=$order" || continue
      if [ "$arm" = cache0 ]; then want=same; else want=differ; fi
      igot=same; [ "$iref" != "$ipoi" ] && igot=differ
      if [ "$igot" != "$want" ]; then
        bad "R9b poison incumbent/$arm order=$order: $igot, want $want"
      fi
      while IFS='|' read -r label flags; do
        [ -n "$label" ] || continue
        # shellcheck disable=SC2086
        ref=$(qhash --block-threads 128 --cache-arm "$arm" $flags --term-order "$order")
        # shellcheck disable=SC2086
        poi=$(qhash --block-threads 128 --cache-arm "$arm" $flags --window-poison \
                    --term-order "$order")
        usable "$ref" "$label $arm order=$order" || continue
        usable "$poi" "$label $arm poisoned order=$order" || continue
        got=same; [ "$ref" != "$poi" ] && got=differ
        ccells=$((ccells + 1))
        if [ "$got" = "$want" ]; then cpass=$((cpass + 1))
        else bad "R9b poison $label/$arm order=$order: $got, want $want"; fi
        ccells=$((ccells + 1))
        if [ "$got" = "$igot" ]; then cpass=$((cpass + 1))
        else bad "R9b poison $label/$arm order=$order: cell $got but incumbent $igot"; fi
        ccells=$((ccells + 1))
        if [ "$poi" = "$ipoi" ]; then cpass=$((cpass + 1))
        else bad "R9b poisoned q $label/$arm order=$order: $poi vs incumbent $ipoi"; fi
      done <<< "$R9B_CELLS"
      note "  poison $arm/$order: incumbent=$igot (want $want), all nine cells match cell for cell"
    done
  done
  # The uncached control has no frame to poison.
  ref=$(qhash --block-threads 128 --term-order locality)
  poi=$(qhash --block-threads 128 --window-poison --term-order locality)
  if usable "$ref" "control128 locality" && usable "$poi" "control128 poisoned locality"; then
    ccells=$((ccells + 1))
    if [ "$ref" = "$poi" ]; then cpass=$((cpass + 1))
    else bad "R9b poison changed the uncached control" "$poi" "$ref"; fi
  fi
  note "  cells=$ccells passed=$cpass"
  cellrow "R9b frame poison" "$ccells" "$cpass"
  [ "$ccells" = 163 ] || bad "R9b poison cell count — cells that never ran are not a verdict either way" "163" "${ccells}"
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
    # All THREE properties are read for every symbol, whatever the others said: a moved count used
    # to hide the digest and the resource line behind it, and those are different readings.
    local sym_ok=1
    if [ "$got" != "$want" ]; then
      bad "$fn normalized instruction count" "$want" "$got"; sym_ok=0
    fi
    if [ "$dig" != "$digest" ]; then
      bad "$fn body digest — the body changed at a constant instruction count" "$digest" "$dig"
      sym_ok=0
    fi
    case "$res" in
      "REG:72 STACK:0 SHARED:$shared LOCAL:0 CONSTANT[0]:"*) ;;
      *) bad "$fn resource usage" "REG:72 STACK:0 SHARED:$shared LOCAL:0" "$res"; sym_ok=0 ;;
    esac
    [ "$sym_ok" = 1 ] && ok=$((ok + 1))
    note "  $fn: $got instrs, digest $dig, $res"
  done <<< "$SEG_SYMBOLS"
  note "  seg bodies $ok/$rows pinned"
  cellrow "the eight seg symbols" "$rows" "$ok"
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
  [ "$rows" = 8 ] || bad "seg symbols read — a symbol that never got read is not a verdict either way" "8" "$rows"
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
    # All THREE properties, for every symbol, whatever the others said (see `seg_sass`).
    local sym_ok=1
    if [ "$got" != "$want" ]; then
      bad "$fn normalized instruction count" "$want" "$got"; sym_ok=0
    fi
    if [ "$dig" != "$digest" ]; then
      bad "$fn body digest — the body changed at a constant instruction count" "$digest" "$dig"
      sym_ok=0
    fi
    case "$res" in
      "REG:$reg STACK:0 SHARED:$shared LOCAL:0 CONSTANT[0]:"*) ;;
      *) bad "$fn resource usage" "REG:$reg STACK:0 SHARED:$shared LOCAL:0" "$res"; sym_ok=0 ;;
    esac
    [ "$sym_ok" = 1 ] && ok=$((ok + 1))
    note "  $fn: $got instrs, digest $dig, $res"
  done <<< "$REORDER_SYMBOLS"
  note "  reorder bodies $ok/$rows pinned"
  cellrow "the two R9 gate-first symbols" "$rows" "$ok"
  [ "$rows" = 2 ] || bad "R9 symbols read — a symbol that never got read is not a verdict either way" "2" "$rows"
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
    # All THREE properties, for every symbol, whatever the others said (see `seg_sass`).
    local sym_ok=1
    if [ "$got" != "$want" ]; then
      bad "$fn normalized instruction count" "$want" "$got"; sym_ok=0
    fi
    if [ "$dig" != "$digest" ]; then
      bad "$fn body digest — the body changed at a constant instruction count" "$digest" "$dig"
      sym_ok=0
    fi
    case "$res" in
      "REG:$reg STACK:0 SHARED:$shared LOCAL:0 CONSTANT[0]:"*) ;;
      *) bad "$fn resource usage" "REG:$reg STACK:0 SHARED:$shared LOCAL:0" "$res"; sym_ok=0 ;;
    esac
    [ "$sym_ok" = 1 ] && ok=$((ok + 1))
    note "  $fn: $got instrs, digest $dig, $res"
  done <<< "$R9B_SYMBOLS"
  note "  R9b grid bodies $ok/$rows pinned"
  cellrow "the R9b grid (body x budget)" "$rows" "$ok"
  [ "$rows" = 20 ] || bad "R9b grid symbols read — a symbol that never got read is not a verdict either way" "20" "$rows"
}

r10_sass() {
  note "### the R10 grid: state x level x parent walk, instruction counts, digests, registers"
  local ar=$ARCHIVE work="$TMP/sass-r10" ar_abs
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
    # All THREE properties, for every symbol, whatever the others said (see `seg_sass`).
    local sym_ok=1
    if [ "$got" != "$want" ]; then
      bad "$fn normalized instruction count" "$want" "$got"; sym_ok=0
    fi
    if [ "$dig" != "$digest" ]; then
      bad "$fn body digest — the body changed at a constant instruction count" "$digest" "$dig"
      sym_ok=0
    fi
    case "$res" in
      "REG:$reg STACK:0 SHARED:$shared LOCAL:0 CONSTANT[0]:"*) ;;
      *) bad "$fn resource usage" "REG:$reg STACK:0 SHARED:$shared LOCAL:0" "$res"; sym_ok=0 ;;
    esac
    [ "$sym_ok" = 1 ] && ok=$((ok + 1))
    note "  $fn: $got instrs, digest $dig, $res"
  done <<< "$R10_SYMBOLS"
  note "  R10 grid bodies $ok/$rows pinned"
  cellrow "the R10 grid (state x level x parent)" "$rows" "$ok"
  [ "$rows" = 24 ] || bad "R10 grid symbols read — a symbol that never got read is not a verdict either way" "24" "$rows"
}

sass() {
  lane_is sass
  note "### frozen SASS: r5_gates.sh sass, the nine R3/R4 bodies (one table, one owner)"
  if ! require_shipped "the SASS lane"; then
    notrun "the whole sass lane" "BUILD-ORDER: the archive under it is not the SHIPPED build, so its digests and register lines would be another build's"
    return
  fi
  local out rc
  out=$("$DIR/r5_gates.sh" sass 2>&1); rc=$?
  printf '%s\n' "$out" | grep -E '^(  archive:|  IDENTICAL|  frozen bodies|FAIL: )' \
    | awk '{print "    " $0}'
  local frozen_ok=1
  [ "$rc" = 0 ] || { bad "r5_gates.sh sass exit status" "0" "$rc"; frozen_ok=0; }
  grep -q '^  frozen bodies 9/9 identical' <<< "$out" \
    || { bad "the nine frozen R3/R4 bodies" "frozen bodies 9/9 identical" \
             "$(grep -m1 '^  frozen bodies' <<< "$out" || echo absent)"; frozen_ok=0; }
  cellrow "frozen R3/R4 bodies (via r5_gates.sh sass)" 1 "$frozen_ok"
  seg_sass
  reorder_sass
  r9b_sass
  r10_sass
}

# ---------------------------------------------------------------- cpu / fixtures / regression

cpu() {
  lane_is cpu
  if ! ensure_shipped; then
    notrun "the whole cpu lane" "the shipped rebuild did not complete, so the tests would run against the diagnostic build"
    return
  fi
  note "### GPU-free unit tests (cpu_*)"
  local result
  if RUSTFLAGS=-Awarnings cargo test -p gpu_gkr_uniskip_bench --lib --release cpu_ \
       > "$TMP/cpu.log" 2>&1 9>&-; then
    result=$(grep -E '^test result:' "$TMP/cpu.log" | tail -1)
    note "  $result"
    cellrow "cpu unit tests" 1 1
  else
    result=$(grep -E '^test result:' "$TMP/cpu.log" | tail -1)
    bad "cpu unit tests" "test result: ok" "${result:-<the run produced no test result line>}"
    cellrow "cpu unit tests" 1 0
    grep -E 'FAILED|panicked|^error|^test result:' "$TMP/cpu.log" | tail -20
  fi
}

fixtures() {
  lane_is fixtures
  note "### emitter fixture matrix (tools/r7_table.py)"
  if bash "$FIXTURES" > "$TMP/fixtures.log" 2>&1; then
    note "  $(tail -1 "$TMP/fixtures.log")"
    cellrow "r7 emitter fixtures" 1 1
  else
    # The sub-suite already printed its OWN whole matrix; carry its summary line into this one and
    # then reproduce its transcript, so nothing it found is lost behind a single red cell.
    bad "r7 emitter fixtures" "0 failed" "$(tail -1 "$TMP/fixtures.log")"
    cellrow "r7 emitter fixtures" 1 0
    cat "$TMP/fixtures.log"
  fi
  # The R9 rung rides r4_table.py, whose R5/R8 paths r5_gates.sh owns; its OWN fixture matrix is
  # gated here, beside the rest of R9.
  note "### emitter fixture matrix (tools/r4_table.py, R9 reorder path)"
  if bash "$R9FIXTURES" > "$TMP/r9-fixtures.log" 2>&1; then
    note "  $(tail -1 "$TMP/r9-fixtures.log")"
    cellrow "R9 emitter fixtures" 1 1
  else
    # The sub-suite already printed its OWN whole matrix; carry its summary line into this one and
    # then reproduce its transcript, so nothing it found is lost behind a single red cell.
    bad "R9 emitter fixtures" "0 failed" "$(tail -1 "$TMP/r9-fixtures.log")"
    cellrow "R9 emitter fixtures" 1 0
    cat "$TMP/r9-fixtures.log"
  fi
  # The R9b rung rides the same emitter on its own dedicated path — two rotations under one tag, which
  # is what its fixture corpus is mostly about.
  note "### emitter fixture matrix (tools/r4_table.py, R9b two-rotation path)"
  if bash "$R9BFIXTURES" > "$TMP/r9b-fixtures.log" 2>&1; then
    note "  $(tail -1 "$TMP/r9b-fixtures.log")"
    cellrow "R9b emitter fixtures" 1 1
  else
    # The sub-suite already printed its OWN whole matrix; carry its summary line into this one and
    # then reproduce its transcript, so nothing it found is lost behind a single red cell.
    bad "R9b emitter fixtures" "0 failed" "$(tail -1 "$TMP/r9b-fixtures.log")"
    cellrow "R9b emitter fixtures" 1 0
    cat "$TMP/r9b-fixtures.log"
  fi
}

regression() {
  lane_is regression
  # r5_gates.sh all starts with its OWN sass lane, which needs the shipped archive; it then builds
  # and restores its own diagnostic binary.
  if ! ensure_shipped; then
    notrun "the whole regression lane" "the shipped rebuild did not complete, so r5_gates.sh would gate the diagnostic build"
    return
  fi
  note "### regression: r5_gates.sh all (chains r3 + r4)"
  local out rc
  out=$("$DIR/r5_gates.sh" all 2>&1); rc=$?
  # r5_gates.sh reports the whole matrix too (and chains r3 + r4, which do as well), so what is echoed
  # here is its BOARD — every cell-group row, its totals, its NOT RUN and MISMATCHES blocks — not a
  # verdict line. A nested gate's matrix is part of this matrix.
  printf '%s\n' "$out" \
    | grep -E '^(  cells=|  oracle cells=|  gated lanes=|  gated arms=|  frozen bodies|  ARM lines|MISMATCH|NOT RUN|\| |### (NOT RUN|MISMATCHES)|\*\*)' \
    | awk '{print "    " $0}'
  local nested ncells nok nbad
  nested=$(grep -m1 '^| \*\*total\*\* |' <<< "$out")
  [ "$rc" = 0 ] || bad "r5_gates.sh all exit status" "0" "$rc"
  if [ -z "$nested" ]; then
    notrun "regression: r5_gates.sh all" "it printed no totals row, so its matrix cannot be carried into this one"
    cellrow "regression: r5_gates.sh all (chains r3 + r4)" 1 0
  else
    # THE NESTED RESULT, carried into this script's own matrix rather than collapsed to pass/fail.
    ncells=$(sed -E 's/.*\| \*\*([0-9]+)\*\* \| \*\*[0-9]+\*\* \| \*\*[0-9]+\*\* \|.*/\1/' <<< "$nested")
    nok=$(sed -E 's/.*\| \*\*[0-9]+\*\* \| \*\*([0-9]+)\*\* \| \*\*[0-9]+\*\* \|.*/\1/' <<< "$nested")
    nbad=$(sed -E 's/.*\| \*\*[0-9]+\*\* \| \*\*[0-9]+\*\* \| \*\*([0-9]+)\*\* \|.*/\1/' <<< "$nested")
    note "  nested board: ${ncells:-?} cells, ${nok:-?} matched, ${nbad:-?} mismatched"
    cellrow "regression: r5_gates.sh all (nested board, chains r3 + r4)" "${ncells:-1}" "${nok:-0}"
    [ "${nbad:-0}" = 0 ] || bad "r5_gates.sh all nested mismatches" "0" "$nbad"
  fi
}

case "${1:-all}" in
  matrix) matrix ;;
  counts) counts ;;
  r9) r9 ;;
  r9diag) r9diag ;;
  r9b) r9b ;;
  r9bdiag) r9bdiag ;;
  identity) identity ;;
  sass) sass ;;
  cpu) cpu ;;
  fixtures) fixtures ;;
  regression) regression ;;
  # THE BUILD-FLAVOUR ORDERING, stated rather than left incidental. Three lanes read the SHIPPED
  # archive's own numbers (`sass`'s digests and register lines, `r9`'s and `r9b`'s pinned register
  # counts) and `counts` swaps the binary underneath everything after it, so the shipped-build lanes
  # run FIRST, the diagnostic lanes run while that build is up, and every later lane asks for the
  # shipped one back. `sass` runs LAST as well, and that is not belt-and-braces: the diagnostic
  # round-trip recompiles the seg TU twice, and r5's own sass lane (which `regression` inherits) covers
  # the frozen NINE only — without the re-gate the binary the tree ENDS on would never have had the
  # eight seg bodies verified. No lane may be appended after it that can rebuild.
  #
  # If that ordering is ever broken, `require_shipped` SAYS so, marks its lane NOT RUN with the reason,
  # and the chain carries on to its last lane regardless — a broken order costs those cells, never the
  # board.
  all)
    sass; matrix; r9; r9b; counts; r9diag; r9bdiag; cpu; fixtures; regression
    note ""
    note "### RE-GATE after the diagnostic round-trip: the binary the tree ENDS on"
    sass
    ;;
  *) echo "usage: $0 {sass|matrix|counts|r9|r9diag|r9b|r9bdiag|identity|cpu|fixtures|regression|all}" >&2; exit 2 ;;
esac
gate_summary
exit "$fail"
