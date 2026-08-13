#!/usr/bin/env bash
# v3 R3 window-arm gates, executable rather than transcribed.
#
# The Task 2 record originally existed only as report prose; this runs it. Two modes,
# because the counter and the mutations need device symbols that a shipped build does not
# carry:
#
#   matrix    q-parity, 40 cells                             — runs on EITHER build
#   blocks    128-vs-256 block-size parity, 8 cells (v3 R4)  — runs on EITHER build
#   diag      production-count gate + device mutations       — needs GPU_GKR_UNISKIP_BENCH_WINDOW_DIAG=1
#   all       matrix + blocks + diag, so it needs a diagnostic build
#
# The parity matrix is normally run on the shipped build, because that is the binary the
# arms are timed with; `all` is only valid on a diagnostic one.
#
# Usage, from the repo root:
#   cargo build --release -p gpu_gkr_uniskip_bench
#   .agents/bin/with_gpu_lock.sh gpu/gkr_uniskip_bench/tools/r3_gates.sh matrix
#
#   .agents/bin/with_gpu_lock.sh gpu/gkr_uniskip_bench/tools/r3_gates.sh blocks
#
#   GPU_GKR_UNISKIP_BENCH_WINDOW_DIAG=1 cargo build --release -p gpu_gkr_uniskip_bench
#   .agents/bin/with_gpu_lock.sh gpu/gkr_uniskip_bench/tools/r3_gates.sh diag   # or: all
#
# Exit status is the gate verdict: non-zero if any cell fails.
set -uo pipefail

B=${B:-target/release/gpu_gkr_uniskip_bench}
ARMS="t w wt wnone wtnone"
DIR=$(cd "$(dirname "$0")" && pwd)
# The whole-matrix reporting layer, shared by every gate script here: nothing is rejected on a gate
# prematurely, the run always ends with the full board (RR, 2026-08-13).
# shellcheck source=gate_report.sh
. "$DIR/gate_report.sh"

# Empty input hashes to a fixed digest, so a missing binary or a failed run would make
# BOTH sides of a comparison equal and every parity cell pass vacuously. Reject that.
EMPTY_SHA=e3b0c44298fc
# NOTE: qhash runs inside a command substitution, so it must never call bad() — the
# assignment to `fail` would be made in the subshell and lost. Diagnostics go to stderr and
# the sentinel INVALID comes back on stdout; usable(), which runs in the parent, is what
# sets `fail`.
qhash() {
  local out rc
  out=$("$B" --log-trace 12 --iterations 0 --dump-q --mode lsb-pair "$@" 2>/dev/null)
  rc=$?
  if [ "$rc" != 0 ]; then echo "  qhash: run failed (exit $rc): $*" >&2; echo INVALID; return; fi
  out=$(printf '%s\n' "$out" | grep -c '^q\[')
  if [ "$out" != 32 ]; then echo "  qhash: expected 32 q lines, got $out: $*" >&2; echo INVALID; return; fi
  "$B" --log-trace 12 --iterations 0 --dump-q --mode lsb-pair "$@" 2>/dev/null \
    | grep '^q\[' | sha256sum | cut -c1-12
}

# Any comparison that could be satisfied by two equal failures must reject the sentinel.
usable() {
  case "$1" in
    INVALID | "$EMPTY_SHA" | "") bad "unusable digest '$1' for: ${2:-}"; return 1 ;;
    *) return 0 ;;
  esac
}

matrix() {
  lane_is matrix
  note "### q parity: 5 arms x 2 orders x 2 eq forms x 2 censuses"
  local cells=0 pass=0
  for order in census locality; do
    for eq in "" "--validate-flat-eq"; do
      for sp in 0 12; do
        # shellcheck disable=SC2086
        local ref; ref=$(qhash --term-order "$order" --self-products "$sp" $eq)
        usable "$ref" "control order=$order eq=[$eq] sp=$sp" || continue
        for arm in $ARMS; do
          cells=$((cells + 1))
          # shellcheck disable=SC2086
          local got; got=$(qhash --pair-arm "$arm" --term-order "$order" --self-products "$sp" $eq)
          usable "$got" "arm=$arm order=$order eq=[$eq] sp=$sp" || continue
          if [ "$got" = "$ref" ]; then pass=$((pass + 1));
          else bad "parity arm=$arm order=$order eq=[$eq] self-products=$sp ($got vs $ref)"; fi
        done
      done
    done
  done
  note "  cells=$cells passed=$pass"
  cellrow "q parity (5 arms x order x eq x census)" "$cells" "$pass"
}

# v3 R4 control128: the 128-thread no-cache baseline must agree with the 256 control on `q`
# across the full validate set. Its own kernel, its own grid and its own epilogue reduction,
# so this is a real re-derivation of every cell, not a launch-parameter change.
blocks() {
  lane_is blocks
  note "### block-size parity: control128 vs the 256 control, 2 orders x 2 eq forms x 2 censuses"
  local cells=0 pass=0
  for order in census locality; do
    for eq in "" "--validate-flat-eq"; do
      for sp in 0 12; do
        cells=$((cells + 1))
        # shellcheck disable=SC2086
        local ref; ref=$(qhash --term-order "$order" --self-products "$sp" $eq)
        usable "$ref" "256 control order=$order eq=[$eq] sp=$sp" || continue
        # shellcheck disable=SC2086
        local got; got=$(qhash --block-threads 128 --term-order "$order" --self-products "$sp" $eq)
        usable "$got" "control128 order=$order eq=[$eq] sp=$sp" || continue
        if [ "$got" = "$ref" ]; then pass=$((pass + 1));
        else bad "block parity order=$order eq=[$eq] self-products=$sp ($got vs $ref)"; fi
      done
    done
  done
  note "  cells=$cells passed=$pass"
  cellrow "block-size parity (control128 vs 256)" "$cells" "$pass"
}

# Chain executions per warp-program walk. The tiny geometry keeps the counter's atomic off
# the critical path and makes one block the whole grid.
count() { "$B" --log-trace 9 --warmup 0 --iterations 1 --mode lsb-pair "$@" --window-count \
  | sed -n 's/^chain executions .*= \([0-9]*\) per warp-program walk$/\1/p'; }

production() {
  lane_is production
  note "### production-count gate (exact)"
  local cells=0 pass=0
  for order in census locality; do
    for spec in "control:326" "wnone:326" "wtnone:326" "w:279" "wt:279"; do
      local arm=${spec%%:*} want=${spec##*:} got
      local -a a=()
      [ "$arm" != control ] && a=(--pair-arm "$arm")
      got=$(count "${a[@]}" --term-order "$order")
      cells=$((cells + 1))
      if [ -z "$got" ]; then
        notrun "production count $arm/$order" "the run printed no chain-count line (diagnostic build?)"
      elif [ "$got" = "$want" ]; then pass=$((pass + 1)); note "  $arm/$order = $got"
      else bad "production chain count $arm/$order" "$want" "$got"; fi
    done
  done
  note "  cells=$cells passed=$pass"
  cellrow "production chain counts" "$cells" "$pass"
}

mutations() {
  lane_is mutations
  local rcells=0 rpass=0 pcells=0 ppass=0
  note "### mutation (a) retarget a live slot holding another source -> q must diverge"
  for arm in w wt; do
    for order in census locality; do
      local ref mut
      ref=$(qhash --pair-arm "$arm" --term-order "$order")
      mut=$(qhash --pair-arm "$arm" --term-order "$order" --window-mutate retarget)
      usable "$ref" "retarget ref $arm/$order" || continue
      usable "$mut" "retarget mut $arm/$order" || continue
      rcells=$((rcells + 1))
      if [ "$ref" != "$mut" ]; then rpass=$((rpass + 1)); note "  $arm/$order diverges ($ref -> $mut)"
      else bad "retarget arm=$arm order=$order q" "a digest different from $ref" "$mut"; fi
    done
  done
  note "  cells=$rcells passed=$rpass"
  cellrow "mutation (a) retarget diverges" "$rcells" "$rpass"
  note "### mutation (b) poison a slot after its fill -> only arms with reuses may change"
  for spec in "control:same" "wnone:same" "wtnone:same" "w:diff" "wt:diff"; do
    local arm=${spec%%:*} want=${spec##*:} ref poi got
    local -a a=()
    [ "$arm" != control ] && a=(--pair-arm "$arm")
    ref=$(qhash "${a[@]}" --term-order locality)
    poi=$(qhash "${a[@]}" --term-order locality --window-poison)
    # The "same" rows are exactly the ones two equal failures could fake.
    usable "$ref" "poison ref $arm" || continue
    usable "$poi" "poison $arm" || continue
    if [ "$ref" = "$poi" ]; then got=same; else got=diff; fi
    pcells=$((pcells + 1))
    if [ "$got" = "$want" ]; then ppass=$((ppass + 1)); note "  $arm: $got ($ref -> $poi)"
    else bad "poison arm=$arm" "$want" "$got"; fi
  done
  note "  cells=$pcells passed=$ppass"
  cellrow "mutation (b) poison behaviour" "$pcells" "$ppass"
}

case "${1:-all}" in
  matrix) matrix ;;
  blocks) blocks ;;
  diag) production; mutations ;;
  all) matrix; blocks; production; mutations ;;
  *) echo "usage: $0 {matrix|blocks|diag|all}" >&2; exit 2 ;;
esac
gate_summary
exit "$fail"
