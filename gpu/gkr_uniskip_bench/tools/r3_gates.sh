#!/usr/bin/env bash
# v3 R3 window-arm gates, executable rather than transcribed.
#
# The Task 2 record originally existed only as report prose; this runs it. Two modes,
# because the counter and the mutations need device symbols that a shipped build does not
# carry:
#
#   shipped   q-parity matrix (32 cells)                     — the default build
#   diag      production-count gate + device mutations       — GPU_GKR_UNISKIP_BENCH_WINDOW_DIAG=1
#
# Usage, from the repo root:
#   cargo build --release -p gpu_gkr_uniskip_bench
#   .agents/bin/with_gpu_lock.sh gpu/gkr_uniskip_bench/tools/r3_gates.sh matrix
#
#   GPU_GKR_UNISKIP_BENCH_WINDOW_DIAG=1 cargo build --release -p gpu_gkr_uniskip_bench
#   .agents/bin/with_gpu_lock.sh gpu/gkr_uniskip_bench/tools/r3_gates.sh diag
#
# Exit status is the gate verdict: non-zero if any cell fails.
set -uo pipefail

B=${B:-target/release/gpu_gkr_uniskip_bench}
ARMS="t w wt wnone"
fail=0
note() { printf '%s\n' "$*"; }
bad() { printf 'FAIL: %s\n' "$*"; fail=1; }

qhash() { "$B" --log-trace 12 --iterations 0 --dump-q --mode lsb-pair "$@" | grep '^q\[' | sha256sum | cut -c1-12; }

matrix() {
  note "### q parity: 4 arms x 2 orders x 2 eq forms x 2 censuses"
  local cells=0 pass=0
  for order in census locality; do
    for eq in "" "--validate-flat-eq"; do
      for sp in 0 12; do
        # shellcheck disable=SC2086
        local ref; ref=$(qhash --term-order "$order" --self-products "$sp" $eq)
        for arm in $ARMS; do
          cells=$((cells + 1))
          # shellcheck disable=SC2086
          local got; got=$(qhash --pair-arm "$arm" --term-order "$order" --self-products "$sp" $eq)
          if [ "$got" = "$ref" ]; then pass=$((pass + 1));
          else bad "parity arm=$arm order=$order eq=[$eq] self-products=$sp ($got vs $ref)"; fi
        done
      done
    done
  done
  note "  cells=$cells passed=$pass"
  [ "$cells" = "$pass" ] || bad "parity matrix incomplete"
}

# Chain executions per warp-program walk. The tiny geometry keeps the counter's atomic off
# the critical path and makes one block the whole grid.
count() { "$B" --log-trace 9 --warmup 0 --iterations 1 --mode lsb-pair "$@" --window-count \
  | sed -n 's/^chain executions .*= \([0-9]*\) per warp-program walk$/\1/p'; }

production() {
  note "### production-count gate (exact)"
  for order in census locality; do
    for spec in "control:326" "wnone:326" "w:279" "wt:279"; do
      local arm=${spec%%:*} want=${spec##*:} a=() got
      [ "$arm" != control ] && a=(--pair-arm "$arm")
      got=$(count "${a[@]}" --term-order "$order")
      if [ "$got" = "$want" ]; then note "  $arm/$order = $got"
      else bad "count arm=$arm order=$order got=${got:-<none>} want=$want"; fi
    done
  done
}

mutations() {
  note "### mutation (a) retarget a live slot holding another source -> q must diverge"
  for arm in w wt; do
    for order in census locality; do
      local ref mut
      ref=$(qhash --pair-arm "$arm" --term-order "$order")
      mut=$(qhash --pair-arm "$arm" --term-order "$order" --window-mutate retarget)
      if [ "$ref" != "$mut" ]; then note "  $arm/$order diverges ($ref -> $mut)"
      else bad "retarget arm=$arm order=$order did not change q"; fi
    done
  done
  note "### mutation (b) poison a slot after its fill -> only arms with reuses may change"
  for spec in "control:same" "wnone:same" "w:diff" "wt:diff"; do
    local arm=${spec%%:*} want=${spec##*:} a=() ref poi got
    [ "$arm" != control ] && a=(--pair-arm "$arm")
    ref=$(qhash "${a[@]}" --term-order locality)
    poi=$(qhash "${a[@]}" --term-order locality --window-poison)
    [ "$ref" = "$poi" ] && got=same || got=diff
    if [ "$got" = "$want" ]; then note "  $arm: $got ($ref${_:+})"
    else bad "poison arm=$arm got=$got want=$want"; fi
  done
}

case "${1:-all}" in
  matrix) matrix ;;
  diag) production; mutations ;;
  all) matrix; production; mutations ;;
  *) echo "usage: $0 {matrix|diag|all}" >&2; exit 2 ;;
esac
[ "$fail" = 0 ] && note "ALL GATES PASS"
exit "$fail"
