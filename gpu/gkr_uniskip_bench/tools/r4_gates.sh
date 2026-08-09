#!/usr/bin/env bash
# v3 R4 coset-cache gates, executable rather than transcribed.
#
#   matrix    q parity: 7 cached arms x 2 block sizes x 2 orders x 2 eq forms x 2 censuses,
#             plus the bounded-vs-unbounded pairs at 128 — runs on EITHER build
#   counts    ncu instruction/sector/H-load gates vs the oracle — EITHER build, needs ncu
#   diag      chain-count gate + device mutations — needs GPU_GKR_UNISKIP_BENCH_WINDOW_DIAG=1
#   all       matrix + counts + diag, so it needs a diagnostic build
#
# Usage, from the repo root:
#   cargo build --release -p gpu_gkr_uniskip_bench
#   .agents/bin/with_gpu_lock.sh gpu/gkr_uniskip_bench/tools/r4_gates.sh matrix
#
#   GPU_GKR_UNISKIP_BENCH_WINDOW_DIAG=1 cargo build --release -p gpu_gkr_uniskip_bench
#   .agents/bin/with_gpu_lock.sh gpu/gkr_uniskip_bench/tools/r4_gates.sh diag   # or: all
#
# Exit status is the gate verdict: non-zero if any cell fails.
set -uo pipefail

B=${B:-target/release/gpu_gkr_uniskip_bench}
ARMS="cache0 hot4 hot16 allrepeat all59 e4rich e4top2"
fail=0
note() { printf '%s\n' "$*"; }
bad() { printf 'FAIL: %s\n' "$*"; fail=1; }

# qhash runs inside a command substitution, so it must never call bad() — the assignment
# would be made in the subshell and lost. Diagnostics go to stderr, INVALID comes back on
# stdout, and usable() in the parent is what sets `fail`.
EMPTY_SHA=e3b0c44298fc
# ONE launch per cell: the captured output is both counted and hashed. Launching twice
# doubles lock time and, worse, a divergence between the two launches would be invisible.
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

matrix() {
  note "### q parity: 7 cached arms x 2 sizes x 2 orders x 2 eq forms x 2 censuses"
  local cells=0 pass=0
  for size in "" "--block-threads 128"; do
    for order in census locality; do
      for eq in "" "--validate-flat-eq"; do
        for sp in 0 12; do
          # shellcheck disable=SC2086
          local ref; ref=$(qhash $size --term-order "$order" --self-products "$sp" $eq)
          usable "$ref" "control size=[$size] order=$order eq=[$eq] sp=$sp" || continue
          for arm in $ARMS; do
            cells=$((cells + 1))
            # shellcheck disable=SC2086
            local got; got=$(qhash $size --cache-arm "$arm" --term-order "$order" --self-products "$sp" $eq)
            usable "$got" "arm=$arm size=[$size] order=$order eq=[$eq] sp=$sp" || continue
            if [ "$got" = "$ref" ]; then pass=$((pass + 1));
            else bad "parity arm=$arm size=[$size] order=$order eq=[$eq] sp=$sp ($got vs $ref)"; fi
          done
        done
      done
    done
  done
  note "  cells=$cells passed=$pass"
  # A dropped loop dimension would otherwise pass silently with fewer cells.
  [ "$cells" = 112 ] || bad "expected 112 parity cells, ran $cells — a loop dimension is missing"
  [ "$cells" = "$pass" ] || bad "parity matrix incomplete"

  # The two launch-bounds siblings at 128 must agree with the unbounded bodies they mirror.
  note "### 128 launch-bounds siblings"
  local a b
  a=$(qhash --block-threads 128 --cache-arm allrepeat)
  b=$(qhash --block-threads 128 --cache-arm allrepeat --no-cache-launch-bounds)
  usable "$a" "cached_128_lb" && usable "$b" "cached_128" && {
    [ "$a" = "$b" ] && note "  cached: bounded == unbounded ($a)" || bad "cached bounded/unbounded differ"; }
  a=$(qhash --block-threads 128)
  b=$(qhash --block-threads 128 --control-launch-bounds)
  usable "$a" "control128" && usable "$b" "control128_lb" && {
    [ "$a" = "$b" ] && note "  control: control128 == control128_lb ($a)" || bad "control128/lb differ"; }

  # CPU oracle once per arm per size — the only leg that does not go through `q` alone.
  note "### CPU oracle (--validate), one cell per arm per size"
  local oks=0 runs=0
  for size in "" "--block-threads 128"; do
    for arm in $ARMS; do
      runs=$((runs + 1))
      # shellcheck disable=SC2086
      if "$B" --log-trace 10 --warmup 0 --iterations 1 --mode lsb-pair $size --cache-arm "$arm" \
           --validate 2>/dev/null | grep -q '^q validate: OK (32/32)'; then oks=$((oks + 1));
      else bad "CPU oracle arm=$arm size=[$size]"; fi
    done
  done
  note "  oracle cells=$runs passed=$oks"
  [ "$runs" = 14 ] || bad "expected 14 oracle cells, ran $runs"
  [ "$runs" = "$oks" ] || bad "CPU oracle incomplete"
}

# spec 4's local-traffic table, measured directly. `--log-trace 9` is one 256-thread block =
# 8 warps, so a per-walk figure is the counter over 8. The metric NAMES matter: on sm_120 the
# LDL/STL warp-instruction counters are `smsp__inst_executed_op_local_{ld,st}`, NOT the
# `..._op_ldl/stl` spelling (which does not exist on this chip and reports n/a).
#
# Instructions and sectors are gated SEPARATELY on purpose. The sector totals prove bytes
# and the absence of over-fetch, but they do NOT determine the instruction mix: hot16's 224
# store-sectors per warp fit both (12 BF, 8 E4-halves) and (28 BF, 0). Only the direct
# counter settles it.
NCU_LOCAL_METRICS=smsp__inst_executed_op_local_ld.sum,smsp__inst_executed_op_local_st.sum,\
smsp__inst_executed_op_local_ld_pred_off_all.sum,smsp__inst_executed_op_local_st_pred_off_all.sum,\
l1tex__t_sectors_pipe_lsu_mem_local_op_ld.sum,l1tex__t_sectors_pipe_lsu_mem_local_op_st.sum,\
l1tex__t_bytes_pipe_lsu_mem_global_op_ld.sum

metric() { # metric() <arm> -> "name value" lines for one small-geometry capture.
  # Run this lane UNDER the lock like every other; ncu is invoked directly here.
  ncu --metrics "$NCU_LOCAL_METRICS" --kernel-name-base demangled \
      --kernel-name 'regex:ab_gkr_uniskip_eval_lsb_pair_cached_kernel' --launch-count 1 \
      --target-processes all --csv "$B" --log-trace 9 --warmup 0 --iterations 1 \
      --mode lsb-pair --cache-arm "$1" 2>/dev/null \
    | awk -F'","' 'NR>1 && $13 ~ /smsp__|l1tex__/ {gsub(/"/,"",$13); gsub(/"/,"",$15); print $13, $15}'
}

# Oracle rows: arm C B E R_B R_E (from .agents/sdd/2026-08-09-v3-r4/expected-counts.md).
COUNT_ORACLE="cache0 0 0 0 0 0
hot4 4 4 0 51 0
hot16 28 12 4 93 20
allrepeat 88 44 11 186 34
e4rich 44 0 11 0 34
e4top2 8 0 2 0 14
all59 92 48 11 190 34"

counts() {
  note "### local instruction / sector / prologue-H gates (ncu, 1 block x 8 warps)"
  note "  metrics: $NCU_LOCAL_METRICS"
  local base=""
  while read -r arm C Bc E RB RE; do
    [ -n "$arm" ] || continue
    local out; out=$(metric "$arm")
    if [ -z "$out" ]; then bad "no ncu output for $arm"; continue; fi
    get() { printf '%s\n' "$out" | awk -v k="$1" '$1==k {print $2}'; }
    local st ld po se le gb
    st=$(( $(get smsp__inst_executed_op_local_st.sum) / 8 ))
    ld=$(( $(get smsp__inst_executed_op_local_ld.sum) / 8 ))
    po=$(( $(get smsp__inst_executed_op_local_st_pred_off_all.sum) + $(get smsp__inst_executed_op_local_ld_pred_off_all.sum) ))
    se=$(get l1tex__t_sectors_pipe_lsu_mem_local_op_st.sum)
    le=$(get l1tex__t_sectors_pipe_lsu_mem_local_op_ld.sum)
    gb=$(get l1tex__t_bytes_pipe_lsu_mem_global_op_ld.sum)
    [ -n "$base" ] || base=$gb
    local want_st=$((Bc + 2 * E)) want_ld=$((RB + 2 * RE))
    local want_se=$((8 * (8 * Bc + 32 * E))) want_le=$((8 * (8 * RB + 32 * RE)))
    local want_h=$((256 * 8 * C)) got_h=$((gb - base))
    [ "$st" = "$want_st" ] || bad "$arm store instrs $st want $want_st"
    [ "$ld" = "$want_ld" ] || bad "$arm load instrs $ld want $want_ld"
    [ "$po" = 0 ] || bad "$arm has $po fully-predicated-off local instructions"
    [ "$se" = "$want_se" ] || bad "$arm store sectors $se want $want_se"
    [ "$le" = "$want_le" ] || bad "$arm load sectors $le want $want_le"
    [ "$got_h" = "$want_h" ] || bad "$arm prologue H bytes $got_h want $want_h"
    note "  $arm: st=$st/$want_st ld=$ld/$want_ld pred_off=$po sect=$se/$le H=$got_h/$want_h"
  done <<< "$COUNT_ORACLE"
}

# Chain executions per warp-program walk, against the spec 4 formula C + (326 - Rc).
count() { "$B" --log-trace 9 --warmup 0 --iterations 1 --mode lsb-pair "$@" --window-count \
  | sed -n 's/^chain executions .*= \([0-9]*\) per warp-program walk$/\1/p'; }

production() {
  note "### chain-count gate (exact, vs .agents/sdd/2026-08-09-v3-r4/expected-counts.md)"
  for order in census locality; do
    for spec in "cache0:326" "hot4:279" "hot16:181" "allrepeat:92" "all59:92" "e4rich:234" "e4top2:278"; do
      local arm=${spec%%:*} want=${spec##*:} got
      got=$(count --cache-arm "$arm" --term-order "$order")
      if [ "$got" = "$want" ]; then note "  $arm/$order = $got"
      else bad "chains arm=$arm order=$order got=${got:-<none>} want=$want"; fi
    done
  done
  # The 128 body runs the same program on a 4-warp block: same per-walk figure.
  local got; got=$(count --block-threads 128 --cache-arm allrepeat --term-order locality)
  [ "$got" = 92 ] && note "  allrepeat/locality @128 = $got" || bad "chains @128 got=${got:-<none>} want=92"
}

mutations() {
  note "### mutation (a) retarget a cached reference to a live same-width slot -> q diverges"
  for arm in hot4 allrepeat e4top2; do
    local ref mut
    ref=$(qhash --cache-arm "$arm")
    mut=$(qhash --cache-arm "$arm" --cache-mutate retarget)
    usable "$ref" "retarget ref $arm" || continue
    usable "$mut" "retarget mut $arm" || continue
    if [ "$ref" != "$mut" ]; then note "  $arm diverges ($ref -> $mut)"
    else bad "retarget arm=$arm did not change q"; fi
  done
  note "### mutation (b) poison the frame after the prologue -> only arms with reuses change"
  for spec in "cache0:same" "hot4:diff" "allrepeat:diff" "e4top2:diff"; do
    local arm=${spec%%:*} want=${spec##*:} ref poi got
    ref=$(qhash --cache-arm "$arm")
    poi=$(qhash --cache-arm "$arm" --window-poison)
    usable "$ref" "poison ref $arm" || continue
    usable "$poi" "poison $arm" || continue
    if [ "$ref" = "$poi" ]; then got=same; else got=diff; fi
    if [ "$got" = "$want" ]; then note "  $arm: $got ($ref -> $poi)"
    else bad "poison arm=$arm got=$got want=$want"; fi
  done
  # The controls have no frame to poison, so they must be untouched by the hook.
  local ref poi
  ref=$(qhash); poi=$(qhash --window-poison)
  usable "$ref" "poison ref control" && usable "$poi" "poison control" && {
    [ "$ref" = "$poi" ] && note "  control: same ($ref)" || bad "poison changed the control"; }
}

case "${1:-all}" in
  matrix) matrix ;;
  counts) counts ;;
  diag) production; mutations ;;
  all) matrix; counts; production; mutations ;;
  *) echo "usage: $0 {matrix|counts|diag|all}" >&2; exit 2 ;;
esac
[ "$fail" = 0 ] && note "ALL GATES PASS"
exit "$fail"
