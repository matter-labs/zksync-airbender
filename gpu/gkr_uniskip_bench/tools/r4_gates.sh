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
DIR=$(cd "$(dirname "$0")" && pwd)
# The whole-matrix reporting layer, shared by every gate script here: nothing is rejected on a gate
# prematurely, the run always ends with the full board (RR, 2026-08-13).
# shellcheck source=gate_report.sh
. "$DIR/gate_report.sh"

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
  lane_is matrix
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
  cellrow "q parity (7 arms x size x order x eq x census)" "$cells" "$pass"
  # A dropped loop dimension would otherwise pass silently with fewer cells.
  [ "$cells" = 112 ] || bad "parity cells count; a loop dimension is missing; a check that never ran is not a verdict either way" "112" "${cells}"

  # E4 SELF-PRODUCT CELL. `force_self_products` rewrites both PRODUCT_BF_BF and
  # PRODUCT_E4_E4, but it takes the first `count` in program order and the six E4xE4 records
  # sit after the 54 BF ones — so the matrix's `--self-products 12` reaches BF only. 60 is
  # the program's exact maximum and puts all six E4 self-products live, which is the only
  # way `resolve_second`'s cache-path short-circuit gets exercised on the E4 side.
  # Parity-only: the count oracles stay on the default census, and a cached-vs-control
  # comparison of the SAME program is unaffected by the knob's census staleness.
  note "### E4 self-product cell (--self-products 60, the program maximum)"
  local scells=0 spass=0
  for size in "" "--block-threads 128"; do
    for order in census locality; do
      # shellcheck disable=SC2086
      local sref; sref=$(qhash $size --term-order "$order" --self-products 60)
      usable "$sref" "control sp=60 size=[$size] order=$order" || continue
      for arm in $ARMS; do
        scells=$((scells + 1))
        # shellcheck disable=SC2086
        local sgot; sgot=$(qhash $size --cache-arm "$arm" --term-order "$order" --self-products 60)
        usable "$sgot" "arm=$arm sp=60 size=[$size] order=$order" || continue
        if [ "$sgot" = "$sref" ]; then spass=$((spass + 1));
        else bad "sp60 parity arm=$arm size=[$size] order=$order ($sgot vs $sref)"; fi
      done
    done
  done
  note "  cells=$scells passed=$spass"
  cellrow "self-products 60" "$scells" "$spass"
  [ "$scells" = 28 ] || bad "self-product cells count; a check that never ran is not a verdict either way" "28" "${scells}"

  # The two launch-bounds siblings at 128 must agree with the unbounded bodies they mirror.
  note "### 128 launch-bounds siblings"
  local a b lbcells=0 lbpass=0
  a=$(qhash --block-threads 128 --cache-arm allrepeat)
  b=$(qhash --block-threads 128 --cache-arm allrepeat --no-cache-launch-bounds)
  lbcells=$((lbcells + 1))
  usable "$a" "cached_128_lb" && usable "$b" "cached_128" && {
    if [ "$a" = "$b" ]; then lbpass=$((lbpass + 1)); note "  cached: bounded == unbounded ($a)"
    else bad "cached@128 bounded vs unbounded q" "$a" "$b"; fi; }
  a=$(qhash --block-threads 128)
  b=$(qhash --block-threads 128 --control-launch-bounds)
  lbcells=$((lbcells + 1))
  usable "$a" "control128" && usable "$b" "control128_lb" && {
    if [ "$a" = "$b" ]; then lbpass=$((lbpass + 1)); note "  control: control128 == control128_lb ($a)"
    else bad "control128 vs control128_lb q" "$a" "$b"; fi; }
  cellrow "128 launch-bounds siblings" "$lbcells" "$lbpass"

  # CPU oracle once per arm per size — the only leg that does not go through `q` alone.
  note "### CPU oracle (--validate), one cell per arm per size"
  local oks=0 runs=0 out
  for size in "" "--block-threads 128"; do
    for arm in $ARMS; do
      runs=$((runs + 1))
      # shellcheck disable=SC2086
      out=$("$B" --log-trace 10 --warmup 0 --iterations 1 --mode lsb-pair $size \
                 --cache-arm "$arm" --validate 2>/dev/null)
      if grep -q '^q validate: OK (32/32)' <<< "$out"; then oks=$((oks + 1));
      else bad "CPU oracle arm=$arm size=[$size]" "q validate: OK (32/32)" \
               "$(grep -m1 '^q validate' <<< "$out" || echo absent)"; fi
    done
  done
  note "  oracle cells=$runs passed=$oks"
  cellrow "CPU oracle (7 arms x 2 sizes)" "$runs" "$oks"
  [ "$runs" = 14 ] || bad "oracle cell count — cells that never ran are not a verdict either way" "14" "$runs"
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
# COUNT_ARMS is the roll call: a row that never ran (edited-away oracle line, ncu failure,
# a `continue` taken) must not reach ALL GATES PASS just because nothing compared unequal.
COUNT_ARMS="cache0 hot4 hot16 allrepeat e4rich e4top2 all59"
COUNT_ORACLE="cache0 0 0 0 0 0
hot4 4 4 0 51 0
hot16 28 12 4 93 20
allrepeat 88 44 11 186 34
e4rich 44 0 11 0 34
e4top2 8 0 2 0 14
all59 92 48 11 190 34"

counts() {
  lane_is counts
  note "### local instruction / sector / prologue-H gates (ncu, 1 block x 8 warps)"
  note "  metrics: $NCU_LOCAL_METRICS"
  local base="" gated=" "
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
    gated="$gated$arm "
    note "  $arm: st=$st/$want_st ld=$ld/$want_ld pred_off=$po sect=$se/$le H=$got_h/$want_h"
  done <<< "$COUNT_ORACLE"
  local ran=0
  for arm in $COUNT_ARMS; do
    case "$gated" in
      *" $arm "*) ran=$((ran + 1)) ;;
      *) bad "the count gate never ran for $arm" "a gated row" "no row — a missing row is not a pass" ;;
    esac
  done
  note "  gated arms=$ran/7"
  cellrow "ncu local-traffic gates (7 arms x 6 readings)" "$ran" "$ran"
  [ "$ran" = 7 ] || bad "gated count rows — a row that never ran is not a verdict either way" "7" "$ran"
}

# Chain executions per warp-program walk, against the spec 4 formula C + (326 - Rc).
count() { "$B" --log-trace 9 --warmup 0 --iterations 1 --mode lsb-pair "$@" --window-count \
  | sed -n 's/^chain executions .*= \([0-9]*\) per warp-program walk$/\1/p'; }

production() {
  lane_is production
  local cells=0 pass=0
  note "### chain-count gate (exact, vs .agents/sdd/2026-08-09-v3-r4/expected-counts.md)"
  for order in census locality; do
    for spec in "cache0:326" "hot4:279" "hot16:181" "allrepeat:92" "all59:92" "e4rich:234" "e4top2:278"; do
      local arm=${spec%%:*} want=${spec##*:} got
      got=$(count --cache-arm "$arm" --term-order "$order")
      cells=$((cells + 1))
      if [ -z "$got" ]; then
        notrun "chain count $arm/$order" "the run printed no chain-count line (diagnostic build?)"
      elif [ "$got" = "$want" ]; then pass=$((pass + 1)); note "  $arm/$order = $got"
      else bad "chain count $arm/$order" "$want" "$got"; fi
    done
  done
  # The 128 body runs the same program on a 4-warp block: same per-walk figure.
  local got; got=$(count --block-threads 128 --cache-arm allrepeat --term-order locality)
  cells=$((cells + 1))
  if [ -z "$got" ]; then
    notrun "chain count allrepeat/locality @128" "the run printed no chain-count line"
  elif [ "$got" = 92 ]; then pass=$((pass + 1)); note "  allrepeat/locality @128 = $got"
  else bad "chain count allrepeat/locality @128" "92" "$got"; fi
  note "  cells=$cells passed=$pass"
  cellrow "chain counts (7 arms x 2 orders, plus @128)" "$cells" "$pass"
}

mutations() {
  lane_is mutations
  local rcells=0 rpass=0 pcells=0 ppass=0
  note "### mutation (a) retarget a cached reference to a live same-width slot -> q diverges"
  for arm in hot4 allrepeat e4top2; do
    local ref mut
    ref=$(qhash --cache-arm "$arm")
    mut=$(qhash --cache-arm "$arm" --cache-mutate retarget)
    usable "$ref" "retarget ref $arm" || continue
    usable "$mut" "retarget mut $arm" || continue
    rcells=$((rcells + 1))
    if [ "$ref" != "$mut" ]; then rpass=$((rpass + 1)); note "  $arm diverges ($ref -> $mut)"
    else bad "retarget arm=$arm q" "a digest different from $ref" "$mut"; fi
  done
  note "  cells=$rcells passed=$rpass"
  cellrow "mutation (a) retarget diverges" "$rcells" "$rpass"
  note "### mutation (b) poison the frame after the prologue -> only arms with reuses change"
  for spec in "cache0:same" "hot4:diff" "allrepeat:diff" "e4top2:diff"; do
    local arm=${spec%%:*} want=${spec##*:} ref poi got
    ref=$(qhash --cache-arm "$arm")
    poi=$(qhash --cache-arm "$arm" --window-poison)
    usable "$ref" "poison ref $arm" || continue
    usable "$poi" "poison $arm" || continue
    if [ "$ref" = "$poi" ]; then got=same; else got=diff; fi
    pcells=$((pcells + 1))
    if [ "$got" = "$want" ]; then ppass=$((ppass + 1)); note "  $arm: $got ($ref -> $poi)"
    else bad "poison arm=$arm" "$want" "$got"; fi
  done
  # The controls have no frame to poison, so they must be untouched by the hook.
  local ref poi
  ref=$(qhash); poi=$(qhash --window-poison)
  pcells=$((pcells + 1))
  usable "$ref" "poison ref control" && usable "$poi" "poison control" && {
    if [ "$ref" = "$poi" ]; then ppass=$((ppass + 1)); note "  control: same ($ref)"
    else bad "poison changed the uncached control" "$ref" "$poi"; fi; }
  note "  cells=$pcells passed=$ppass"
  cellrow "mutation (b) poison behaviour" "$pcells" "$ppass"
}

case "${1:-all}" in
  matrix) matrix ;;
  counts) counts ;;
  diag) production; mutations ;;
  all) matrix; counts; production; mutations ;;
  *) echo "usage: $0 {matrix|counts|diag|all}" >&2; exit 2 ;;
esac
gate_summary
exit "$fail"
