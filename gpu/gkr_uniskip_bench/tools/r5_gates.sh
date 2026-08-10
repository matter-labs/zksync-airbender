#!/usr/bin/env bash
# v3 R5 admission-frontier gates, executable rather than transcribed.
#
#   sass        the nine frozen bodies, byte-identical to the R3/R4 freeze artifacts —
#               SHIPPED build only, and it says so instead of comparing the wrong binary
#   matrix      q parity: the nine kN arms at 128 against the 128 control, over orders x
#               eq forms x censuses, plus the CPU oracle — runs on EITHER build
#   admitted    live frontier rotations; every lane's ORDERED admitted_ids against the
#               canonical admission ordering — runs on EITHER build
#   counts      the oracle's per-lane counts: ncu local ld/st instructions (+ sectors and
#               prologue H), which need the SHIPPED build, then the chain counter, which
#               needs the diagnostic one — this lane builds it
#   regression  r3_gates.sh all + r4_gates.sh all — needs the diagnostic binary
#   all         every lane, sequenced so `sass` sees the shipped build
#
# Usage, from the repo root:
#   cargo build --release -p gpu_gkr_uniskip_bench
#   .agents/bin/with_gpu_lock.sh gpu/gkr_uniskip_bench/tools/r5_gates.sh all
#
# `counts` and `regression` need GPU_GKR_UNISKIP_BENCH_WINDOW_DIAG=1. This script builds
# that binary ITSELF and rebuilds the shipped one on exit — whatever it was handed and
# however it exits. A diagnostic binary left behind times like a diagnostic binary, and
# the next thing anyone runs here is a measurement.
#
# Exit status is the gate verdict: non-zero if any cell fails.
set -uo pipefail

B=${B:-target/release/gpu_gkr_uniskip_bench}
export B
DIR=$(cd "$(dirname "$0")" && pwd)
SDD=${SDD:-$(cd "$DIR/../../.." && pwd)/.agents/sdd}
KN="k24 k32 k40 k45 k46 k48 k49 k50 k51"
fail=0
diag_built=0
note() { printf '%s\n' "$*"; }
bad() { printf 'FAIL: %s\n' "$*"; fail=1; }

TMP=$(mktemp -d)

# `9>&-` is load-bearing, not hygiene. This script runs under `.agents/bin/with_gpu_lock.sh`,
# which holds the GPU lock on fd 9; a `cargo build` here spawns the sccache SERVER, which is
# a long-lived daemon and inherits every open fd — including that one. The lock then stays
# held after the script exits and the next `with_gpu_lock.sh` waits forever. Closing fd 9
# for the build (and for the compilers it spawns) is what keeps the lock the script's own.
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

# Empty input hashes to a fixed digest, so a missing binary or a failed run would make BOTH
# sides of a parity comparison equal. qhash runs inside a command substitution and must
# never call bad() — the assignment to `fail` would be lost with the subshell. Diagnostics
# go to stderr, INVALID comes back on stdout, and usable() in the parent sets `fail`.
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

# Oracle rows: lane K B E C Rc R_B R_E chains stores loads, copied from
# `.agents/sdd/2026-08-10-v3-r5/expected-counts-r5.md` (both tables; the frontier is
# identical under census and locality, so the rows carry no order). The R5 identities are
# re-checked below, so a transcription slip here fails the gate instead of moving it.
R5_ORACLE="k24 24 20 4 36 197 117 20 165 28 157
k32 32 28 4 44 221 141 20 149 36 181
k40 40 36 4 52 245 165 20 133 44 205
k45 45 41 4 57 260 180 20 123 49 220
k46 46 41 5 61 268 180 22 119 51 224
k48 48 41 7 69 284 180 26 111 55 232
k49 49 41 8 73 292 180 28 107 57 236
k50 50 41 9 77 300 180 30 103 59 240
k51 51 41 10 81 308 180 32 99 61 244"

# hot16 = the K16 prefix point exactly. `expected-counts-r5.md` states it as an ANCHOR line
# rather than a frontier-table row, so it is carried separately: the kN lanes' asserted cell
# counts stay exactly nine, and hot16 still gets its C/removals gated in the admitted lane.
R5_ANCHOR="hot16 16 12 4 28 173 93 20 181 20 133"

oracle_rows() { printf '%s\n%s\n' "$R5_ORACLE" "$R5_ANCHOR"; }

# The canonical admission ordering, all 55 reused sources, transcribed ONCE from the
# `admission head (id,refs,w)` line of `.agents/sdd/2026-08-10-v3-r5/oracle-derivation.txt`
# (identical under both term orders). Every lane's admitted-id list is its first-K prefix,
# IN THIS ORDER: counts alone cannot see a reversal among equal-ref, equal-class sources.
ADMISSION_ORDER=0,1,2,3,4,5,48,49,50,51,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,52,53,54,55,56,57,58,41,42,43

# The transcription guard, run once by whichever lane reads the oracle first: every literal
# above is re-derived from the R4 formulas, so a slipped digit fails the gate rather than
# quietly moving it.
oracle_checked=0
oracle_identities() {
  [ "$oracle_checked" = 1 ] && return 0
  oracle_checked=1
  local n lane K Bc E C Rc RB RE chains stores loads
  n=$(printf '%s' "$ADMISSION_ORDER" | tr ',' '\n' | grep -c .)
  [ "$n" = 55 ] || bad "the transcribed admission ordering has $n entries, the oracle has 55"
  while read -r lane K Bc E C Rc RB RE chains stores loads; do
    [ -n "$lane" ] || continue
    [ "$C" = "$((Bc + 4 * E))" ] || bad "oracle row $lane: C=$C is not B+4E"
    [ "$Rc" = "$((RB + 4 * RE))" ] || bad "oracle row $lane: Rc=$Rc is not R_B+4R_E"
    [ "$chains" = "$((C + 326 - Rc))" ] || bad "oracle row $lane: chains=$chains is not C+(326-Rc)"
    [ "$stores" = "$((Bc + 2 * E))" ] || bad "oracle row $lane: stores=$stores is not B+2E"
    [ "$loads" = "$((RB + 2 * RE))" ] || bad "oracle row $lane: loads=$loads is not R_B+2R_E"
    case "$lane" in k*) [ "$lane" = "k$K" ] || bad "oracle row $lane names K=$K" ;; esac
  done <<< "$(oracle_rows)"
}

newest_archive() {
  # shellcheck disable=SC2012  # cargo's build dirs are hash-suffixed; -t is the point here
  ls -1t target/release/build/gpu_gkr_uniskip_bench-*/out/libgpu_gkr_uniskip_bench_native.a 2>/dev/null | head -1
}

# ON | OFF | unknown for the archive the current binary links. build.rs ALWAYS passes the
# define ("ON" or "OFF"), so the CMake cache is truthful about the flavor.
build_flavor() {
  local ar=$1 v
  [ -n "$ar" ] || { echo unknown; return; }
  v=$(awk -F= '/^AB_UNISKIP_WINDOW_DIAG:/ {print $2}' \
        "${ar%/libgpu_gkr_uniskip_bench_native.a}/build/CMakeCache.txt" 2>/dev/null | head -1)
  echo "${v:-unknown}"
}

# Both the frozen bodies and the ncu counters are SHIPPED-build facts, and neither failure
# mode is loud: the frozen artifacts would simply differ, and the diag counter is a global
# atomic that leaves the local ld/st mix intact, so a diagnostic binary can PASS the count
# gate while being the wrong binary. TRAP: R4's proof took `sorted(glob)[0]`, the first build
# dir BY NAME, which silently re-proved a stale archive; newest mtime is the linked one.
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

# ---------------------------------------------------------------- matrix

matrix() {
  note "### q parity: 9 kN arms @128 x 2 orders x 2 eq forms x 2 censuses"
  local cells=0 pass=0
  for order in census locality; do
    for eq in "" "--validate-flat-eq"; do
      for sp in 0 12; do
        # The 128 control, i.e. the frozen unbounded control128 — R4's matrix already gates
        # it against control128_lb, so one reference per cell is enough.
        # shellcheck disable=SC2086
        local ref; ref=$(qhash --block-threads 128 --term-order "$order" --self-products "$sp" $eq)
        usable "$ref" "control@128 order=$order eq=[$eq] sp=$sp" || continue
        for arm in $KN; do
          cells=$((cells + 1))
          # shellcheck disable=SC2086
          local got; got=$(qhash --block-threads 128 --cache-arm "$arm" --term-order "$order" --self-products "$sp" $eq)
          usable "$got" "arm=$arm order=$order eq=[$eq] sp=$sp" || continue
          if [ "$got" = "$ref" ]; then pass=$((pass + 1));
          else bad "parity arm=$arm order=$order eq=[$eq] sp=$sp ($got vs $ref)"; fi
        done
      done
    done
  done
  note "  cells=$cells passed=$pass"
  # A dropped loop dimension would otherwise pass silently with fewer cells.
  [ "$cells" = 72 ] || bad "expected 72 parity cells, ran $cells — a loop dimension is missing"
  [ "$cells" = "$pass" ] || bad "parity matrix incomplete"

  # E4 SELF-PRODUCT CELL, R4's lesson carried to the new arms: `--self-products 12` takes
  # the first 12 binary products in program order and the six E4xE4 records sit after the 54
  # BF ones, so the matrix above never reaches the E4 cache path. 60 is the program's exact
  # maximum. The kN arms admit up to ten E4 sources against hot16's four, which is the part
  # R4's 28-cell lane cannot cover. Parity-only: the count oracles stay on the default census.
  note "### E4 self-product cell (--self-products 60, the program maximum)"
  local scells=0 spass=0
  for order in census locality; do
    local sref; sref=$(qhash --block-threads 128 --term-order "$order" --self-products 60)
    usable "$sref" "control@128 sp=60 order=$order" || continue
    for arm in $KN; do
      scells=$((scells + 1))
      local sgot; sgot=$(qhash --block-threads 128 --cache-arm "$arm" --term-order "$order" --self-products 60)
      usable "$sgot" "arm=$arm sp=60 order=$order" || continue
      if [ "$sgot" = "$sref" ]; then spass=$((spass + 1));
      else bad "sp60 parity arm=$arm order=$order ($sgot vs $sref)"; fi
    done
  done
  note "  cells=$scells passed=$spass"
  [ "$scells" = 18 ] || bad "expected 18 self-product cells, ran $scells"
  [ "$scells" = "$spass" ] || bad "self-product matrix incomplete"

  # CPU oracle once per arm — the only leg that does not go through `q` alone.
  note "### CPU oracle (--validate), one cell per kN arm"
  local oks=0 runs=0
  for arm in $KN; do
    runs=$((runs + 1))
    if "$B" --log-trace 10 --warmup 0 --iterations 1 --mode lsb-pair --block-threads 128 \
         --cache-arm "$arm" --validate 2>/dev/null | grep -q '^q validate: OK (32/32)'; then
      oks=$((oks + 1))
    else bad "CPU oracle arm=$arm"; fi
  done
  note "  oracle cells=$runs passed=$oks"
  [ "$runs" = 9 ] || bad "expected 9 oracle cells, ran $runs"
  [ "$runs" = "$oks" ] || bad "CPU oracle incomplete"
}

# ---------------------------------------------------------------- counts

# spec 4's local-traffic table, measured directly. `--log-trace 9` is one 256-thread block =
# 8 warps, so a per-walk figure is the counter over 8. The metric NAMES matter: on sm_120 the
# LDL/STL warp-instruction counters are `smsp__inst_executed_op_local_{ld,st}`, NOT the
# `..._op_ldl/stl` spelling (which does not exist on this chip and reports n/a).
#
# Instructions and sectors are gated SEPARATELY on purpose. The sector totals prove bytes
# and the absence of over-fetch, but they do NOT determine the instruction mix: one sector
# total fits several (BF, E4-half) splits. Only the direct counter settles it.
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

ncu_counts() {
  note "### local instruction / sector / prologue-H gates (ncu, 1 block x 8 warps)"
  require_shipped "the ncu counter lane" || return
  note "  metrics: $NCU_LOCAL_METRICS"
  # cache0 is the H baseline: its prologue loads nothing, so the global-load byte delta
  # against it is the prologue's own traffic.
  local base out
  out=$(metric cache0)
  if [ -z "$out" ]; then bad "no ncu output for the cache0 H baseline"; return; fi
  base=$(printf '%s\n' "$out" | awk '$1=="l1tex__t_bytes_pipe_lsu_mem_global_op_ld.sum" {print $2}')
  [ -n "$base" ] || { bad "cache0 capture carries no global-load bytes"; return; }
  note "  cache0 H baseline = $base B"

  # A row that never ran (an ncu failure, a `continue` taken) must not reach ALL GATES PASS
  # just because nothing compared unequal.
  local gated=" " lane K Bc E C Rc RB RE chains stores loads
  while read -r lane K Bc E C Rc RB RE chains stores loads; do
    [ -n "$lane" ] || continue
    out=$(metric "$lane")
    if [ -z "$out" ]; then bad "no ncu output for $lane"; continue; fi
    get() { printf '%s\n' "$out" | awk -v k="$1" '$1==k {print $2}'; }
    local st ld po se le gb
    st=$(( $(get smsp__inst_executed_op_local_st.sum) / 8 ))
    ld=$(( $(get smsp__inst_executed_op_local_ld.sum) / 8 ))
    po=$(( $(get smsp__inst_executed_op_local_st_pred_off_all.sum) + $(get smsp__inst_executed_op_local_ld_pred_off_all.sum) ))
    se=$(get l1tex__t_sectors_pipe_lsu_mem_local_op_st.sum)
    le=$(get l1tex__t_sectors_pipe_lsu_mem_local_op_ld.sum)
    gb=$(get l1tex__t_bytes_pipe_lsu_mem_global_op_ld.sum)
    local want_se=$((8 * (8 * Bc + 32 * E))) want_le=$((8 * (8 * RB + 32 * RE)))
    local want_h=$((256 * 8 * C)) got_h=$((gb - base))
    [ "$st" = "$stores" ] || bad "$lane store instrs $st want $stores"
    [ "$ld" = "$loads" ] || bad "$lane load instrs $ld want $loads"
    [ "$po" = 0 ] || bad "$lane has $po fully-predicated-off local instructions"
    [ "$se" = "$want_se" ] || bad "$lane store sectors $se want $want_se"
    [ "$le" = "$want_le" ] || bad "$lane load sectors $le want $want_le"
    [ "$got_h" = "$want_h" ] || bad "$lane prologue H bytes $got_h want $want_h"
    gated="$gated$lane "
    note "  $lane: st=$st/$stores ld=$ld/$loads pred_off=$po sect=$se/$le H=$got_h/$want_h"
  done <<< "$R5_ORACLE"
  local ran=0
  for lane in $KN; do
    case "$gated" in
      *" $lane "*) ran=$((ran + 1)) ;;
      *) bad "count gate never ran for $lane — a missing row is a failure, not a pass" ;;
    esac
  done
  note "  gated lanes=$ran/9"
  [ "$ran" = 9 ] || bad "expected 9 gated count rows, completed $ran"
}

# Chain executions per warp-program walk, against the spec 4 formula C + (326 - Rc).
count() { "$B" --log-trace 9 --warmup 0 --iterations 1 --mode lsb-pair "$@" --window-count \
  | sed -n 's/^chain executions .*= \([0-9]*\) per warp-program walk$/\1/p'; }

chain_counts() {
  note "### chain-count gate (exact, vs .agents/sdd/2026-08-10-v3-r5/expected-counts-r5.md)"
  local cells=0 pass=0 lane K Bc E C Rc RB RE chains stores loads
  for order in census locality; do
    while read -r lane K Bc E C Rc RB RE chains stores loads; do
      [ -n "$lane" ] || continue
      # Both block sizes: `--window-count` divides by the block's warp count, and R4 found
      # that divisor hard-coded to 256. The frontier lanes all run at 128.
      local got256 got128
      got256=$(count --cache-arm "$lane" --term-order "$order")
      got128=$(count --block-threads 128 --cache-arm "$lane" --term-order "$order")
      cells=$((cells + 2))
      for got in "$got256" "$got128"; do
        if [ "$got" = "$chains" ]; then pass=$((pass + 1))
        else bad "chains lane=$lane order=$order got=${got:-<none>} want=$chains"; fi
      done
      note "  $lane/$order = ${got256:-<none>} @256, ${got128:-<none>} @128 (want $chains = C+(326-Rc))"
    done <<< "$R5_ORACLE"
  done
  note "  cells=$cells passed=$pass"
  [ "$cells" = 36 ] || bad "expected 36 chain cells, ran $cells"
  [ "$cells" = "$pass" ] || bad "chain-count gate incomplete"
}

counts() {
  oracle_identities
  ncu_counts
  ensure_diag && chain_counts
}

# ---------------------------------------------------------------- admitted

admitted() {
  oracle_identities
  note "### admitted_ids: live rotations, ORDERED, vs the canonical admission prefixes"
  local checked=" " arms=0
  for spec in "--frontier-factorial:10:FRONTIER-FACTORIAL" "--frontier-extension:8:FRONTIER-EXTENSION"; do
    local flag=${spec%%:*} rest=${spec#*:}
    local lanes=${rest%%:*} tag=${rest#*:}
    for order in census locality; do
      # Smallest geometry that still tiles both block sizes, one rotation, no warmup: this
      # lane reads the ARM header, never a time.
      local log="$TMP/frontier-$lanes-$order.log"
      if ! "$B" --log-trace 9 --mode lsb-pair "$flag" --iterations "$lanes" --warmup 0 \
             --term-order "$order" >"$log" 2>&1; then
        bad "$flag order=$order run failed"; tail -3 "$log"; continue
      fi
      if ! grep -q "^$tag done order=$order warmup=0 rounds=$lanes lanes=$lanes\$" "$log"; then
        bad "$flag order=$order emitted no trailer — a truncated log is not a pass"; continue
      fi
      local n; n=$(grep -c '^ARM ' "$log")
      [ "$n" = "$lanes" ] || bad "$flag order=$order has $n ARM lines, the rotation names $lanes"
      local label c removals nadm ids want K
      while read -r _ label _ _ _ _ _ c removals nadm ids; do
        arms=$((arms + 1))
        case "$label" in
          k*@128) K=${label#k}; K=${K%@128} ;;
          hot16@128) K=16 ;;
          cache0@128 | control_lb@128 | control@256)
            [ "$ids" = "-" ] && [ "$nadm" = 0 ] || bad "$label admits '$ids' ($nadm); it has no admitted set"
            continue ;;
          *) bad "$flag order=$order: unknown lane label $label"; continue ;;
        esac
        want=$(printf '%s' "$ADMISSION_ORDER" | cut -d, -f"1-$K")
        # The ARM line's C and removals are what Task 3's slope pricing divides by, so they
        # are GATED against the oracle here rather than echoed: C from the table, removals
        # as Rc - C.
        local row want_c want_rem
        row=$(oracle_rows | awk -v k="${label%@128}" '$1==k {print $5, $6 - $5}')
        if [ -z "$row" ]; then bad "$label has no oracle row"; continue; fi
        want_c=${row%% *}; want_rem=${row##* }
        if [ "$ids" != "$want" ]; then
          bad "$label order=$order admitted_ids is not the canonical prefix at K=$K"
          note "    got  $ids"
          note "    want $want"
        elif [ "$nadm" != "$K" ]; then
          bad "$label order=$order declares $nadm admitted ids at K=$K"
        elif [ "$c" != "$want_c" ]; then
          bad "$label order=$order ARM C=$c, the oracle says $want_c"
        elif [ "$removals" != "$want_rem" ]; then
          bad "$label order=$order ARM removals=$removals, the oracle says $want_rem = Rc-C"
        else
          checked="$checked$order/$label "
          note "  $label/$order: K=$K C=$c/$want_c removals=$removals/$want_rem, prefix exact"
        fi
      done < <(grep '^ARM ' "$log")
    done
  done
  # Roll call: every kN lane, under both orders, over the union of the two rotations.
  local ran=0
  for order in census locality; do
    for arm in $KN hot16; do
      case "$checked" in
        *" $order/$arm@128 "*) ran=$((ran + 1)) ;;
        *) bad "no admitted_ids check ran for $arm under $order" ;;
      esac
    done
  done
  note "  ARM lines parsed=$arms, lane/order checks=$ran/20"
  [ "$arms" = 36 ] || bad "expected 36 ARM lines over the four runs, parsed $arms"
  [ "$ran" = 20 ] || bad "expected 20 lane/order admission checks, ran $ran"
}

# ---------------------------------------------------------------- sass

# fn|artifact|kind|declared instruction count. DUMP = a raw `cuobjdump -sass` artifact,
# SECT = a `## <fn>: N normalized instructions` section, PLAIN = a single-body artifact.
SASS_EXPECT="ab_gkr_uniskip_eval_lsb_pair_kernel|2026-08-09-v3-r3/task1-final-sass.txt|DUMP|5104
ab_gkr_uniskip_eval_lsb_pair_lb_kernel|2026-08-09-v3-r3/task1-final-sass.txt|DUMP|5104
ab_gkr_uniskip_eval_lsb_pair_win_kernel|2026-08-09-v3-r3/task1-final-sass.txt|DUMP|5592
ab_gkr_uniskip_eval_lsb_pair_win_lb_kernel|2026-08-09-v3-r3/task1-final-sass.txt|DUMP|5600
ab_gkr_uniskip_eval_lsb_pair_128_kernel|2026-08-09-v3-r4/task1a-control128-sass.txt|PLAIN|5048
ab_gkr_uniskip_eval_lsb_pair_128_lb_kernel|2026-08-09-v3-r4/task1b-control128lb-sass.txt|PLAIN|5064
ab_gkr_uniskip_eval_lsb_pair_cached_kernel|2026-08-09-v3-r4/task1b-cached-256-sass.txt|SECT|6024
ab_gkr_uniskip_eval_lsb_pair_cached_128_kernel|2026-08-09-v3-r4/task1b-cached-128-sass.txt|SECT|5976
ab_gkr_uniskip_eval_lsb_pair_cached_128_lb_kernel|2026-08-09-v3-r4/task1b-cached-128-sass.txt|SECT|5992"

# One normalizer for the live dump and for the DUMP artifacts, so the two sides cannot
# normalize differently. TRAP: the address comment is 4 OR 5 hex digits — a `{4}` regex
# truncates every body at instruction 4096 and mismatched functions then compare equal.
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

artifact_body() { # artifact_body <kind> <file> <fn> <out>
  case "$1" in
    PLAIN) awk '$0 != "" && substr($0, 1, 1) != "#"' "$2" >"$4" ;;
    SECT) awk -v fn="$3" '
            /^## / { s = $2; sub(/:$/, "", s); grab = (s == fn); next }
            grab && $0 ~ /[^ \t]/ { print }
          ' "$2" >"$4" ;;
    DUMP)
      local dir
      dir="$TMP/artifact-$(basename "$2")"
      [ -d "$dir" ] || norm_dump "$2" "$dir"
      cp "$dir/$3" "$4" 2>/dev/null || : >"$4"
      ;;
  esac
}

sass() {
  note "### frozen SASS: the nine bodies, byte-identical to the R3/R4 freeze artifacts"
  require_shipped "the frozen-SASS lane" || return
  local ar=$ARCHIVE work="$TMP/sass" ar_abs
  ar_abs=$(readlink -f "$ar")
  mkdir -p "$work"
  # The freeze artifacts scope themselves to the pair TU's OWN fatbin; the device-linked
  # copy differs in relocated MOV/UMOV immediates and would report a false DIFFERS.
  ( cd "$work" && ar x "$ar_abs" uniskip_lsb_pair.cu.o ) 2>/dev/null
  if [ ! -f "$work/uniskip_lsb_pair.cu.o" ]; then bad "could not extract uniskip_lsb_pair.cu.o from $ar"; return; fi
  if ! cuobjdump -sass "$work/uniskip_lsb_pair.cu.o" >"$work/dump.txt" 2>"$work/dump.err"; then
    bad "cuobjdump failed on the pair TU"; tail -3 "$work/dump.err"; return
  fi
  norm_dump "$work/dump.txt" "$work/live"
  local ok=0 rows=0 fn art kind want
  while IFS='|' read -r fn art kind want; do
    [ -n "$fn" ] || continue
    rows=$((rows + 1))
    if [ ! -f "$work/live/$fn" ]; then bad "$fn is missing from the built archive"; continue; fi
    artifact_body "$kind" "$SDD/$art" "$fn" "$work/want-$fn"
    local have_n want_n
    have_n=$(wc -l <"$work/live/$fn")
    want_n=$(wc -l <"$work/want-$fn")
    if [ "$want_n" != "$want" ]; then
      bad "$fn: artifact $art carries $want_n instructions, the record declares $want"
      continue
    fi
    if cmp -s "$work/live/$fn" "$work/want-$fn"; then
      ok=$((ok + 1))
      note "  IDENTICAL $fn ($have_n instrs)"
    else
      bad "$fn DIFFERS from $art ($have_n vs $want_n instrs)"
      diff "$work/want-$fn" "$work/live/$fn" | head -6
    fi
  done <<< "$SASS_EXPECT"
  note "  frozen bodies $ok/$rows identical"
  [ "$rows" = 9 ] || bad "expected 9 frozen bodies, checked $rows"
  [ "$ok" = 9 ] || bad "frozen SASS is not 9/9"
}

# ---------------------------------------------------------------- builds + regression

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

regression() {
  ensure_diag || return
  local g out rc
  for g in r3_gates.sh r4_gates.sh; do
    note "### regression: $g all"
    out=$("$DIR/$g" all 2>&1); rc=$?
    printf '%s\n' "$out" | grep -E '^(  cells=|  oracle cells=|  gated arms=|ALL GATES PASS|FAIL: )' \
      | awk '{print "    " $0}'
    [ "$rc" = 0 ] || bad "$g all exited $rc"
    printf '%s\n' "$out" | grep -q '^ALL GATES PASS' || bad "$g all did not print ALL GATES PASS"
  done
}

case "${1:-all}" in
  matrix) matrix ;;
  counts) counts ;;
  admitted) admitted ;;
  sass) sass ;;
  regression) regression ;;
  # `sass` first: it is the only lane that must see the shipped build, and `counts` swaps
  # the binary underneath everything after it.
  all) sass; matrix; admitted; counts; regression ;;
  *) echo "usage: $0 {matrix|counts|admitted|sass|regression|all}" >&2; exit 2 ;;
esac
[ "$fail" = 0 ] && note "ALL GATES PASS"
exit "$fail"
