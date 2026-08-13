#!/usr/bin/env bash
# v3 R5 admission-frontier gates, executable rather than transcribed. The v3 R8 interior arms
# (K17–23) are the same frontier measured at seven more prefix points, so they join these lanes
# rather than getting a file of their own: same body, same oracle formulas, same rotation
# grammar.
#
#   sass        the nine frozen bodies, byte-identical to the R3/R4 freeze artifacts —
#               SHIPPED build only, and it says so instead of comparing the wrong binary
#   matrix      q parity: the sixteen kN arms at 128 against the 128 control, over orders x
#               eq forms x censuses, plus the CPU oracle — runs on EITHER build
#   admitted    live frontier rotations; every lane's ORDERED admitted_ids against the
#               canonical admission ordering — runs on EITHER build
#   counts      the oracle's per-lane counts: ncu local ld/st instructions (+ sectors and
#               prologue H), which need the SHIPPED build, then the chain counter, which
#               needs the diagnostic one — this lane builds it
#   fixtures    the emitter's fixture matrix: every R8 decision row and fail-closed guard,
#               plus the R5 replay — needs no binary and no GPU
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
# The v3 R8 interior arms, kept as their OWN list: the R5 rows, cells and counts above stay
# exactly what they were, and every cell family below gains the seven new arms by appending
# this list rather than by editing that one.
KN8="k17 k18 k19 k20 k21 k22 k23"
ARMS="$KN $KN8"
FIXTURES=$DIR/r8_fixtures/check.sh
diag_built=0
# The whole-matrix reporting layer, shared by every gate script here: nothing is rejected on a gate
# prematurely, the run always ends with the full board (RR, 2026-08-13).
# shellcheck source=gate_report.sh
. "$DIR/gate_report.sh"

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

# The v3 R8 interior rows, same format, copied from
# `.agents/sdd/2026-08-12-v3-r8/expected-counts-r8.md` (whose K17–23 rows are themselves
# verbatim from the R5 derivation output — that derivation enumerated every prefix point). All
# seven sit inside the refs-3 BF band, so each step is B+1, C+1, Rc+3, R_B+3, chains−2,
# stores+1, loads+3, removals+2. The identities below are re-checked row by row, so a
# transcription slip here fails the gate instead of moving it.
R8_ORACLE="k17 17 13 4 29 176 96 20 179 21 136
k18 18 14 4 30 179 99 20 177 22 139
k19 19 15 4 31 182 102 20 175 23 142
k20 20 16 4 32 185 105 20 173 24 145
k21 21 17 4 33 188 108 20 171 25 148
k22 22 18 4 34 191 111 20 169 26 151
k23 23 19 4 35 194 114 20 167 27 154"

oracle_rows() { printf '%s\n%s\n%s\n' "$R5_ORACLE" "$R5_ANCHOR" "$R8_ORACLE"; }

# The count and chain lanes read this: the R5 rows FIRST and in their original order, then the
# R8 rows appended, so no existing cell moves and the seven new lanes join every family.
count_rows() { printf '%s\n%s\n' "$R5_ORACLE" "$R8_ORACLE"; }

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

  # THE R8 AXIS CLOSURE. hot16 -> k17 -> … -> k23 -> k24 is one refs-3 BF admission per step,
  # so every step must move (K, B, E, C, Rc, R_B, R_E, chains, stores, loads) by
  # (+1, +1, 0, +1, +3, +3, 0, -2, +1, +3) and the eight steps must close on the k24 row that
  # was already there. A slipped digit that happens to satisfy the per-row identities above —
  # they are five equations in nine unknowns — is caught here.
  local first=1 pl pK pB pE pC pRc pRB pRE pch pst pld
  while read -r lane K Bc E C Rc RB RE chains stores loads; do
    [ -n "$lane" ] || continue
    if [ "$first" = 0 ] && ! { [ "$K" = "$((pK + 1))" ] && [ "$Bc" = "$((pB + 1))" ] &&
         [ "$E" = "$pE" ] && [ "$C" = "$((pC + 1))" ] && [ "$Rc" = "$((pRc + 3))" ] &&
         [ "$RB" = "$((pRB + 3))" ] && [ "$RE" = "$pRE" ] && [ "$chains" = "$((pch - 2))" ] &&
         [ "$stores" = "$((pst + 1))" ] && [ "$loads" = "$((pld + 3))" ]; }; then
      bad "R8 axis step $pl -> $lane is not one refs-3 BF admission (+1 B, +1 C, +3 Rc, -2 chains)"
    fi
    first=0
    pl=$lane; pK=$K; pB=$Bc; pE=$E; pC=$C; pRc=$Rc; pRB=$RB; pRE=$RE
    pch=$chains; pst=$stores; pld=$loads
  done <<< "$(printf '%s\n%s\n%s\n' "$R5_ANCHOR" "$R8_ORACLE" \
                "$(printf '%s\n' "$R5_ORACLE" | head -1)")"
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

# ---------------------------------------------------------------- matrix

matrix() {
  lane_is matrix
  note "### q parity: 16 kN arms @128 x 2 orders x 2 eq forms x 2 censuses"
  local cells=0 pass=0
  for order in census locality; do
    for eq in "" "--validate-flat-eq"; do
      for sp in 0 12; do
        # The 128 control, i.e. the frozen unbounded control128 — R4's matrix already gates
        # it against control128_lb, so one reference per cell is enough.
        # shellcheck disable=SC2086
        local ref; ref=$(qhash --block-threads 128 --term-order "$order" --self-products "$sp" $eq)
        usable "$ref" "control@128 order=$order eq=[$eq] sp=$sp" || continue
        for arm in $ARMS; do
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
  cellrow "q parity (frontier lanes x order x eq x census)" "$cells" "$pass"
  # A dropped loop dimension would otherwise pass silently with fewer cells.
  [ "$cells" = 128 ] || bad "parity cells count; a loop dimension is missing; a check that never ran is not a verdict either way" "128" "${cells}"

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
    for arm in $ARMS; do
      scells=$((scells + 1))
      local sgot; sgot=$(qhash --block-threads 128 --cache-arm "$arm" --term-order "$order" --self-products 60)
      usable "$sgot" "arm=$arm sp=60 order=$order" || continue
      if [ "$sgot" = "$sref" ]; then spass=$((spass + 1));
      else bad "sp60 parity arm=$arm order=$order ($sgot vs $sref)"; fi
    done
  done
  note "  cells=$scells passed=$spass"
  cellrow "self-products 60" "$scells" "$spass"
  [ "$scells" = 32 ] || bad "self-product cells count; a check that never ran is not a verdict either way" "32" "${scells}"

  # CPU oracle once per arm — the only leg that does not go through `q` alone.
  note "### CPU oracle (--validate), one cell per kN arm"
  local oks=0 runs=0 out
  for arm in $ARMS; do
    runs=$((runs + 1))
    # Captured first, then matched: `"$B" … | grep -q` under `pipefail` races the binary's teardown
    # and reports a SUCCESSFUL match as a failure (r7's diagnosis, reproduced 200/200).
    out=$("$B" --log-trace 10 --warmup 0 --iterations 1 --mode lsb-pair --block-threads 128 \
               --cache-arm "$arm" --validate 2>/dev/null)
    if grep -q '^q validate: OK (32/32)' <<< "$out"; then
      oks=$((oks + 1))
    else bad "CPU oracle arm=$arm" "q validate: OK (32/32)" \
             "$(grep -m1 '^q validate' <<< "$out" || echo absent)"; fi
  done
  note "  oracle cells=$runs passed=$oks"
  cellrow "CPU oracle (one cell per kN arm)" "$runs" "$oks"
  [ "$runs" = 16 ] || bad "oracle cell count — cells that never ran are not a verdict either way" "16" "$runs"
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
  lane_is counts
  note "### local instruction / sector / prologue-H gates (ncu, 1 block x 8 warps)"
  if ! require_shipped "the ncu counter lane"; then
    notrun "the ncu counter lane" "BUILD-ORDER: the archive under it is not the SHIPPED build, so its counters would be another build's"
    return
  fi
  note "  metrics: $NCU_LOCAL_METRICS"
  # cache0 is the H baseline: its prologue loads nothing, so the global-load byte delta
  # against it is the prologue's own traffic.
  local base out
  out=$(metric cache0)
  if [ -z "$out" ]; then
    notrun "the ncu counter lane" "no ncu output for the cache0 H baseline, so every row's H delta is unmeasurable"
    return
  fi
  base=$(printf '%s\n' "$out" | awk '$1=="l1tex__t_bytes_pipe_lsu_mem_global_op_ld.sum" {print $2}')
  [ -n "$base" ] || { notrun "the ncu counter lane" "the cache0 capture carries no global-load bytes, so no H delta can be taken"; return; }
  note "  cache0 H baseline = $base B"

  # A row that never ran (an ncu failure, a `continue` taken) must not reach ALL GATES PASS
  # just because nothing compared unequal.
  local gated=" " lane K Bc E C Rc RB RE chains stores loads
  while read -r lane K Bc E C Rc RB RE chains stores loads; do
    [ -n "$lane" ] || continue
    out=$(metric "$lane")
    if [ -z "$out" ]; then notrun "ncu row $lane" "the capture produced no output"; continue; fi
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
  done <<< "$(count_rows)"
  local ran=0
  for lane in $ARMS; do
    case "$gated" in
      *" $lane "*) ran=$((ran + 1)) ;;
      *) bad "the count gate never ran for $lane" "a gated row" "no row — a missing row is not a pass" ;;
    esac
  done
  note "  gated lanes=$ran/16"
  cellrow "ncu local-traffic gates (16 lanes x 6 readings)" "$ran" "$ran"
  [ "$ran" = 16 ] || bad "gated count rows count; a check that never ran is not a verdict either way" "16" "${ran}"
}

# Chain executions per warp-program walk, against the spec 4 formula C + (326 - Rc).
count() { "$B" --log-trace 9 --warmup 0 --iterations 1 --mode lsb-pair "$@" --window-count \
  | sed -n 's/^chain executions .*= \([0-9]*\) per warp-program walk$/\1/p'; }

chain_counts() {
  lane_is counts
  note "### chain-count gate (exact, vs expected-counts-r5.md + expected-counts-r8.md)"
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
        if [ -z "$got" ]; then
          notrun "chain count $lane/$order" "the run printed no chain-count line (diagnostic build?)"
        elif [ "$got" = "$chains" ]; then pass=$((pass + 1))
        else bad "chain count $lane/$order (C+(326-Rc))" "$chains" "$got"; fi
      done
      note "  $lane/$order = ${got256:-<none>} @256, ${got128:-<none>} @128 (want $chains = C+(326-Rc))"
    done <<< "$(count_rows)"
  done
  note "  cells=$cells passed=$pass"
  cellrow "chain counts per walk, @256 and @128" "$cells" "$pass"
  [ "$cells" = 64 ] || bad "chain cells count; a check that never ran is not a verdict either way" "64" "${cells}"
}

counts() {
  oracle_identities
  ncu_counts
  ensure_diag && chain_counts
}

# ---------------------------------------------------------------- admitted

admitted() {
  lane_is admitted
  oracle_identities
  note "### admitted_ids: live rotations, ORDERED, vs the canonical admission prefixes"
  local checked=" " arms=0
  for spec in "--frontier-factorial:10:FRONTIER-FACTORIAL" \
              "--frontier-extension:8:FRONTIER-EXTENSION" \
              "--frontier-interior:12:FRONTIER-INTERIOR"; do
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
      # A missing trailer is recorded and the ARM walk below still runs: a truncated log can still
      # answer every question about the lines it does carry.
      if ! grep -q "^$tag done order=$order warmup=0 rounds=$lanes lanes=$lanes\$" "$log"; then
        bad "$flag order=$order trailer — a truncated log is not a pass" \
            "$tag done order=$order warmup=0 rounds=$lanes lanes=$lanes" "absent"
      fi
      local n; n=$(grep -c '^ARM ' "$log")
      [ "$n" = "$lanes" ] || bad "$flag order=$order ARM line count" "$lanes" "$n"
      local label c removals nadm ids want K
      while read -r _ label _ _ _ _ _ c removals nadm ids; do
        arms=$((arms + 1))
        case "$label" in
          k*@128) K=${label#k}; K=${K%@128} ;;
          hot16@128) K=16 ;;
          cache0@128 | control_lb@128 | control@256)
            [ "$ids" = "-" ] && [ "$nadm" = 0 ] || bad "$label admits '$ids' ($nadm); it has no admitted set"
            continue ;;
          *) notrun "$flag order=$order lane $label" "the rotation names a label this oracle has no row for"; continue ;;
        esac
        want=$(printf '%s' "$ADMISSION_ORDER" | cut -d, -f"1-$K")
        # The ARM line's C and removals are what Task 3's slope pricing divides by, so they
        # are GATED against the oracle here rather than echoed: C from the table, removals
        # as Rc - C.
        local row want_c want_rem
        row=$(oracle_rows | awk -v k="${label%@128}" '$1==k {print $5, $6 - $5}')
        if [ -z "$row" ]; then
          notrun "$label" "the committed oracle has no row for it, so C and removals cannot be checked"
          continue
        fi
        want_c=${row%% *}; want_rem=${row##* }
        # FOUR readings of one ARM line — the ordered prefix, the admitted count, C, and removals.
        # This was an `if/elif/elif/elif` chain, so the first mismatch hid the other three; they are
        # independent facts about the dealt plan and all four are taken now.
        local arm_ok=1
        if [ "$ids" != "$want" ]; then
          bad "$label order=$order admitted_ids is not the canonical prefix at K=$K" "$want" "$ids"
          arm_ok=0
        fi
        if [ "$nadm" != "$K" ]; then
          bad "$label order=$order admitted-id count" "$K" "$nadm"; arm_ok=0
        fi
        if [ "$c" != "$want_c" ]; then
          bad "$label order=$order ARM C against the oracle" "$want_c" "$c"; arm_ok=0
        fi
        if [ "$removals" != "$want_rem" ]; then
          bad "$label order=$order ARM removals against the oracle (Rc-C)" "$want_rem" "$removals"
          arm_ok=0
        fi
        if [ "$arm_ok" = 1 ]; then
          checked="$checked$order/$label "
          note "  $label/$order: K=$K C=$c/$want_c removals=$removals/$want_rem, prefix exact"
        fi
      done < <(grep '^ARM ' "$log")
    done
  done
  # Roll call: every kN lane, under both orders, over the union of the three rotations.
  local ran=0
  for order in census locality; do
    for arm in $ARMS hot16; do
      case "$checked" in
        *" $order/$arm@128 "*) ran=$((ran + 1)) ;;
        *) bad "no admitted_ids check ran for $arm under $order" "a checked ARM line" "none" ;;
      esac
    done
  done
  note "  ARM lines parsed=$arms, lane/order checks=$ran/34"
  cellrow "admitted_ids / C / removals against the oracle" "$ran" "$ran"
  [ "$arms" = 60 ] || bad "ARM lines over the six runs count; a check that never ran is not a verdict either way" "60" "${arms}"
  [ "$ran" = 34 ] || bad "lane/order admission checks count; a check that never ran is not a verdict either way" "34" "${ran}"
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
  lane_is sass
  note "### frozen SASS: the nine bodies, byte-identical to the R3/R4 freeze artifacts"
  if ! require_shipped "the frozen-SASS lane"; then
    notrun "the frozen-SASS lane" "BUILD-ORDER: the archive under it is not the SHIPPED build, so its bodies would be another build's"
    return
  fi
  local ar=$ARCHIVE work="$TMP/sass" ar_abs
  ar_abs=$(readlink -f "$ar")
  mkdir -p "$work"
  # The freeze artifacts scope themselves to the pair TU's OWN fatbin; the device-linked
  # copy differs in relocated MOV/UMOV immediates and would report a false DIFFERS.
  ( cd "$work" && ar x "$ar_abs" uniskip_lsb_pair.cu.o ) 2>/dev/null
  if [ ! -f "$work/uniskip_lsb_pair.cu.o" ]; then
    notrun "the frozen-SASS lane" "could not extract uniskip_lsb_pair.cu.o from $ar"
    return
  fi
  if ! cuobjdump -sass "$work/uniskip_lsb_pair.cu.o" >"$work/dump.txt" 2>"$work/dump.err"; then
    notrun "the frozen-SASS lane" "cuobjdump failed on the pair TU — see the tail below"
    tail -3 "$work/dump.err"; return
  fi
  norm_dump "$work/dump.txt" "$work/live"
  local ok=0 rows=0 fn art kind want
  while IFS='|' read -r fn art kind want; do
    [ -n "$fn" ] || continue
    rows=$((rows + 1))
    if [ ! -f "$work/live/$fn" ]; then
      notrun "$fn" "the symbol is missing from the built archive, so there is nothing to compare"
      continue
    fi
    artifact_body "$kind" "$SDD/$art" "$fn" "$work/want-$fn"
    local have_n want_n
    have_n=$(wc -l <"$work/live/$fn")
    want_n=$(wc -l <"$work/want-$fn")
    # BOTH readings, whatever the other said: the artifact's own instruction count against the record,
    # and the live body against the artifact. A moved count used to hide the body comparison behind it,
    # and "the record drifted" and "the body changed" are different findings.
    local body_ok=1
    if [ "$want_n" != "$want" ]; then
      bad "$fn: artifact $art instruction count against the record" "$want" "$want_n"
      body_ok=0
    fi
    if cmp -s "$work/live/$fn" "$work/want-$fn"; then
      note "  IDENTICAL $fn ($have_n instrs)"
    else
      bad "$fn body against $art" "$want_n instrs, byte-identical" "$have_n instrs, differing"
      diff "$work/want-$fn" "$work/live/$fn" | head -6
      body_ok=0
    fi
    [ "$body_ok" = 1 ] && ok=$((ok + 1))
  done <<< "$SASS_EXPECT"
  note "  frozen bodies $ok/$rows identical"
  cellrow "the nine frozen R3/R4 pair bodies" "$rows" "$ok"
  [ "$rows" = 9 ] || bad "frozen bodies count; a check that never ran is not a verdict either way" "9" "${rows}"
  [ "$ok" = 9 ] || bad "frozen SASS is not 9/9"
}

# ---------------------------------------------------------------- builds + regression

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

# ---------------------------------------------------------------- fixtures

# GPU-free, and the only lane here that is: it runs the emitter against generated logs, so it
# gates the R8 interior decision path (and, by replaying the archived R5 logs when they are
# there, that the R5 path this file's rung owns still emits).
fixtures() {
  lane_is fixtures
  note "### emitter fixture matrix (tools/r4_table.py, R8 interior + R5 replay)"
  if bash "$FIXTURES" > "$TMP/fixtures.log" 2>&1; then
    note "  $(tail -1 "$TMP/fixtures.log")"
    cellrow "r5 emitter fixtures" 1 1
  else
    # The sub-suite printed its own summary; carry it into this one and reproduce its transcript.
    bad "r5 emitter fixtures" "0 failed" "$(tail -1 "$TMP/fixtures.log")"
    cellrow "r5 emitter fixtures" 1 0
    cat "$TMP/fixtures.log"
  fi
}

regression() {
  lane_is regression
  if ! ensure_diag; then
    notrun "the whole regression lane" "the diagnostic build did not complete, so r3/r4 would gate the wrong binary"
    return
  fi
  local g out rc nested
  for g in r3_gates.sh r4_gates.sh; do
    note "### regression: $g all"
    out=$("$DIR/$g" all 2>&1); rc=$?
    # Echo the sub-script's OWN whole-matrix report — its totals row, its NOT RUN and MISMATCHES
    # blocks — not just a pass/fail. A nested gate's board is part of this board.
    printf '%s\n' "$out" \
      | grep -E '^(  cells=|  oracle cells=|  gated arms=|MISMATCH|NOT RUN|\| |### (NOT RUN|MISMATCHES)|\*\*)' \
      | awk '{print "    " $0}'
    # Two readings, both taken: the status, and the nested totals row.
    nested=$(grep -m1 '^| \*\*total\*\* |' <<< "$out")
    [ "$rc" = 0 ] || bad "$g all exit status" "0" "$rc"
    if [ -z "$nested" ]; then
      notrun "$g all" "it printed no totals row, so its matrix cannot be carried into this one"
      cellrow "regression: $g all" 1 0
    else
      # Carry the nested cell counts into this script's matrix, so the totals here include them.
      local ncells nok nbad
      ncells=$(sed -E 's/.*\| \*\*([0-9]+)\*\* \| \*\*[0-9]+\*\* \| \*\*[0-9]+\*\* \|.*/\1/' <<< "$nested")
      nok=$(sed -E 's/.*\| \*\*[0-9]+\*\* \| \*\*([0-9]+)\*\* \| \*\*[0-9]+\*\* \|.*/\1/' <<< "$nested")
      nbad=$(sed -E 's/.*\| \*\*[0-9]+\*\* \| \*\*[0-9]+\*\* \| \*\*([0-9]+)\*\* \|.*/\1/' <<< "$nested")
      cellrow "regression: $g all (nested)" "${ncells:-1}" "${nok:-0}"
      [ "${nbad:-0}" = 0 ] || bad "$g all nested mismatches" "0" "$nbad"
    fi
  done
}

case "${1:-all}" in
  matrix) matrix ;;
  counts) counts ;;
  admitted) admitted ;;
  sass) sass ;;
  fixtures) fixtures ;;
  regression) regression ;;
  # `sass` first: it is the only lane that must see the shipped build, and `counts` swaps
  # the binary underneath everything after it. `fixtures` needs no binary at all, so it sits
  # before the lane that swaps one.
  all) sass; matrix; admitted; fixtures; counts; regression ;;
  *) echo "usage: $0 {matrix|counts|admitted|sass|fixtures|regression|all}" >&2; exit 2 ;;
esac
gate_summary
exit "$fail"
