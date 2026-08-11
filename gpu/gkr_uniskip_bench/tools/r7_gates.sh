#!/usr/bin/env bash
# v3 R7 segmented-pair gates, executable rather than transcribed.
#
#   sass        the nine frozen bodies (by INVOKING r5_gates.sh sass, so that table lives in
#               one place) plus the five seg symbols: symbol set, per-symbol normalized
#               instruction counts, `_cv64` normalized-IDENTICAL to `_cv100`, and the shipped
#               resource usage (72 regs, no stack, no local) — SHIPPED build only, and it says
#               so instead of comparing the wrong binary
#   matrix      Task 5's validation matrix, scripted: q parity over the 12 pinned carrier x arm
#               pairs against the LOCAL control128, the self-product cells (also against the
#               local reference), the CPU-oracle cells, the dealt-plan SEG line against the
#               committed oracle, the per-symbol carveout echoes, the ARM lane facts and the
#               three rotations end to end
#   counts      the diagnostic chain counter per cohort, over every pinned pair and both term
#               orders — needs the diagnostic binary, which this lane builds
#   cpu         the crate's GPU-free unit tests (cpu_*)
#   fixtures    the emitter's fixture matrix — every decision row and every fail-closed guard
#               of tools/r7_table.py, self-generating, GPU-free
#   regression  tools/r5_gates.sh all, which itself chains r3 + r4
#   all         sass; matrix; counts; cpu; fixtures; regression — sequenced so `sass` sees the
#               shipped build and every later lane that needs it gets it back
#
# Usage, from the repo root:
#   cargo build --release -p gpu_gkr_uniskip_bench
#   .agents/bin/with_gpu_lock.sh gpu/gkr_uniskip_bench/tools/r7_gates.sh all
#
# `counts` and `regression` need GPU_GKR_UNISKIP_BENCH_WINDOW_DIAG=1. This script builds that
# binary ITSELF and rebuilds the shipped one before any lane that needs it and on exit —
# whatever it was handed and however it exits. The diagnostic build spills 8 B on the seg-S
# symbols (Task 3), so a diagnostic binary left behind times like a diagnostic binary, and the
# next thing anyone runs here is a measurement.
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

# The five seg symbols: fn|normalized instruction count|shared bytes. Task 3 and Task 4
# measured these on the shipped build; `_cv64` and `_cv100` are ONE body under two symbols, so
# their bodies must also be identical to each other after normalization.
SEG_SYMBOLS="ab_gkr_uniskip_eval_lsb_seg_recompute_kernel|8336|2048
ab_gkr_uniskip_eval_lsb_seg_g_kernel|9560|2048
ab_gkr_uniskip_eval_lsb_seg_s_acc_kernel|10088|0
ab_gkr_uniskip_eval_lsb_seg_s_cv100_kernel|9784|0
ab_gkr_uniskip_eval_lsb_seg_s_cv64_kernel|9784|0"
SEG_TU=uniskip_lsb_seg.cu.o

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
  # seg carriers agreeing with each other proves only that they agree.
  note "### self-products 60: one S and one G pair, both orders, vs the LOCAL reference"
  local scells=0 spass=0
  for order in census locality; do
    local sref; sref=$(qhash --block-threads 128 --self-products 60 --term-order "$order")
    usable "$sref" "local control128 sp60 order=$order" || continue
    note "  reference control128 sp60 $order = $sref"
    for carrier in seg-s seg-g; do
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
  [ "$scells" = 4 ] || bad "expected 4 self-product cells, ran $scells"
  [ "$scells" = "$spass" ] || bad "self-product matrix incomplete"

  # CPU oracle — the only leg that does not go through `q` alone.
  note "### CPU oracle (--validate), one cell per carrier family and order"
  local oks=0 runs=0
  for order in census locality; do
    for carrier in seg-s seg-g; do
      runs=$((runs + 1))
      if "$B" --log-trace 12 --warmup 0 --iterations 1 --mode lsb-pair --block-threads 128 \
           --cache-arm hot16 --carrier "$carrier" --term-order "$order" --validate 2>/dev/null \
           | grep -q '^q validate: OK (32/32)'; then
        oks=$((oks + 1))
      else bad "CPU oracle $carrier/hot16 order=$order"; fi
    done
  done
  note "  oracle cells=$runs passed=$oks"
  [ "$runs" = 4 ] || bad "expected 4 oracle cells, ran $runs"
  [ "$runs" = "$oks" ] || bad "CPU oracle incomplete"
}

seg_line_cells() {
  note "### the dealt-plan SEG line, against the COMMITTED oracle (r7_table.py --seg-line)"
  local cells=0 pass=0 order flag want log n got
  for order in census locality; do
    want=$($EMITTER --seg-line "$order")
    if [ -z "$want" ]; then bad "the emitter rendered no oracle SEG line for $order"; continue; fi
    note "  oracle $order: $want"
    # A rotation owns both block sizes internally, so only the single-arm surface names one.
    for flag in --seg-smem-factorial --seg-gmem-factorial \
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
  [ "$cells" = 8 ] || bad "expected 8 SEG-line cells, ran $cells"
  [ "$cells" = "$pass" ] || bad "SEG-line cells incomplete"
}

echo_cells() {
  note "### the applied carveout, one echo per USED symbol (the emitter cross-checks these)"
  local cached=eval_lsb_pair_cached_128_lb
  local rows="--seg-smem-factorial|16:$cached 32:eval_lsb_seg_s_cv64 100:eval_lsb_seg_s_cv100 32:eval_lsb_seg_s_acc 16:eval_lsb_seg_recompute
--seg-gmem-factorial|16:$cached 16:eval_lsb_seg_g 16:eval_lsb_seg_recompute
--seg-anchor|16:$cached
--seg-anchor --carveout-hint 32|32:$cached
--seg-anchor --carveout-hint 100|100:$cached
--block-threads 128 --cache-arm hot16 --carrier seg-s|32:eval_lsb_seg_s_cv64
--block-threads 128 --cache-arm k40 --carrier seg-s100|100:eval_lsb_seg_s_cv100
--block-threads 128 --cache-arm hot16 --carrier seg-s-acc|32:eval_lsb_seg_s_acc
--block-threads 128 --cache-arm hot16 --carrier seg-g|16:eval_lsb_seg_g
--block-threads 128 --cache-arm cache0 --carrier seg-recompute|16:eval_lsb_seg_recompute"
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
  [ "$cells" = 10 ] || bad "expected 10 echo cells, ran $cells"
  [ "$cells" = "$pass" ] || bad "echo cells incomplete"
}

lane_facts() {
  note "### ARM lane facts: C and removals per arm, off the rotations' own lines"
  local cells=0 pass=0 flag log lane c removals arm want_c want_rem chains
  for flag in --seg-smem-factorial --seg-gmem-factorial --seg-anchor; do
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
  [ "$cells" = 21 ] || bad "expected 21 lane-fact cells (10 + 9 + 2), ran $cells"
  [ "$cells" = "$pass" ] || bad "lane facts incomplete"
}

rotations() {
  note "### the three rotations end to end (one sample per lane per round)"
  local cells=0 pass=0 spec flag rounds lanes log n
  for spec in "--seg-smem-factorial:10:10" "--seg-gmem-factorial:9:9" "--seg-anchor:10:2"; do
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
  [ "$cells" = 3 ] || bad "expected 3 rotation cells, ran $cells"
  [ "$cells" = "$pass" ] || bad "rotation cells incomplete"
}

matrix() {
  if [ ! -x "$B" ]; then
    bad "matrix: no binary at $B — cargo build --release -p gpu_gkr_uniskip_bench"
    return
  fi
  note_flavor
  q_parity
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

counts() {
  ensure_diag || return
  note "### chain-count gate: per-cohort chains for every pinned pair, both term orders"
  local cells=0 pass=0 order carrier arm calls blocks cohorts per want
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
      note "  $carrier/$arm/$order: $calls total / $blocks blocks / $cohorts cohorts = $per per cohort"
    done <<< "$PAIRS"
  done
  note "  cells=$cells passed=$pass"
  [ "$cells" = 24 ] || bad "expected 24 chain cells, ran $cells"
  [ "$cells" = "$pass" ] || bad "chain-count gate incomplete"
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

seg_sass() {
  note "### the five seg symbols: symbol set, instruction counts, cv64 = cv100, resources"
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
  local rows=0 ok=0 fn want shared got res
  while IFS='|' read -r fn want shared; do
    [ -n "$fn" ] || continue
    rows=$((rows + 1))
    if [ ! -f "$work/live/$fn" ]; then bad "$fn is missing from the built archive"; continue; fi
    got=$(wc -l <"$work/live/$fn")
    # Resource usage is the SPILL gate: the diagnostic build spills 8 B on the S symbols, so
    # the shipped one saying STACK:0 LOCAL:0 at 72 registers is what makes a timing comparable.
    res=$(awk -v fn="$fn:" '$2 == fn {getline; print $0}' "$work/res.txt" \
          | tr -s ' ' | sed 's/^ //')
    if [ "$got" != "$want" ]; then
      bad "$fn has $got normalized instructions, the record pins $want"
      continue
    fi
    case "$res" in
      "REG:72 STACK:0 SHARED:$shared LOCAL:0 CONSTANT[0]:"*) ;;
      *) bad "$fn resource usage is [$res]; want REG:72 STACK:0 SHARED:$shared LOCAL:0"; continue ;;
    esac
    ok=$((ok + 1))
    note "  $fn: $got instrs, $res"
  done <<< "$SEG_SYMBOLS"
  note "  seg bodies $ok/$rows pinned"
  [ "$rows" = 5 ] || bad "expected 5 seg symbols, checked $rows"
  [ "$ok" = 5 ] || bad "the seg symbol table is not 5/5"
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
  sass) sass ;;
  cpu) cpu ;;
  fixtures) fixtures ;;
  regression) regression ;;
  # `sass` first: it is the only lane that must see the shipped build, and `counts` swaps the
  # binary underneath everything after it — the lanes that need it back ask for it themselves.
  all) sass; matrix; counts; cpu; fixtures; regression ;;
  *) echo "usage: $0 {sass|matrix|counts|cpu|fixtures|regression|all}" >&2; exit 2 ;;
esac
[ "$fail" = 0 ] && note "ALL GATES PASS"
exit "$fail"
