#!/usr/bin/env bash
#
# A/B benchmark the eager (default, packed-timestamp) JIT path WITHOUT vs WITH the
# `mem_merge` feature (load/store merging into wide vector stores).
#
# It builds two release test binaries (baseline = `--features jit`; merged =
# `--features jit,mem_merge`), runs the full-block benchmark test N times for each,
# parses the printed simulator frequency (MHz), and reports median / peak.
#
# Usage:
#   scripts/compare_mem_merge.sh [RUNS] [WINDOW]
#     RUNS    number of timed runs per config (default 8)
#     WINDOW  merge window for the merged build: 2 | 4 | 8 (default 8)
#
# Examples:
#   scripts/compare_mem_merge.sh
#   scripts/compare_mem_merge.sh 12 4
#   RISCV_MERGE_WINDOW=8 scripts/compare_mem_merge.sh 10
#
# Notes:
#   * Run on a quiet machine; close other heavy processes. The frequency metric is
#     emulated_instructions / run_program_wall_time, so it is sensitive to system load.
#     median/peak (not mean) are reported because run_program is deterministic and noise
#     is one-sided (additive).
#   * The merge window can also be passed via the RISCV_MERGE_WINDOW env var (the 2nd
#     positional arg wins if both are given).

set -euo pipefail

RUNS="${1:-8}"
WINDOW="${2:-${RISCV_MERGE_WINDOW:-8}}"

TEST=jit::tests::test_jit_full_block_with_flattened_responder
CRATE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$CRATE_DIR"

case "$WINDOW" in
  2|4|8) ;;
  *) echo "WINDOW must be 2, 4 or 8 (got '$WINDOW')" >&2; exit 1 ;;
esac

# Resolve the compiled test executable for a given feature set.
build_bin() {
  local feats="$1"
  cargo test --features "$feats" --release --lib --no-run --message-format=json 2>/dev/null \
    | python3 -c "import sys,json
for l in sys.stdin:
 try: o=json.loads(l)
 except: continue
 if o.get('reason')=='compiler-artifact' and o.get('target',{}).get('name')=='riscv_transpiler' and o.get('executable'):
  print(o['executable'])" | tail -1
}

echo ">> building baseline (features: jit) ..." >&2
BASE_BIN="$(build_bin "jit")"
echo ">> building merged   (features: jit,mem_merge) ..." >&2
MERGE_BIN="$(build_bin "jit,mem_merge")"

if [[ -z "${BASE_BIN:-}" || -z "${MERGE_BIN:-}" ]]; then
  echo "failed to locate test binaries" >&2
  exit 1
fi
echo ">> baseline: $BASE_BIN" >&2
echo ">> merged:   $MERGE_BIN (RISCV_MERGE_WINDOW=$WINDOW)" >&2

# Run the benchmark test once and extract the reported frequency (MHz).
freq() {
  "$1" "$TEST" --exact "$TEST" --nocapture 2>/dev/null \
    | grep -oiE 'Frequency is [0-9.]+' | grep -oE '[0-9.]+' | head -1
}

TMP="$(mktemp)"
trap 'rm -f "$TMP"' EXIT

printf '%-6s %12s %12s\n' "run" "baseline" "merged(w$WINDOW)" >&2
for ((i = 1; i <= RUNS; i++)); do
  b="$(freq "$BASE_BIN")"
  m="$(RISCV_MERGE_WINDOW="$WINDOW" freq "$MERGE_BIN")"
  printf '%-6s %12s %12s\n' "$i" "$b" "$m" >&2
  echo "$b $m" >> "$TMP"
done

stats() { # column -> "median peak"
  awk -v c="$1" '{print $c}' "$TMP" | sort -n \
    | awk '{a[NR]=$1} END{n=NR; med=(n%2?a[(n+1)/2]:(a[n/2]+a[n/2+1])/2); printf "%.1f %.1f", med, a[n]}'
}

read -r BMED BPEAK <<<"$(stats 1)"
read -r MMED MPEAK <<<"$(stats 2)"
DELTA="$(awk -v a="$BMED" -v b="$MMED" 'BEGIN{printf "%+.1f", (b-a)/a*100}')"

echo
printf '=== mem_merge A/B (full block, %d runs, window=%s) ===\n' "$RUNS" "$WINDOW"
printf '%-18s median=%-7s peak=%-7s MHz\n' "baseline" "$BMED" "$BPEAK"
printf '%-18s median=%-7s peak=%-7s MHz\n' "mem_merge(w$WINDOW)" "$MMED" "$MPEAK"
printf '%-18s %s%%\n' "median delta" "$DELTA"
