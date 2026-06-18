#!/usr/bin/env bash
#
# Benchmark the two register-allocation experiments back-to-back (interleaved) on the
# reference block:
#   opt1 (ts_in_gpr)    : 4 RISC-V values in host GPRs, timestamps in the 4 freed GPRs
#   opt2 (default)      : 8 RISC-V values in host GPRs, timestamps in XMM lanes
#
# Each config is built ONCE into its own test binary; the binaries are then run directly
# and interleaved (no per-rep recompile, robust to thermal/load drift).
#
# Usage:  ./run.sh [reps] [lazy|eager]
#   reps  : number of interleaved repetitions (default 5)
#   mode  : which path to benchmark (default lazy = batched + eager fallback)
#
set -uo pipefail
cd "$(dirname "$0")"

REPS="${1:-5}"
MODE="${2:-lazy}"
case "$MODE" in
  eager) T=jit::tests::test_jit_full_block_with_flattened_responder ;;
  lazy)  T=jit::tests::test_jit_full_block_with_flattened_responder_lazy ;;
  *) echo "usage: $0 [reps] [lazy|eager]" >&2; exit 1 ;;
esac

build_bin() { # $1=features ; echoes path of the freshly built test binary
  local out
  out="$(cargo test --features "$1" --release --lib "$T" --no-run 2>&1)" || { echo "$out" >&2; return 1; }
  echo "$out" | grep -oE '[^ (]*deps/riscv_transpiler-[a-f0-9]+' | head -1
}

echo "Building opt1 (ts_in_gpr: 4 GPRs + GPR timestamps)..." >&2
B1="$(build_bin "jit ts_in_gpr")"  || exit 1
cp "$B1" /tmp/jit_opt1             || { echo "copy opt1 failed ($B1)" >&2; exit 1; }
echo "Building opt2 (default: 8 GPRs + XMM timestamps)..." >&2
B2="$(build_bin "jit")"            || exit 1
cp "$B2" /tmp/jit_opt2             || { echo "copy opt2 failed ($B2)" >&2; exit 1; }

freq() { # $1=binary ; echoes the MHz number
  "$1" "$T" --exact --nocapture 2>/dev/null \
    | grep -oE 'Frequency is [0-9.]+' | grep -oE '[0-9.]+' | head -1
}

echo
echo "test=$T   reps=$REPS"
printf '%-4s %-20s %-20s\n' "rep" "opt1(4gpr)" "opt2(8gpr+xmm)"
for i in $(seq 1 "$REPS"); do
  o1="$(freq /tmp/jit_opt1)"
  o2="$(freq /tmp/jit_opt2)"
  printf '%-4s %-20s %-20s\n' "$i" "${o1:-FAIL}" "${o2:-FAIL}"
done
