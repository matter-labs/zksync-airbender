#!/usr/bin/env bash
#
# Benchmark the EAGER path with the two register-timestamp schemes, back-to-back
# (interleaved) on the reference block:
#   packed (default)  : write ONE timestamp (the cycle's 0-mod-4 base) into the
#                       (32 x 33 x 33) array and bump r8 once; reconstruct offline.
#   xmm    (xmm_ts)   : keep the 8 mapped registers' timestamps live in XMM lanes
#                       (`pinsrq`) and advance r8 per sub-slot.
#
# Each config is built ONCE into its own test binary; the binaries are then run directly
# and interleaved (no per-rep recompile, robust to thermal/load drift).
#
# Usage:  ./run_packed.sh [reps]   (default 5)
#
set -uo pipefail
cd "$(dirname "$0")"

REPS="${1:-5}"
T=jit::tests::test_jit_full_block_with_flattened_responder   # eager full-block

build_bin() { # $1=features ; echoes path of the freshly built test binary
  local out
  out="$(cargo test --features "$1" --release --lib "$T" --no-run 2>&1)" || { echo "$out" >&2; return 1; }
  echo "$out" | grep -oE '[^ (]*deps/riscv_transpiler-[a-f0-9]+' | head -1
}

echo "Building packed eager (default)..." >&2
P="$(build_bin "jit")"            || exit 1
cp "$P" /tmp/jit_eager_packed     || { echo "copy packed failed ($P)" >&2; exit 1; }
echo "Building xmm eager (xmm_ts)..." >&2
X="$(build_bin "jit xmm_ts")"     || exit 1
cp "$X" /tmp/jit_eager_xmm        || { echo "copy xmm failed ($X)" >&2; exit 1; }

freq() { # $1=binary ; echoes the MHz number
  "$1" "$T" --exact "$T" --nocapture 2>/dev/null \
    | grep -oE 'Frequency is [0-9.]+' | grep -oE '[0-9.]+' | head -1
}

echo
echo "test=$T   reps=$REPS"
printf '%-4s %-20s %-20s\n' "rep" "packed(default)" "xmm(xmm_ts)"
for i in $(seq 1 "$REPS"); do
  p="$(freq /tmp/jit_eager_packed)"
  x="$(freq /tmp/jit_eager_xmm)"
  printf '%-4s %-20s %-20s\n' "$i" "${p:-FAIL}" "${x:-FAIL}"
done
