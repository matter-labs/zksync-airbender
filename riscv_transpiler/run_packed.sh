#!/usr/bin/env bash
#
# Benchmark the EAGER path with the two timestamp-bookkeeping schemes, back-to-back
# (interleaved) on the reference block:
#   base   (default)   : per cycle, write each touched register's timestamp (to GPR/XMM/
#                        memory) and advance r8 per sub-slot.
#   packed (packed_ts) : per cycle, write ONE timestamp (the cycle's 0-mod-4 base) into the
#                        (32 x 33 x 33) array, and bump r8 once.
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

echo "Building base eager (default)..." >&2
B="$(build_bin "jit")"            || exit 1
cp "$B" /tmp/jit_eager_base       || { echo "copy base failed ($B)" >&2; exit 1; }
echo "Building packed eager (packed_ts)..." >&2
P="$(build_bin "jit packed_ts")"  || exit 1
cp "$P" /tmp/jit_eager_packed     || { echo "copy packed failed ($P)" >&2; exit 1; }

freq() { # $1=binary ; echoes the MHz number
  "$1" "$T" --exact "$T" --nocapture 2>/dev/null \
    | grep -oE 'Frequency is [0-9.]+' | grep -oE '[0-9.]+' | head -1
}

echo
echo "test=$T   reps=$REPS"
printf '%-4s %-20s %-20s\n' "rep" "base(3-write)" "packed(1-store)"
for i in $(seq 1 "$REPS"); do
  b="$(freq /tmp/jit_eager_base)"
  p="$(freq /tmp/jit_eager_packed)"
  printf '%-4s %-20s %-20s\n' "$i" "${b:-FAIL}" "${p:-FAIL}"
done
