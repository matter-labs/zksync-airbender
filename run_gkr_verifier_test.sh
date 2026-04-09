#!/usr/bin/env bash
set -euo pipefail

# Circuit variant: "no_caches" (default) or "" for cached
VARIANT="${GKR_VARIANT:-no_caches}"
# Blake mode: blake2_with_compression (default), blake2_g_function, mop_extension
BLAKE="${BLAKE_MODE:-blake2_with_compression}"

FEATURES="gkr_verify,${BLAKE}"
if [[ -n "$VARIANT" ]]; then
  FEATURES="${FEATURES},${VARIANT}"
fi

CIRCUITS=(
  add_sub_lui_auipc_mop
  bigint_with_extended_control
  blake2_with_extended_control
  jump_branch_slt
  keccak_special5
  mem_subword_only
  mem_word_only
  shift_binop
  inits_and_teardowns
)

read_cycles() {
  for circuit in "${CIRCUITS[@]}"; do
    local svg="verifier/gkr_flamegraph_${circuit}.svg"
    if [[ -f "$svg" ]]; then
      grep -o 'total_samples="[0-9]*"' "$svg" | grep -o '[0-9]*'
    else
      echo "0"
    fi
  done
}

# --- Record BEFORE cycles ---
echo "==> Reading cycle counts before tests..."
before=()
while IFS= read -r n; do
  before+=("$n")
done < <(read_cycles)

for i in "${!CIRCUITS[@]}"; do
  echo "  ${CIRCUITS[$i]}: ${before[$i]}"
done

# --- Run pipeline ---

# echo "==> Step 0: Compile GKR circuits"
# (cd cs && RUSTFLAGS="-Awarnings" cargo test -p cs -- gkr)

# echo "==> Step 1: Generate proof"
# (cd prover && RUST_MIN_STACK=100000000 RUSTFLAGS="-Awarnings" cargo test -p prover --release --features gkr_self_checks \
#   -- --nocapture gkr_run_basic_unrolled_test)

echo "==> Step 2: Regenerate inlined GKR verifier (variant=${VARIANT:-cached})"
RUSTFLAGS="-Awarnings" cargo test -p verifier_generator ${VARIANT:+--features $VARIANT} --test generate_verifiers

echo "==> Step 3: Build RISC-V binary (blake=${BLAKE}, variant=${VARIANT:-cached})"
(cd tools/gkr_verifier && BLAKE_MODE="$BLAKE" GKR_VARIANT="$VARIANT" ./dump_bin.sh)

echo "==> Step 4: Verifier tests (blake=${BLAKE}, variant=${VARIANT:-cached})"
RUSTFLAGS="-Awarnings" cargo test -p verifier --tests --features "$FEATURES" -- --include-ignored

# --- Record AFTER cycles ---
echo ""
echo "==> Reading cycle counts after tests..."
after=()
while IFS= read -r n; do
  after+=("$n")
done < <(read_cycles)

# --- Summary ---
echo ""
echo "=== Cycle Count Summary ==="
printf "%-40s %10s %10s %10s\n" "Circuit" "Before" "After" "Delta"
printf "%-40s %10s %10s %10s\n" "-------" "------" "-----" "-----"
total_before=0
total_after=0
for i in "${!CIRCUITS[@]}"; do
  b=${before[$i]}
  a=${after[$i]}
  d=$((a - b))
  total_before=$((total_before + b))
  total_after=$((total_after + a))
  if [[ $d -gt 0 ]]; then
    sign="+"
  elif [[ $d -lt 0 ]]; then
    sign=""
  else
    sign=""
  fi
  printf "%-40s %10d %10d %10s\n" "${CIRCUITS[$i]}" "$b" "$a" "${sign}${d}"
done
total_d=$((total_after - total_before))
if [[ $total_d -gt 0 ]]; then
  sign="+"
elif [[ $total_d -lt 0 ]]; then
  sign=""
else
  sign=""
fi
printf "%-40s %10d %10d %10s\n" "TOTAL" "$total_before" "$total_after" "${sign}${total_d}"
echo ""
echo "==> All tests passed!"
