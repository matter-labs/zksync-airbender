#!/usr/bin/env bash
# Prove, verify and reject under the wrong mode, with the same steps in every soundness mode:
# prove base -> continue to recursion-unified (and, with DIRECT=1, prove recursion-unified in
# one call), verifying each proof in its own mode and each recursion-unified proof as every
# other mode, which must fail with SoundnessModeMismatch.
#
# usage: soundness_mode_smoke.sh CLI BIN BACKEND [BACKEND SETTINGS...]
#   INPUT_FILE        the program's input, passed to `prove` (optional)
#   DIRECT=1          also prove recursion-unified directly from the input
#   EXPECT_UNROLLED=1 require every recursion-unified proof to include an unrolled recursion layer
set -euo pipefail

cli=$1
bin=$2
backend=$3
shift 3
settings=("$@")
input=()
if [[ -n "${INPUT_FILE:-}" ]]; then
  input=(--input-file "$INPUT_FILE")
fi
modes=(pessimistic-conjecture ethproofs-soundcalc)
out=output/soundness-mode-smoke
unified=()

check_unified() {
  local proof=$1 mode=$2
  "$cli" verify --proof "$proof" --bin "$bin" --soundness-mode "$mode"
  if [[ "${EXPECT_UNROLLED:-0}" == 1 ]] &&
    ! tr -d ' \n' <"$proof" | grep -q '"unrolled_recursion_ms":\[[0-9]'; then
    echo "$proof has no unrolled recursion layer" >&2
    exit 1
  fi
  unified+=("$mode:$proof")
}

for mode in "${modes[@]}"; do
  echo "== $mode: prove base"
  "$cli" prove --bin "$bin" "${input[@]}" --target base --backend "$backend" \
    --soundness-mode "$mode" --output-dir "$out" --output-file "$mode-base.json" "${settings[@]}"
  "$cli" verify --proof "$out/$mode-base.json" --bin "$bin" --soundness-mode "$mode"
  echo "== $mode: continue to recursion-unified"
  "$cli" continue-proof --proof "$out/$mode-base.json" --bin "$bin" --target recursion-unified \
    --backend "$backend" --soundness-mode "$mode" --output-dir "$out" \
    --output-file "$mode-continued.json" "${settings[@]}"
  check_unified "$out/$mode-continued.json" "$mode"
  if [[ "${DIRECT:-0}" == 1 ]]; then
    echo "== $mode: prove recursion-unified"
    "$cli" prove --bin "$bin" "${input[@]}" --target recursion-unified --backend "$backend" \
      --soundness-mode "$mode" --output-dir "$out" --output-file "$mode-direct.json" \
      "${settings[@]}"
    check_unified "$out/$mode-direct.json" "$mode"
  fi
done

for entry in "${unified[@]}"; do
  mode=${entry%%:*}
  proof=${entry#*:}
  for other in "${modes[@]}"; do
    [[ "$other" == "$mode" ]] && continue
    echo "== $proof verified as $other must fail"
    log="$proof.as-$other.log"
    if "$cli" verify --proof "$proof" --bin "$bin" --soundness-mode "$other" >"$log" 2>&1; then
      echo "$proof verified as $other" >&2
      exit 1
    fi
    if ! grep -q SoundnessModeMismatch "$log"; then
      cat "$log" >&2
      echo "$proof failed as $other without SoundnessModeMismatch" >&2
      exit 1
    fi
  done
done
