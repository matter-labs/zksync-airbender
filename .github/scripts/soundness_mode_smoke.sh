#!/usr/bin/env bash
# Prove and verify in every soundness mode, and reject every proof under the wrong mode: both by
# its label and with the label rewritten to the other mode.
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
mkdir -p "$out"
for mode in "${modes[@]}"; do
  "$cli" trusted-params --bin "$bin" --soundness-mode "$mode" \
    --output "$out/$mode-trusted-params.json"
done

# The artifact's JSON name of a CLI soundness mode.
label() {
  case $1 in
    pessimistic-conjecture) echo PessimisticConjecture ;;
    ethproofs-soundcalc) echo EthproofsSoundnessCalc ;;
  esac
}

# fails <log> <command...>: the command must fail; its output goes to <log>.
fails() {
  local log=$1
  shift
  if "$@" >"$log" 2>&1; then
    echo "$* succeeded" >&2
    exit 1
  fi
}

# check_modes <proof> <mode> <relabel error>: the proof verifies in its mode; under the other mode
# its label is rejected, and with the label rewritten verification fails with <relabel error>.
check_modes() {
  local proof=$1 mode=$2 relabel_error=$3 other log relabeled
  "$cli" verify --proof "$proof" --bin "$bin" --soundness-mode "$mode" \
    --trusted-params "$out/$mode-trusted-params.json"
  for other in "${modes[@]}"; do
    [[ "$other" == "$mode" ]] && continue
    echo "== $proof verified as $other must fail"
    log="$proof.as-$other.log"
    fails "$log" "$cli" verify --proof "$proof" --bin "$bin" --soundness-mode "$other" \
      --trusted-params "$out/$other-trusted-params.json"
    if ! grep -q SoundnessModeMismatch "$log"; then
      cat "$log" >&2
      echo "$proof failed as $other without SoundnessModeMismatch" >&2
      exit 1
    fi
    echo "== $proof relabeled as $other must fail"
    relabeled="$proof.relabeled-$other.json"
    sed "s/\"soundness_mode\": \"$(label "$mode")\"/\"soundness_mode\": \"$(label "$other")\"/" \
      "$proof" >"$relabeled"
    if cmp -s "$proof" "$relabeled"; then
      echo "$proof has no soundness_mode $(label "$mode") to relabel" >&2
      exit 1
    fi
    log="$relabeled.log"
    fails "$log" "$cli" verify --proof "$relabeled" --bin "$bin" --soundness-mode "$other" \
      --trusted-params "$out/$other-trusted-params.json"
    if ! grep -q "$relabel_error" "$log"; then
      cat "$log" >&2
      echo "$relabeled failed without $relabel_error" >&2
      exit 1
    fi
  done
}

check_unified() {
  local proof=$1 mode=$2
  check_modes "$proof" "$mode" "chain_end_params do not match the trusted per-layer end-params"
  # -z reads the file as one record, so the match spans the pretty-printed lines.
  if [[ "${EXPECT_UNROLLED:-0}" == 1 ]] &&
    ! grep -zqE '"unrolled_recursion_ms":[[:space:]]*\[[[:space:]]*[0-9]' "$proof"; then
    echo "$proof has no unrolled recursion layer" >&2
    exit 1
  fi
}

for mode in "${modes[@]}"; do
  echo "== $mode: prove base"
  "$cli" prove --bin "$bin" "${input[@]}" --target base --backend "$backend" \
    --soundness-mode "$mode" --output-dir "$out" --output-file "$mode-base.json" "${settings[@]}"
  check_modes "$out/$mode-base.json" "$mode" NativeVerificationFailed
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
