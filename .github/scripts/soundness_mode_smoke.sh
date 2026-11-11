#!/usr/bin/env bash
# Prove and verify in every soundness mode, and reject every proof under the wrong mode: both by
# its label and with the label rewritten to the other mode.
#
# usage: soundness_mode_smoke.sh CLI BIN BACKEND [BACKEND SETTINGS...]
#   INPUT_FILE        the program's input, passed to `prove` (optional)
#   DIRECT=1          also prove recursion-unified directly from the input
#   EXPECT_UNROLLED=1 require every recursion-unified proof to include an unrolled recursion layer
#   FIXTURE_CHAIN_ROOT verify existing <mode>/{base,unified}.json.zlib instead of proving
#   FIXTURE_CODEC      prebuilt fixture-codec for existing artifacts
#   SOUNDNESS_MODE     check only this mode's artifacts (wrong-mode checks still cover both)
#   SMOKE_OUTPUT_DIR   temporary outputs and logs
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
all_modes=(pessimistic-conjecture ethproofs-soundcalc)
modes=("${all_modes[@]}")
if [[ -n ${SOUNDNESS_MODE:-} ]]; then
  [[ $SOUNDNESS_MODE == pessimistic-conjecture || $SOUNDNESS_MODE == ethproofs-soundcalc ]]
  modes=("$SOUNDNESS_MODE")
fi
out=${SMOKE_OUTPUT_DIR:-output/soundness-mode-smoke}
mkdir -p "$out"
for mode in "${all_modes[@]}"; do
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
  for other in "${all_modes[@]}"; do
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
    sed "s/\"soundness_mode\":[[:space:]]*\"$(label "$mode")\"/\"soundness_mode\": \"$(label "$other")\"/" \
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
  # A verified unified chain has base, bridge, final and one entry per unrolled layer.
  # -z lets the check accept both compact and pretty JSON.
  if [[ "${EXPECT_UNROLLED:-0}" == 1 ]] &&
    ! grep -zqE '"chain_end_params":[[:space:]]*\[([[:space:]]*\[[0-9,[:space:]]*\],){3}[[:space:]]*\[' "$proof"; then
    echo "$proof has no unrolled recursion layer" >&2
    exit 1
  fi
}

if [[ -n ${FIXTURE_CHAIN_ROOT:-} ]]; then
  [[ -x ${FIXTURE_CODEC:-} ]]
  for mode in "${modes[@]}"; do
    directory="$FIXTURE_CHAIN_ROOT/${mode//-/_}"
    "$FIXTURE_CODEC" decode "$directory/base.json.zlib" >"$out/$mode-base.json"
    "$FIXTURE_CODEC" decode "$directory/unified.json.zlib" >"$out/$mode-unified.json"
    check_modes "$out/$mode-base.json" "$mode" NativeVerificationFailed
    check_unified "$out/$mode-unified.json" "$mode"
  done
  exit 0
fi

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
