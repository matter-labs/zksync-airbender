#!/usr/bin/env bash
set -euo pipefail

ALL_CIRCUITS=($(ls tools/gkr_verifier/src/bin/*.rs | sed 's|.*/||;s|\.rs||'))
ALL_STEPS=(circuits prover generator native corruption binaries transpiler)

usage() {
  echo "Usage: $0 [options] [steps...]"
  echo ""
  echo "Options:"
  echo "  --blake MODE       blake2_with_compression (default), blake2_g_function, mop_extension"
  echo "  --variant VAR      no_caches (default) or caches"
  echo "  --security-level L 80 (default), 100, or both"
  echo "  --from STEP        run this step and everything after it"
  echo "  --circuits A,B,..  select circuit(s) (comma-separated, default: all)"
  echo "  --cycles           show before/after cycle count comparison"
  echo "  --warnings         show compiler warnings (suppressed by default)"
  echo "  --dry-run          print what would run without executing"
  echo "  -h, --help         show this message"
  echo ""
  echo "Steps:"
  echo "  circuits      Compile GKR circuits"
  echo "  prover        Generate proof"
  echo "  generator     Regenerate inlined verifier"
  echo "  native        Run native tests"
  echo "  corruption    Run corruption tests"
  echo "  binaries      Build RISC-V binaries"
  echo "  transpiler    Run transpiler tests"
  echo ""
  echo "  malicious     Generate & verify malicious proofs (soundness gap tests)"
  echo ""
  echo "  Shorthands:"
  echo "  tests         = native + corruption + transpiler"
  echo "  all           = full pipeline (default, excludes malicious)"
  echo ""
  echo "Circuits:"
  for c in "${ALL_CIRCUITS[@]}"; do echo "  $c"; done
  echo ""
  echo "Examples:"
  echo "  $0 --from generator"
  echo "  $0 --circuits blake2_with_extended_control transpiler"
  echo "  $0 --blake mop_extension --from binaries --cycles"
  echo "  $0 --dry-run --from generator"
  exit 1
}

BLAKE="blake2_with_compression"
VARIANT="no_caches"
SECURITY_LEVEL="80"
FROM=""
SELECTED_CIRCUITS=()
DRY_RUN=false
SHOW_CYCLES=false
SHOW_WARNINGS=false

while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help) usage ;;
    --blake) BLAKE="$2"; shift 2 ;;
    --variant) VARIANT="$2"; shift 2 ;;
    --security-level) SECURITY_LEVEL="$2"; shift 2 ;;
    --from) FROM="$2"; shift 2 ;;
    --circuits) IFS=',' read -ra SELECTED_CIRCUITS <<< "$2"; shift 2 ;;
    --dry-run) DRY_RUN=true; shift ;;
    --cycles) SHOW_CYCLES=true; shift ;;
    --warnings) SHOW_WARNINGS=true; shift ;;
    *) break ;;
  esac
done

case "$SECURITY_LEVEL" in
  80|100|both) ;;
  *)
    echo "ERROR: --security-level must be 80, 100, or both. Got: $SECURITY_LEVEL" >&2
    exit 2 ;;
esac

case "$SECURITY_LEVEL" in
  80)   LEVEL_TEST_FILTER="_sec_80";  LEVEL_FEATURES="security_80" ;;
  100)  LEVEL_TEST_FILTER="_sec_100"; LEVEL_FEATURES="security_100" ;;
  both) LEVEL_TEST_FILTER="";         LEVEL_FEATURES="security_80,security_100" ;;
esac

if [[ ${#SELECTED_CIRCUITS[@]} -eq 0 ]]; then
  CIRCUITS=("${ALL_CIRCUITS[@]}")
else
  CIRCUITS=("${SELECTED_CIRCUITS[@]}")
fi

# --- Resolve steps ---

expand_steps() {
  for s in "$@"; do
    case "$s" in
      tests) echo "native corruption transpiler" ;;
      all) echo "${ALL_STEPS[*]}" ;;
      *) echo "$s" ;;
    esac
  done
}

VALID=" ${ALL_STEPS[*]} malicious "

if [[ $# -gt 0 ]]; then
  RAW_STEPS=($(expand_steps "$@"))
  for step in "${RAW_STEPS[@]}"; do
    if [[ ! "$VALID" =~ " $step " ]]; then
      echo "Unknown step: $step"
      usage
    fi
  done
  STEPS=()
  for s in "${ALL_STEPS[@]}"; do
    if [[ " ${RAW_STEPS[*]} " =~ " $s " ]]; then
      STEPS+=("$s")
    fi
  done
  if [[ " ${RAW_STEPS[*]} " =~ " malicious " ]]; then
    STEPS+=("malicious")
  fi
elif [[ -n "$FROM" ]]; then
  if [[ ! "$VALID" =~ " $FROM " ]]; then
    echo "Unknown step for --from: $FROM"
    usage
  fi
  found=false
  STEPS=()
  for s in "${ALL_STEPS[@]}"; do
    if [[ "$s" = "$FROM" ]]; then found=true; fi
    if $found; then STEPS+=("$s"); fi
  done
else
  STEPS=("${ALL_STEPS[@]}")
fi

# --- Build flags ---

FEATURES="${BLAKE},${LEVEL_FEATURES}"
VARIANT_FEATURES=""
GENERATOR_FEATURES="${LEVEL_FEATURES}"
if [[ "$VARIANT" = "no_caches" ]]; then
  FEATURES="${FEATURES},no_caches"
  VARIANT_FEATURES="--features no_caches"
  GENERATOR_FEATURES="${GENERATOR_FEATURES},no_caches"
fi

CIRCUIT_FILTER=""
if [[ ${#SELECTED_CIRCUITS[@]} -gt 0 ]]; then
  CIRCUIT_FILTER=$(IFS="|"; echo "${SELECTED_CIRCUITS[*]}")
fi

TEST_FILTERS=()
if [[ -n "$LEVEL_TEST_FILTER" ]]; then
  if [[ ${#SELECTED_CIRCUITS[@]} -gt 0 ]]; then
    for c in "${SELECTED_CIRCUITS[@]}"; do
      TEST_FILTERS+=("${c}${LEVEL_TEST_FILTER}")
    done
  else
    TEST_FILTERS+=("$LEVEL_TEST_FILTER")
  fi
elif [[ ${#SELECTED_CIRCUITS[@]} -gt 0 ]]; then
  TEST_FILTERS=("${SELECTED_CIRCUITS[@]}")
fi

WARN_FLAGS=""
if ! $SHOW_WARNINGS; then
  WARN_FLAGS="-Awarnings"
fi

# --- Helpers ---

run_step() {
  local label="$1"; shift
  echo "==> ${label}"
  if $DRY_RUN; then
    echo "    $*"
    return 0
  fi
  "$@"
}

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
if $SHOW_CYCLES && ! $DRY_RUN; then
  before=()
  while IFS= read -r n; do
    before+=("$n")
  done < <(read_cycles)
fi

# --- Run pipeline ---

for step in "${STEPS[@]}"; do
  case "$step" in
    circuits)
      run_step "Compile GKR circuits" \
        bash -c "cd cs && RUSTFLAGS=\"$WARN_FLAGS\" cargo test -p cs -- gkr" ;;
    prover)
      run_step "Generate proof" \
        bash -c "cd prover && RUST_MIN_STACK=100000000 RUSTFLAGS=\"$WARN_FLAGS\" cargo test -p prover --release --features gkr_self_checks $VARIANT_FEATURES -- --nocapture gkr_run_basic_unrolled_test${LEVEL_TEST_FILTER}" ;;
    generator)
      run_step "Regenerate verifier (variant=${VARIANT})" \
        bash -c "RUSTFLAGS=\"$WARN_FLAGS\" cargo test -p verifier_generator --no-default-features --features ${GENERATOR_FEATURES} --test generate_verifiers -- ${CIRCUIT_FILTER}" ;;
    native)
      run_step "Native tests" \
        env RUSTFLAGS="$WARN_FLAGS" cargo test -p verifier --no-default-features --features "$FEATURES" --test native -- "${TEST_FILTERS[@]}" --nocapture ;;
    corruption)
      run_step "Corruption tests" \
        env RUSTFLAGS="$WARN_FLAGS" cargo test -p verifier --no-default-features --features "$FEATURES" --test corruption -- "${TEST_FILTERS[@]}" --include-ignored --nocapture ;;
    binaries)
      run_step "Build RISC-V binaries (blake=${BLAKE}, variant=${VARIANT})" \
        bash -c "cd tools/gkr_verifier && ./dump_bin.sh --blake $BLAKE --variant $VARIANT $($SHOW_WARNINGS && echo --warnings) ${CIRCUITS[*]}" ;;
    transpiler)
      run_step "Transpiler tests" \
        env RUSTFLAGS="$WARN_FLAGS" cargo test -p verifier --no-default-features --features "$FEATURES" --test transpiler -- "${TEST_FILTERS[@]}" --include-ignored --nocapture ;;
    malicious)
      run_step "Generate malicious proofs (corrupt witness, no self-checks)" \
        bash -c "cd prover && RUST_MIN_STACK=100000000 RUSTFLAGS=\"$WARN_FLAGS\" cargo test -p prover --release --no-default-features --features prover,bincode $VARIANT_FEATURES -- --ignored --nocapture malicious_proof"
      run_step "Verify malicious proofs rejected (soundness gap tests)" \
        env RUSTFLAGS="$WARN_FLAGS" cargo test -p verifier --no-default-features --features "$FEATURES" --test malicious -- --include-ignored --nocapture ;;
  esac
done

# --- Cycle count comparison ---
if $SHOW_CYCLES && ! $DRY_RUN; then
  after=()
  while IFS= read -r n; do
    after+=("$n")
  done < <(read_cycles)

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
    sign=""
    [[ $d -gt 0 ]] && sign="+"
    printf "%-40s %10d %10d %10s\n" "${CIRCUITS[$i]}" "$b" "$a" "${sign}${d}"
  done
  total_d=$((total_after - total_before))
  sign=""
  [[ $total_d -gt 0 ]] && sign="+"
  printf "%-40s %10d %10d %10s\n" "TOTAL" "$total_before" "$total_after" "${sign}${total_d}"
fi

echo ""
echo "==> Done!"
