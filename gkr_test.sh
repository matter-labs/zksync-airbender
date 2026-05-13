#!/usr/bin/env bash
set -euo pipefail

die() { echo "ERROR: $*" >&2; exit 2; }

# Must run from repo root.
[[ -f Cargo.toml && -d tools/gkr_verifier/src/bin ]] \
  || die "must run from airbender repo root (Cargo.toml + tools/gkr_verifier/src/bin not found)"

ALL_CIRCUITS=($(ls tools/gkr_verifier/src/bin/*.rs | sed 's|.*/||;s|\.rs||;s|_sec_[0-9]*$||' | sort -u))
ALL_STEPS=(circuits witness_gen prover generator native corruption binaries transpiler)

usage() {
  cat <<EOF
Usage: $0 [options] [steps...]

Runs the GKR pipeline. Steps execute in canonical pipeline order regardless of
the order they are passed on the command line. Default with no steps is "all".

Options:
  --blake MODE          blake2_with_compression (default), blake2_g_function, mop_extension
  --variant VAR         no_caches (default) or caches
  --security-level L    80 (default), 100, or both
  --from STEP           run STEP and everything after it (canonical order)
  --circuits A,B,...    base circuit name(s), comma-separated (default: all)
  --cycles              before/after cycle comparison from transpiler flamegraphs
  --warnings            show compiler warnings (suppressed by default)
  --dry-run             print what would run without executing
  -h, --help            show this message

Steps (run in this canonical order):
  circuits      Compile GKR circuits
  witness_gen   Generate witness evaluation functions
  prover        Generate proof
  generator     Regenerate inlined verifier
  native        Run native tests
  corruption    Run corruption tests
  binaries      Build RISC-V binaries
  transpiler    Run transpiler tests (writes flamegraphs)

Extra step (off by default, runs last when invoked):
  malicious     Generate & verify malicious proofs (soundness gap tests)

Shorthands:
  tests         expands to: native corruption transpiler
  all           expands to: full canonical pipeline (excludes malicious)

Exit codes:
  0  success
  1  bad usage (unknown step or --help)
  2  invalid argument value or wrong working directory
  3  no bin files for the requested circuit/level combination

Examples:
  $0 --from generator
  $0 --circuits blake2_with_extended_control --from binaries
  $0 --blake mop_extension --from binaries --cycles
  $0 --security-level both --from generator
  $0 --dry-run --from generator

Circuits:
EOF
  for c in "${ALL_CIRCUITS[@]}"; do echo "  $c"; done
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
  *) die "--security-level must be 80, 100, or both. Got: $SECURITY_LEVEL" ;;
esac

case "$SECURITY_LEVEL" in
  80)   LEVELS=(sec_80) ;;
  100)  LEVELS=(sec_100) ;;
  both) LEVELS=(sec_80 sec_100) ;;
esac

# All level-derived state flows from LEVELS so a new security level is one case arm.
LEVEL_FEATURES_ARR=()
for lvl in "${LEVELS[@]}"; do LEVEL_FEATURES_ARR+=("security_${lvl#sec_}"); done
LEVEL_FEATURES=$(IFS=,; echo "${LEVEL_FEATURES_ARR[*]}")

# Test filter is the level suffix when one level is selected; empty under "both"
# so cargo's substring match picks up every level's tests.
LEVEL_TEST_FILTER=""
[[ ${#LEVELS[@]} -eq 1 ]] && LEVEL_TEST_FILTER="_${LEVELS[0]}"

if [[ ${#SELECTED_CIRCUITS[@]} -eq 0 ]]; then
  base_circuits=("${ALL_CIRCUITS[@]}")
else
  base_circuits=("${SELECTED_CIRCUITS[@]}")
fi

# CIRCUITS is the (base × level) cross-product, filtered by which bin files exist.
# Each entry is the full bin name (e.g. add_sub_lui_auipc_mop_sec_80) used for both
# dump_bin.sh and SVG lookup, so the level is unambiguous end-to-end.
CIRCUITS=()
for base in "${base_circuits[@]}"; do
  for lvl in "${LEVELS[@]}"; do
    if [[ -f "tools/gkr_verifier/src/bin/${base}_${lvl}.rs" ]]; then
      CIRCUITS+=("${base}_${lvl}")
    fi
  done
done

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
      echo "ERROR: unknown step: $step" >&2
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
    echo "ERROR: unknown step for --from: $FROM" >&2
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
GENERATOR_FEATURES="${LEVEL_FEATURES}"
VARIANT_FEATURES=()
if [[ "$VARIANT" = "no_caches" ]]; then
  FEATURES="${FEATURES},no_caches"
  GENERATOR_FEATURES="${GENERATOR_FEATURES},no_caches"
  VARIANT_FEATURES=(--features no_caches)
fi

# Generator's #[test] fn names are bare base circuit names. cargo test OR's
# positional filters as substring matches; a single "foo|bar" string would match
# "|" literally, so each circuit needs its own arg.
GENERATOR_FILTERS=()
if [[ ${#SELECTED_CIRCUITS[@]} -gt 0 ]]; then
  GENERATOR_FILTERS=("${SELECTED_CIRCUITS[@]}")
fi

# Native and transpiler test functions are named ${name}_sec_80 / ${name}_sec_100
# (level-suffixed). Corruption tests are named rejects_<kind>_${name} — no level
# suffix — so the level part of the filter would exclude all of them.
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

CORRUPTION_FILTERS=()
if [[ ${#SELECTED_CIRCUITS[@]} -gt 0 ]]; then
  CORRUPTION_FILTERS=("${SELECTED_CIRCUITS[@]}")
fi

# For local cargo invocations: -Awarnings silences compiler warnings unless
# --warnings was passed.
WARN_FLAGS=""
if ! $SHOW_WARNINGS; then
  WARN_FLAGS="-Awarnings"
fi

# For dump_bin.sh: it suppresses warnings by default; --warnings re-enables them
# (same convention as this script).
DUMP_BIN_WARN_FLAGS=()
if $SHOW_WARNINGS; then
  DUMP_BIN_WARN_FLAGS=(--warnings)
fi

# --- Helpers ---

# Run a command in a subshell after cd'ing to dir. Avoids `bash -c` quoting layers.
# Some workspace crates don't compile cleanly, so we cd into the target crate and
# let cargo's auto-detection scope the build, instead of `cargo -p X` from root.
in_dir() {
  local dir="$1"; shift
  ( cd "$dir" && "$@" )
}

run_step() {
  local label="$1"; shift
  echo "==> ${label}"
  if $DRY_RUN; then
    echo "    $*"
    return 0
  fi
  local start=$SECONDS
  "$@"
  printf "    [%ds] %s\n" "$((SECONDS - start))" "$label"
}

# Prover-side cargo invocations need RUST_MIN_STACK=100M because the recursive
# sumcheck/folding hits deep stack frames; the default 8M overflows.
run_prover_cargo() {
  in_dir prover env \
    RUST_MIN_STACK=100000000 \
    RUSTFLAGS="$WARN_FLAGS" \
    cargo test -p prover --release "$@"
}

read_cycles() {
  for circuit in "${CIRCUITS[@]}"; do
    local svg="verifier/gkr_flamegraph_${circuit}.svg"
    if [[ -f "$svg" ]]; then
      grep -o 'total_samples="[0-9]*"' "$svg" | grep -o '[0-9]*'
    else
      echo "WARN: $svg not found" >&2
      echo "MISSING"
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
        in_dir cs env RUSTFLAGS="$WARN_FLAGS" cargo test -p cs -- gkr ;;
    witness_gen)
      run_step "Generate witness evaluation functions" \
        in_dir witness_eval_generator env RUSTFLAGS="$WARN_FLAGS" cargo test -p witness_eval_generator -- gen_for_gkr ;;
    prover)
      run_step "Generate proof" \
        run_prover_cargo \
          --features gkr_self_checks "${VARIANT_FEATURES[@]+"${VARIANT_FEATURES[@]}"}" \
          -- --nocapture "gkr_run_basic_unrolled_test${LEVEL_TEST_FILTER}" ;;
    generator)
      run_step "Regenerate verifier (variant=${VARIANT})" \
        env RUSTFLAGS="$WARN_FLAGS" cargo test -p verifier_generator \
          --no-default-features --features "$GENERATOR_FEATURES" \
          --test generate_verifiers \
          -- "${GENERATOR_FILTERS[@]+"${GENERATOR_FILTERS[@]}"}" ;;
    native)
      run_step "Native tests" \
        env RUSTFLAGS="$WARN_FLAGS" cargo test -p verifier --no-default-features --features "$FEATURES" --test native -- "${TEST_FILTERS[@]+"${TEST_FILTERS[@]}"}" ;;
    corruption)
      run_step "Corruption tests" \
        env RUSTFLAGS="$WARN_FLAGS" cargo test -p verifier --no-default-features --features "$FEATURES" --test corruption -- "${CORRUPTION_FILTERS[@]+"${CORRUPTION_FILTERS[@]}"}" --include-ignored ;;
    binaries)
      if [[ ${#CIRCUITS[@]} -eq 0 ]]; then
        echo "ERROR: no bin files found for security-level=${SECURITY_LEVEL}, circuits=${SELECTED_CIRCUITS[*]:-all}" >&2
        echo "  expected tools/gkr_verifier/src/bin/<base>_<level>.rs for level(s): ${LEVELS[*]}" >&2
        exit 3
      fi
      run_step "Build RISC-V binaries (blake=${BLAKE}, variant=${VARIANT})" \
        in_dir tools/gkr_verifier ./dump_bin.sh \
          --blake "$BLAKE" --variant "$VARIANT" \
          "${DUMP_BIN_WARN_FLAGS[@]+"${DUMP_BIN_WARN_FLAGS[@]}"}" \
          "${CIRCUITS[@]}" ;;
    transpiler)
      run_step "Transpiler tests" \
        env RUSTFLAGS="$WARN_FLAGS" cargo test -p verifier --no-default-features --features "$FEATURES" --test transpiler -- "${TEST_FILTERS[@]+"${TEST_FILTERS[@]}"}" --include-ignored ;;
    malicious)
      run_step "Generate malicious proofs (corrupt witness, no self-checks)" \
        run_prover_cargo \
          --no-default-features --features prover,bincode "${VARIANT_FEATURES[@]+"${VARIANT_FEATURES[@]}"}" \
          -- --ignored --nocapture malicious_proof
      run_step "Verify malicious proofs rejected (soundness gap tests)" \
        env RUSTFLAGS="$WARN_FLAGS" cargo test -p verifier --no-default-features --features "$FEATURES" --test malicious -- --include-ignored ;;
  esac
done

# --- Cycle count comparison ---
if $SHOW_CYCLES && ! $DRY_RUN; then
  after=()
  while IFS= read -r n; do
    after+=("$n")
  done < <(read_cycles)

  # Markdown table — column padding makes it readable in the terminal AND
  # GitHub renders the alignment hints (`---:`) for right-aligned numeric cells.
  hr_circuit='----------------------------------------'
  hr_num='---------:'
  echo ""
  echo "### Cycle counts"
  echo ""
  printf "| %-40s | %10s | %10s | %10s |\n" "Circuit" "Before" "After" "Delta"
  printf "| %s | %s | %s | %s |\n" "$hr_circuit" "$hr_num" "$hr_num" "$hr_num"
  total_before=0
  total_after=0
  for i in "${!CIRCUITS[@]}"; do
    b=${before[$i]}
    a=${after[$i]}
    if [[ "$b" == "MISSING" || "$a" == "MISSING" ]]; then
      printf "| %-40s | %10s | %10s | %10s |\n" "${CIRCUITS[$i]}" "$b" "$a" "n/a"
      continue
    fi
    d=$((a - b))
    total_before=$((total_before + b))
    total_after=$((total_after + a))
    sign=""
    [[ $d -gt 0 ]] && sign="+"
    printf "| %-40s | %10d | %10d | %10s |\n" "${CIRCUITS[$i]}" "$b" "$a" "${sign}${d}"
  done
  total_d=$((total_after - total_before))
  sign=""
  [[ $total_d -gt 0 ]] && sign="+"
  printf "| %-40s | %10d | %10d | %10s |\n" "**TOTAL**" "$total_before" "$total_after" "${sign}${total_d}"
fi

echo ""
echo "==> Done!"
