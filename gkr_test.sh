#!/usr/bin/env bash
set -euo pipefail

# ============================================================================
# Declarative config — single source of truth for the mode → circuits partition
# ============================================================================
PER_FAMILY_CIRCUITS=(
  add_sub_lui_auipc_mop
  jump_branch_slt
  shift_binop
  unsigned_mul_div
  mem_word_only
  mem_subword_only
  inits_and_teardowns
)
DELEGATIONS=(
  blake2_with_extended_control
  bigint_with_extended_control
  keccak_special5
  blake2_g_function
)
# In per_family mode the pipeline exercises the per-family circuits + delegations.
# In unified mode it exercises unified_reduced_machine + the same delegations.
PER_FAMILY_SET=("${PER_FAMILY_CIRCUITS[@]}" "${DELEGATIONS[@]}")
UNIFIED_SET=(unified_reduced_machine "${DELEGATIONS[@]}")

ALL_STEPS=(circuits witness_gen build_program generator prover native corruption binaries transpiler)
OPT_IN_STEPS=(malicious)

# ============================================================================
# Defaults
# ============================================================================
MODE=""                            # set by subcommand
BLAKE="blake2_with_compression"
VARIANT="caches"
ENCODING="coeff"
SECURITY_LEVEL="80"
PROVE_EMPTY=false
SELF_CHECKS=true
CHECK_SATISFIED=false
SELECTED_CIRCUITS=()
FROM=""
SHOW_WARNINGS=false
DRY_RUN=false

# ============================================================================
# Plumbing
# ============================================================================
die() { echo "ERROR: $*" >&2; exit 2; }

usage() {
  cat <<EOF
Usage: $0 <subcommand> [options] [steps...]

Runs the GKR pipeline. Subcommand picks the circuit set + RISC-V program; steps
execute in canonical pipeline order regardless of cmdline order.

Subcommands:
  per_family    Per-family circuits + delegations (program: keccak_f1600 default,
                hashed_fibonacci via GKR_PROGRAM env var)
  unified       Unified-reduced-machine + delegations (program: multi_family_smoke)

Options:
  --blake V             blake2_with_compression (default) | blake2_g_function | special_opcodes_extension
                        Propagated to prover-side program selection via GKR_BLAKE.
  --variant V           caches (default) | no_caches
  --encoding ENC        coeff (default) | eval (WHIR leaf encoding)
                        Forwarded as the eval_leaves feature to prover + generator.
  --security-level L    80 (default) | 100 | both
  --prove-empty         Prove every applicable circuit even if program made 0 calls.
                        Forwarded via GKR_PROVE_EMPTY.
  --no-self-checks      Disable in-prove sumcheck/cache/at-point-eval checks.
                        Drops the gkr_self_checks feature; default ON.
  --check-satisfied     Enable the heavyweight constraint-satisfaction check.
                        Adds gkr_check_satisfied feature; default OFF (slow).
  --circuits A,B,...    Subcommand-aware filter; must be a subset of the
                        subcommand's circuit set. Forwarded via GKR_CIRCUITS.
  --from STEP           Run STEP and everything after it in canonical order.
  --warnings            Show compiler warnings (suppressed by default).
  --dry-run             Print what would run without executing.
  -h, --help            Show this message.

Steps (canonical order):
  circuits        Compile GKR circuits
  witness_gen     Generate witness evaluation functions
  build_program   Rebuild the RISC-V example program the prover reads
  generator       Regenerate inlined verifier
  prover          Generate proof (the slow one)
  native          Run native verifier tests
  corruption      Run corruption tests
  binaries        Build RISC-V binaries
  transpiler      Run transpiler tests (writes flamegraphs)

Extra step (opt-in, runs last when invoked):
  malicious       Soundness-gap tests. Subcommand-aware: per_family runs the
                  malicious_proof generator + verifier malicious.rs; unified
                  re-runs the unified_negative tests.

Examples:
  $0 per_family
  $0 unified
  $0 per_family --from generator
  $0 unified --circuits blake2_with_extended_control --from binaries
  $0 per_family --security-level both --from generator
  $0 unified --dry-run

Exit codes:
  0  success
  1  bad usage (unknown step/subcommand or --help)
  2  invalid argument value or wrong working directory
  3  no bin files for the requested circuit/level combination

Circuits by subcommand:
  per_family: ${PER_FAMILY_SET[*]}
  unified:    ${UNIFIED_SET[*]}
EOF
  exit 1
}

# ============================================================================
# Subcommand parse — sets MODE and MODE_CIRCUITS
# ============================================================================
[[ $# -lt 1 ]] && usage
case "$1" in
  per_family) MODE="per_family"; MODE_CIRCUITS=("${PER_FAMILY_SET[@]}"); shift ;;
  unified)    MODE="unified";    MODE_CIRCUITS=("${UNIFIED_SET[@]}");    shift ;;
  -h|--help)  usage ;;
  *) die "first arg must be 'per_family' or 'unified'. Got: $1 (run with --help)" ;;
esac

[[ -f Cargo.toml && -d tools/gkr_verifier/src/bin ]] \
  || die "must run from airbender repo root (Cargo.toml + tools/gkr_verifier/src/bin not found)"

# ============================================================================
# Option parse
# ============================================================================
while [[ $# -gt 0 ]]; do
  case "$1" in
    -h|--help) usage ;;
    --blake) BLAKE="$2"; shift 2 ;;
    --variant) VARIANT="$2"; shift 2 ;;
    --encoding) ENCODING="$2"; shift 2 ;;
    --security-level) SECURITY_LEVEL="$2"; shift 2 ;;
    --prove-empty) PROVE_EMPTY=true; shift ;;
    --no-self-checks) SELF_CHECKS=false; shift ;;
    --check-satisfied) CHECK_SATISFIED=true; shift ;;
    --circuits) IFS=',' read -ra SELECTED_CIRCUITS <<< "$2"; shift 2 ;;
    --from) FROM="$2"; shift 2 ;;
    --warnings) SHOW_WARNINGS=true; shift ;;
    --dry-run) DRY_RUN=true; shift ;;
    *) break ;;
  esac
done

# ============================================================================
# Validate
# ============================================================================
case "$BLAKE" in
  blake2_with_compression|blake2_g_function|special_opcodes_extension) ;;
  *) die "--blake must be blake2_with_compression, blake2_g_function, or special_opcodes_extension. Got: $BLAKE" ;;
esac

case "$VARIANT" in
  caches|no_caches) ;;
  *) die "--variant must be caches or no_caches. Got: $VARIANT" ;;
esac

case "$SECURITY_LEVEL" in
  80|100|both) ;;
  *) die "--security-level must be 80, 100, or both. Got: $SECURITY_LEVEL" ;;
esac

if [[ ${#SELECTED_CIRCUITS[@]} -gt 0 ]]; then
  for c in "${SELECTED_CIRCUITS[@]}"; do
    found=false
    for allowed in "${MODE_CIRCUITS[@]}"; do
      [[ "$c" = "$allowed" ]] && { found=true; break; }
    done
    $found || die "--circuits $c not valid in $MODE mode. Allowed: ${MODE_CIRCUITS[*]}"
  done
fi

# ============================================================================
# Resolve circuit list, security levels, and the (base × level) CIRCUITS array
# ============================================================================
if [[ ${#SELECTED_CIRCUITS[@]} -gt 0 ]]; then
  BASE_CIRCUITS=("${SELECTED_CIRCUITS[@]}")
else
  BASE_CIRCUITS=("${MODE_CIRCUITS[@]}")
fi

case "$SECURITY_LEVEL" in
  80)   LEVELS=(sec_80) ;;
  100)  LEVELS=(sec_100) ;;
  both) LEVELS=(sec_80 sec_100) ;;
esac

LEVEL_FEATURES_ARR=()
for lvl in "${LEVELS[@]}"; do LEVEL_FEATURES_ARR+=("security_${lvl#sec_}"); done
LEVEL_FEATURES=$(IFS=,; echo "${LEVEL_FEATURES_ARR[*]}")

# Single-level runs get a level test-filter; "both" leaves it empty so cargo
# matches every level's tests via substring.
LEVEL_TEST_FILTER=""
[[ ${#LEVELS[@]} -eq 1 ]] && LEVEL_TEST_FILTER="_${LEVELS[0]}"

# CIRCUITS = (base × level), filtered by which bin files actually exist.
CIRCUITS=()
for base in "${BASE_CIRCUITS[@]}"; do
  for lvl in "${LEVELS[@]}"; do
    [[ -f "tools/gkr_verifier/src/bin/${base}_${lvl}.rs" ]] && CIRCUITS+=("${base}_${lvl}")
  done
done

# ============================================================================
# Resolve steps
# ============================================================================
VALID_STEPS=" ${ALL_STEPS[*]} ${OPT_IN_STEPS[*]} "

is_step_valid() { [[ "$VALID_STEPS" =~ " $1 " ]]; }

if [[ $# -gt 0 ]]; then
  RAW_STEPS=("$@")
  for s in "${RAW_STEPS[@]}"; do
    is_step_valid "$s" || { echo "ERROR: unknown step: $s" >&2; usage; }
  done
  STEPS=()
  for s in "${ALL_STEPS[@]}" "${OPT_IN_STEPS[@]}"; do
    [[ " ${RAW_STEPS[*]} " =~ " $s " ]] && STEPS+=("$s")
  done
elif [[ -n "$FROM" ]]; then
  is_step_valid "$FROM" || { echo "ERROR: unknown step for --from: $FROM" >&2; usage; }
  STEPS=()
  found=false
  for s in "${ALL_STEPS[@]}"; do
    [[ "$s" = "$FROM" ]] && found=true
    $found && STEPS+=("$s")
  done
  # --from on an opt-in step runs only that step.
  [[ ${#STEPS[@]} -eq 0 ]] && STEPS=("$FROM")
else
  STEPS=("${ALL_STEPS[@]}")
fi

# ============================================================================
# Feature flags + cargo test filter assembly
# ============================================================================
FEATURES="${BLAKE},${LEVEL_FEATURES}"
GENERATOR_FEATURES="${LEVEL_FEATURES}"
VARIANT_FEATURES=()
if [[ "$VARIANT" = "no_caches" ]]; then
  FEATURES="${FEATURES},no_caches"
  GENERATOR_FEATURES="${GENERATOR_FEATURES},no_caches"
  VARIANT_FEATURES=(--features no_caches)
fi

# Leaf encoding: `eval_leaves` switches the prover commit and the generated
# verifier to evaluation form. Default (coeff) needs no feature. The verifier
# crate needs nothing extra — the generated code is self-contained. Appended to
# every prover invocation so committed proofs always match the generated verifier.
ENCODING_PROVER_FEATURES=()
case "$ENCODING" in
  coeff) ;;
  eval)
    GENERATOR_FEATURES="${GENERATOR_FEATURES},eval_leaves"
    ENCODING_PROVER_FEATURES=(--features eval_leaves) ;;
  *) die "--encoding must be coeff or eval. Got: $ENCODING" ;;
esac

# Prover-crate additive features. Neither gkr_self_checks nor gkr_check_satisfied
# is in the prover crate's defaults; each is opt-in via --features.
PROVER_CARGO_FEATURE_ARGS=()
PROVER_FEATURES_LIST=()
$SELF_CHECKS && PROVER_FEATURES_LIST+=("gkr_self_checks")
$CHECK_SATISFIED && PROVER_FEATURES_LIST+=("gkr_check_satisfied")
if [[ ${#PROVER_FEATURES_LIST[@]} -gt 0 ]]; then
  PROVER_CARGO_FEATURE_ARGS=(--features "$(IFS=,; echo "${PROVER_FEATURES_LIST[*]}")")
fi

# Generator's #[test] fns are bare base names. Native/transpiler are
# level-suffixed. Corruption uses bare base names (no level suffix on
# corruption test names). cargo test OR's positional filters as substrings; a
# single "foo|bar" arg matches "|" literally, so each circuit needs its own arg.
#
# All four filters derive from BASE_CIRCUITS so the verifier-side test steps
# stay in sync with what the prover step just generated. Without this, running
# `unified` would still execute every per-family verifier test (against stale
# per-family proofs) because cargo's substring filter doesn't know about modes.
GENERATOR_FILTERS=("${BASE_CIRCUITS[@]}")
CORRUPTION_FILTERS=("${BASE_CIRCUITS[@]}")
TEST_FILTERS=()
if [[ -n "$LEVEL_TEST_FILTER" ]]; then
  for c in "${BASE_CIRCUITS[@]}"; do TEST_FILTERS+=("${c}${LEVEL_TEST_FILTER}"); done
else
  TEST_FILTERS=("${BASE_CIRCUITS[@]}")
fi

WARN_FLAGS=""
$SHOW_WARNINGS || WARN_FLAGS="-Awarnings"
DUMP_BIN_WARN_FLAGS=()
$SHOW_WARNINGS && DUMP_BIN_WARN_FLAGS=(--warnings)

# ============================================================================
# Helpers
# ============================================================================
# Run a command in a subshell after cd'ing to dir. Avoids `bash -c` quoting
# layers. Some workspace crates don't compile cleanly from the root, so we cd
# into the target crate and let cargo's auto-detection scope the build.
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

# Prover-side cargo invocations need RUST_MIN_STACK=100M because deep
# sumcheck/folding frames overflow the default 8M. GKR_* env vars cascade to
# the orchestration runtime config (see prover/src/tests/gkr/mod.rs).
run_prover_cargo() {
  local circuits_csv=""
  if [[ ${#SELECTED_CIRCUITS[@]} -gt 0 ]]; then
    circuits_csv=$(IFS=,; echo "${SELECTED_CIRCUITS[*]}")
  fi
  in_dir prover env \
    RUST_MIN_STACK=100000000 \
    RUSTFLAGS="$WARN_FLAGS" \
    GKR_BLAKE="$BLAKE" \
    GKR_PROVE_EMPTY=$([[ "$PROVE_EMPTY" = "true" ]] && echo 1 || echo 0) \
    GKR_CIRCUITS="$circuits_csv" \
    GKR_MODE="$MODE" \
    cargo test -p prover --release "$@"
}

# ============================================================================
# Step functions
# ============================================================================
step_circuits() {
  run_step "Compile GKR circuits" \
    in_dir cs env RUSTFLAGS="$WARN_FLAGS" cargo test -p cs -- gkr
}

step_witness_gen() {
  run_step "Generate witness evaluation functions" \
    in_dir witness_eval_generator env RUSTFLAGS="$WARN_FLAGS" \
      cargo test -p witness_eval_generator -- gen_for_gkr
}

# Each mode reads a different program. Unified loads
# examples/multi_family_smoke/app_blake2_*.bin (variant picked by GKR_BLAKE).
# Per-family defaults to riscv_transpiler/examples/keccak_f1600/app.bin (a
# pre-built artifact — no build step needed). To run per-family with the
# hashed_fibonacci program instead, set GKR_PROGRAM=hashed_fibonacci_g_function
# (or =hashed_fibonacci_compression), which both triggers the build below AND
# propagates to the Rust-side program-selection match in family_circuits.rs.
step_build_program() {
  case "$MODE" in
    unified)
      run_step "Build unified-mode program (multi_family_smoke)" \
        in_dir examples/multi_family_smoke bash dump_bin.sh ;;
    per_family)
      case "${GKR_PROGRAM:-}" in
        hashed_fibonacci_g_function|hashed_fibonacci_compression)
          run_step "Build per-family program (hashed_fibonacci)" \
            in_dir examples/hashed_fibonacci bash build_all.sh ;;
        *)
          echo "[build_program] per_family default is keccak_f1600 (pre-built); skipping build." ;;
      esac ;;
  esac
}

step_generator() {
  run_step "Regenerate verifier (variant=${VARIANT})" \
    env RUSTFLAGS="$WARN_FLAGS" cargo test -p verifier_generator \
      --no-default-features --features "$GENERATOR_FEATURES" \
      --test generate_verifiers \
      -- "${GENERATOR_FILTERS[@]+"${GENERATOR_FILTERS[@]}"}"
}

step_prover() {
  local filter="gkr_run_basic_unrolled_test${LEVEL_TEST_FILTER}"
  [[ "$MODE" = "unified" ]] && filter="gkr_run_unified_test${LEVEL_TEST_FILTER}"
  run_step "Generate proof (mode=${MODE}, self_checks=${SELF_CHECKS}, check_satisfied=${CHECK_SATISFIED})" \
    run_prover_cargo \
      "${PROVER_CARGO_FEATURE_ARGS[@]+"${PROVER_CARGO_FEATURE_ARGS[@]}"}" \
      "${VARIANT_FEATURES[@]+"${VARIANT_FEATURES[@]}"}" \
      "${ENCODING_PROVER_FEATURES[@]+"${ENCODING_PROVER_FEATURES[@]}"}" \
      -- --nocapture "$filter"
}

step_native() {
  run_step "Native tests" \
    env RUSTFLAGS="$WARN_FLAGS" cargo test -p verifier \
      --no-default-features --features "$FEATURES" --test native \
      -- "${TEST_FILTERS[@]+"${TEST_FILTERS[@]}"}"
}

step_corruption() {
  run_step "Corruption tests" \
    env RUSTFLAGS="$WARN_FLAGS" cargo test -p verifier \
      --no-default-features --features "$FEATURES" --test corruption \
      -- "${CORRUPTION_FILTERS[@]+"${CORRUPTION_FILTERS[@]}"}" --include-ignored
}

step_binaries() {
  if [[ ${#CIRCUITS[@]} -eq 0 ]]; then
    echo "ERROR: no bin files found for security-level=${SECURITY_LEVEL}, circuits=${SELECTED_CIRCUITS[*]:-all in $MODE}" >&2
    echo "  expected tools/gkr_verifier/src/bin/<base>_<level>.rs for level(s): ${LEVELS[*]}" >&2
    exit 3
  fi
  run_step "Build RISC-V binaries (blake=${BLAKE}, variant=${VARIANT})" \
    in_dir tools/gkr_verifier ./dump_bin.sh \
      --blake "$BLAKE" --variant "$VARIANT" \
      "${DUMP_BIN_WARN_FLAGS[@]+"${DUMP_BIN_WARN_FLAGS[@]}"}" \
      "${CIRCUITS[@]}"
}

step_transpiler() {
  run_step "Transpiler tests" \
    env RUSTFLAGS="$WARN_FLAGS" cargo test -p verifier \
      --no-default-features --features "$FEATURES" --test transpiler \
      -- "${TEST_FILTERS[@]+"${TEST_FILTERS[@]}"}" --include-ignored
}

# per_family: malicious_proof test (#[ignore]) writes corrupted proofs with
# self_checks OFF; verifier-side malicious.rs then asserts rejection.
# unified: now BOTH layers (symmetric uplift from plans/negative_test_pipeline_rework.md):
#   (1) unified_negative_tests mutate the witness and assert check_satisfied /
#       check_lookups_in_range reject (constraint + range-lookup layer), and
#   (2) generate_malicious_unified_proofs corrupts the witness and PROVES it
#       (self_checks OFF), then verifier-side malicious.rs (rejects_malicious_unified_*)
#       asserts the real verifier rejects (proof layer).
# The inits/teardowns-eval corruption lives in the `corruption` step
# (rejects_corrupted_it_evals_unified_reduced_machine_sec_80).
step_malicious() {
  case "$MODE" in
    per_family)
      run_step "Generate malicious proofs (corrupt witness, no self-checks)" \
        run_prover_cargo \
          --no-default-features --features prover,bincode \
          "${VARIANT_FEATURES[@]+"${VARIANT_FEATURES[@]}"}" \
          "${ENCODING_PROVER_FEATURES[@]+"${ENCODING_PROVER_FEATURES[@]}"}" \
          -- --ignored --nocapture malicious_proof
      run_step "Verify malicious proofs rejected (soundness gap tests)" \
        env RUSTFLAGS="$WARN_FLAGS" cargo test -p verifier \
          --no-default-features --features "$FEATURES" \
          --test malicious -- --include-ignored
      ;;
    unified)
      run_step "Unified negative tests (constraint + range-lookup layer)" \
        run_prover_cargo \
          "${PROVER_CARGO_FEATURE_ARGS[@]+"${PROVER_CARGO_FEATURE_ARGS[@]}"}" \
          "${VARIANT_FEATURES[@]+"${VARIANT_FEATURES[@]}"}" \
          "${ENCODING_PROVER_FEATURES[@]+"${ENCODING_PROVER_FEATURES[@]}"}" \
          -- --nocapture unified_negative
      # Proof layer: corrupt the witness and PROVE it. Default features (no
      # PROVER_CARGO_FEATURE_ARGS) ⇒ no gkr_self_checks (the bad witness reaches
      # the prover) but proptest stays available, unlike per_family's
      # --no-default-features path which unified_negative_tests.rs can't compile under.
      # prove_built_unified_trace skips check_satisfied, so proving succeeds and the
      # verifier is what must reject. GKR_BLAKE (set by run_prover_cargo) selects the
      # matching program variant so the proof lines up with the verifier below.
      run_step "Generate malicious unified proofs (corrupt witness, no self-checks)" \
        run_prover_cargo \
          "${VARIANT_FEATURES[@]+"${VARIANT_FEATURES[@]}"}" \
          "${ENCODING_PROVER_FEATURES[@]+"${ENCODING_PROVER_FEATURES[@]}"}" \
          -- --ignored --nocapture generate_malicious_unified_proofs
      run_step "Verify malicious unified proofs rejected (soundness gap tests)" \
        env RUSTFLAGS="$WARN_FLAGS" cargo test -p verifier \
          --no-default-features --features "$FEATURES" \
          --test malicious -- --include-ignored rejects_malicious_unified
      ;;
  esac
}

# ============================================================================
# Main loop
# ============================================================================
for step in "${STEPS[@]}"; do
  case "$step" in
    circuits)       step_circuits ;;
    witness_gen)    step_witness_gen ;;
    build_program)  step_build_program ;;
    generator)      step_generator ;;
    prover)         step_prover ;;
    native)         step_native ;;
    corruption)     step_corruption ;;
    binaries)       step_binaries ;;
    transpiler)     step_transpiler ;;
    malicious)      step_malicious ;;
  esac
done

echo ""
echo "==> Done!"
