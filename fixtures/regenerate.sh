#!/usr/bin/env bash
set -euo pipefail

check=0
mode_filter=
stage_filter=
while (($#)); do
  case $1 in
    --check) check=1; shift ;;
    --mode|--stage)
      (($# >= 2)) || { echo "$1 needs a value" >&2; exit 1; }
      if [[ $1 == --mode ]]; then mode_filter=$2; else stage_filter=$2; fi
      shift 2 ;;
    *) echo "unknown argument: $1" >&2; exit 1 ;;
  esac
done
case $mode_filter in
  ''|pessimistic_conjecture|ethproofs_soundcalc) ;;
  *) echo "unknown mode: $mode_filter" >&2; exit 1 ;;
esac
case $stage_filter in
  ''|circuits|base_unified|unrolled|compression|l1) ;;
  *) echo "unknown stage: $stage_filter" >&2; exit 1 ;;
esac
case $stage_filter in
  compression|l1)
    [[ $mode_filter != ethproofs_soundcalc ]] || {
      echo "L1 stages support only pessimistic_conjecture" >&2; exit 1;
    }
    mode_filter=pessimistic_conjecture ;;
esac
backend=${FIXTURE_BACKEND:-cpu}
case $backend in
  cpu|gpu) ;;
  *) echo "unknown FIXTURE_BACKEND: $backend" >&2; exit 1 ;;
esac
if [[ $backend == gpu && ( -z $stage_filter || $stage_filter == circuits ) ]]; then
  echo "FIXTURE_BACKEND=gpu does not support the circuits stage; use the canonical GPU matrix" >&2
  exit 1
fi
if (( !check )) && [[ $stage_filter == base_unified || $stage_filter == unrolled ]]; then
  echo "selecting a chain stage is --check-only; write mode regenerates the whole chain" >&2
  exit 1
fi

script_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
repo=$(cd "${AB_TEST_ARTIFACT_ROOT:-$script_root}" && pwd)
export AB_TEST_ARTIFACT_ROOT=$repo
export FSV_DIR="$repo/tools/gkr_verifier/full_statement_verifiers"
export RUST_MIN_STACK=${RUST_MIN_STACK:-16777216}
cd "$repo"

out_repo=$repo
temporary=
if ((check)); then
  temporary=$(mktemp -d)
  out_repo=$temporary
fi
producer_log=
trusted_params=${FIXTURE_TRUSTED_PARAMS:-}
[[ -z $trusted_params ]] || mkdir -p "$trusted_params"
cleanup() {
  local result=$?
  if [[ -n $temporary ]]; then
    if ((result)); then
      echo "Fixture check outputs retained at $temporary" >&2
    else
      rm -rf "$temporary"
    fi
  fi
  if ((result)) && [[ -n $producer_log && -f $producer_log ]]; then
    echo "Producer log retained at $producer_log" >&2
  fi
}
trap cleanup EXIT

producer=${FIXTURE_CANONICAL_PRODUCER:-}
cli=${FIXTURE_CLI:-}
codec=${FIXTURE_CODEC:-}
if [[ -z $stage_filter || $stage_filter == circuits ]]; then
  if [[ -n $producer ]]; then
    [[ -x $producer ]]
    producer_command=("$producer")
  else
    producer_command=(cargo test -p prover --lib --features test --profile cli --)
  fi
fi
if [[ $stage_filter != circuits ]]; then
  if [[ -z $cli ]]; then
    if [[ $backend == gpu ]]; then
      cargo build --release -p cli --features gpu
    else
      cargo build --release -p cli
    fi
    cli="$repo/target/release/cli"
  fi
  if [[ -z $codec ]]; then
    cargo build --release -p proof_fixtures --bin fixture-codec
    codec="$repo/target/release/fixture-codec"
  fi
  [[ -x $cli && -x $codec ]]
fi

compare_file() {
  if ((check)); then
    cmp "$1" "$repo/${1#"$out_repo/"}"
  fi
}
check_artifact() {
  local name=$1
  local file="$chain_out/$name.json.zlib"
  "$codec" check "$file"
  local trusted=()
  # The cache includes compression records; L1 wrap verification stays external.
  if [[ -n $trusted_params && $name != l1 ]]; then
    local params="$trusted_params/$cli_mode-trusted-params.json"
    local params_target=recursion-unified
    [[ $mode != pessimistic_conjecture ]] || params_target=compression
    [[ -f $params ]] || "$cli" trusted-params --bin "$bin" --soundness-mode "$cli_mode" --target "$params_target" --backend cpu --output "$params"
    trusted=(--trusted-params "$params")
  fi
  "$cli" verify --proof "$file" --bin "$bin" --soundness-mode "$cli_mode" "${trusted[@]}"
  compare_file "$file"
}

modes=(pessimistic_conjecture ethproofs_soundcalc)
[[ -z $mode_filter ]] || modes=("$mode_filter")
for mode in "${modes[@]}"; do
  cli_mode=${mode//_/-}
  bin="$repo/examples/basic_fibonacci/app.bin"
  chain_out="$out_repo/fixtures/chains/$mode"
  chain_parent="$repo/fixtures/chains/$mode"
  common=(--bin "$bin" --backend "$backend" --soundness-mode "$cli_mode" --output-dir "$chain_out")
  stages=(circuits base_unified unrolled)
  [[ $mode != pessimistic_conjecture ]] || stages+=(compression l1)
  [[ -z $stage_filter ]] || stages=("$stage_filter")
  for stage in "${stages[@]}"; do
    echo "== $mode / $stage"
    case $stage in
      circuits)
        if ((check)); then
          producer_log="$temporary/producer-$mode.log"
        else
          producer_log=$(mktemp)
        fi
        PROOF_FIXTURES_OUTPUT_ROOT="$out_repo" "${producer_command[@]}" \
          --exact "tests::gkr::canonical_proofs::regenerate_canonical_circuit_proofs_$mode" \
          --nocapture --test-threads=1 | tee "$producer_log"
        grep -q 'test result: ok. 1 passed; 0 failed' "$producer_log"
        if ((!check)); then
          rm -f "$producer_log"
          producer_log=
        fi
        for file in "$out_repo/fixtures/circuits/$mode/"*.json.zlib; do
          compare_file "$file"
        done ;;
      base_unified)
        "$cli" prove "${common[@]}" --target base --output-file base.json.zlib
        check_artifact base
        RECURSION_UNROLLED_LAYERS=0 "$cli" continue-proof "${common[@]}" \
          --proof "$chain_parent/base.json.zlib" --target recursion-unified --output-file unified.json.zlib
        check_artifact unified
        if ((check)) && [[ $backend == cpu ]]; then
          FIXTURE_CHAIN_ROOT="$repo/fixtures/chains" FIXTURE_CODEC="$codec" \
            SOUNDNESS_MODE="$cli_mode" SMOKE_OUTPUT_DIR="$out_repo/smoke/$mode" \
            "$repo/.github/scripts/soundness_mode_smoke.sh" "$cli" "$bin" "$backend"
        fi ;;
      unrolled)
        RECURSION_UNROLLED_LAYERS=1 "$cli" continue-proof "${common[@]}" \
          --proof "$chain_parent/base.json.zlib" --target recursion-unrolled --output-file unrolled.json.zlib
        check_artifact unrolled
        RECURSION_UNROLLED_LAYERS=0 "$cli" continue-proof "${common[@]}" \
          --proof "$chain_parent/unrolled.json.zlib" --target recursion-unified --output-file unrolled_unified.json.zlib
        check_artifact unrolled_unified ;;
      compression)
        "$cli" continue-proof "${common[@]}" \
          --proof "$chain_parent/unified.json.zlib" --target compression --output-file compression.json.zlib
        check_artifact compression ;;
      l1)
        "$cli" continue-proof "${common[@]}" \
          --proof "$chain_parent/compression.json.zlib" --target l1 --output-file l1.json.zlib
        check_artifact l1 ;;
    esac
  done
done
