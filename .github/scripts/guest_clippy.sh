#!/usr/bin/env bash
# Clippy, with warnings denied, over every guest workspace in each feature set it builds with,
# then over the root-workspace crates those guests depend on, cross-compiled for the guest target
# with the features and target features each guest build uses. Clippy lints only the members of
# the workspace it runs in, so the guest runs compile those crates without linting them.
#
# tools/gkr_verifier: every Blake mode (they are mutually exclusive), once with caches and once
# with no_caches and modular_fma. tools/gkr_verifier_l1_wrap: its only configuration.
# examples/*: no features, then each feature alone (the examples' features are Blake modes).
# The verifier guests build like dump_bin.sh: RUSTC_BOOTSTRAP=1 unlocks the unstable options on
# their pinned stable toolchain, and RUSTFLAGS stays unset so .cargo/config.toml applies.
set -euo pipefail
cd "$(dirname "$0")/../.."
root=$PWD
target=riscv32i-unknown-none-elf
declare -A dependency_runs=()

guest() {
    local dir=$1
    shift
    local cargo=(cargo) locked=() unstable=()
    case $dir in
    tools/*) cargo=(env RUSTC_BOOTSTRAP=1 cargo) locked=(--locked) unstable=(-Z panic-immediate-abort -Z build-std=core,alloc) ;;
    # Some examples keep their lockfile out of the repository.
    *) if git ls-files --error-unmatch "$dir/Cargo.lock" > /dev/null 2>&1; then locked=(--locked); fi ;;
    esac
    echo "==> $dir $*"
    (cd "$dir" && "${cargo[@]}" clippy "${locked[@]}" --release "${unstable[@]}" --bins "$@" -- -D warnings)
    local run
    run=$(cd "$dir" && "${cargo[@]}" metadata "${locked[@]}" --format-version 1 --filter-platform "$target" "$@" |
        python3 "$root/.github/scripts/guest_dependencies.py" "$root" "$root/$dir/.cargo/config.toml")
    dependency_runs[$run]=1
}

for blake in blake2_with_compression blake2_g_function mop_extension special_opcodes_extension; do
    for extra in "" ",no_caches,modular_fma"; do
        guest tools/gkr_verifier --no-default-features --features "${blake}${extra}"
    done
done
guest tools/gkr_verifier_l1_wrap

for manifest in examples/*/Cargo.toml; do
    dir=$(dirname "$manifest")
    features=$(cargo metadata --no-deps --format-version 1 --manifest-path "$manifest" |
        python3 -c 'import json, sys; print(" ".join(f for f in json.load(sys.stdin)["packages"][0]["features"] if f != "default"))')
    guest "$dir"
    for feature in $features; do
        guest "$dir" --features "$feature"
    done
done

for run in "${!dependency_runs[@]}"; do
    read -r target_features packages <<< "$run"
    echo "==> root-workspace guest dependencies ($target_features): $packages"
    # shellcheck disable=SC2086
    RUSTFLAGS="-C target-feature=$target_features" cargo clippy --target "$target" -Z build-std=core,alloc \
        --lib --no-default-features $packages -- -D warnings
done
