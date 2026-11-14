#!/bin/sh
# Regenerate the verifier guest sources (both soundness modes) and rebuild every
# committed verifier guest binary with the native toolchain.
# Run from any directory; no Docker, no emulation.
#
# Reproducibility comes from the guest build setup itself (tools/gkr_verifier):
#   - rust-toolchain.toml pins rustc/LLVM/LLD (the same dist build on every host);
#   - rustc_wrapper.sh pins cargo's `-C metadata`, so symbol names, and with them the
#     function/constant placement and the ROM bytes, do not depend on the checkout path
#     or host triple;
#   - dump_bin.sh remaps the checkout root, sysroot and cargo registry in DWARF and drops
#     the toolchain's `.comment` strings from the .elf files.
# The same commit built on x86-64 Linux, x86-64 macOS and arm64 macOS gives byte-identical
# .elf files; compare with `git status` / `git diff --stat` afterwards.
set -eu
REPO_ROOT="$(cd "$(dirname "$0")/../.." && pwd -P)"
GENERATE_SOURCES=1
GENERATE_VERIFIERS=1
FULL_STATEMENT_VERIFIERS=1
CIRCUIT_VERIFIERS=1
while [ $# -gt 0 ]; do
    case "$1" in
        --skip-generate-verifiers) GENERATE_VERIFIERS=0; shift ;;
        --skip-circuit-verifiers) CIRCUIT_VERIFIERS=0; shift ;;
        --only-circuit-verifiers) GENERATE_SOURCES=0; FULL_STATEMENT_VERIFIERS=0; shift ;;
        *) echo "unknown argument: $1" >&2; exit 1 ;;
    esac
done

# The guest sources are generated: regenerate them first, for BOTH soundness modes
# (pessimistic_conjecture and ethproofs_soundcalc), so the binaries below are built from
# the current circuits, configs and generator.
#
# 1. The delegation circuits' setup parameters (setup caps committed with each mode's
#    config): circuit_defs/setups/generated/delegation_parameters_<mode>.rs, included by
#    full_statement_verifier::delegation_circuits_setups::<mode>.
# 2. Every circuit's verifier in each mode: verifier/src/generated/<circuit>/<mode>/, plus
#    the shared verifier/src/generated/common/ module. These are what the per-circuit
#    verifiers and (through full_statement_verifier::imports::<mode>) the full-statement
#    verifiers compile.
# Both run from the workspace (its own toolchain); the generators skip themselves under
# CI=1, so make sure it is unset here.
cd "$REPO_ROOT"
unset CI
if [ "$GENERATE_SOURCES" = 1 ]; then
    echo "==> regenerating the delegation parameters (both soundness modes)"
    cargo test --release -p setups generate_delegation_circuits_artifacts
    if [ "$GENERATE_VERIFIERS" = 1 ]; then
        echo "==> regenerating the circuit verifiers (both soundness modes)"
        cargo test --release -p verifier_generator --test generate_verifiers
    fi
fi

cd "$REPO_ROOT/tools/gkr_verifier"

# Full-statement verifiers in both soundness modes and every recursive Blake variant.
if [ "$FULL_STATEMENT_VERIFIERS" = 1 ]; then
    # Build the independent 512 KiB-ROM L1 wrap guest before the recursive producer.
    bash ../gkr_verifier_l1_wrap/dump_bin.sh
    ./dump_recursive_verifiers.sh
fi

# Standalone per-circuit verifiers (both soundness modes): every binary under src/bin/circuit_verifiers/.
if [ "$CIRCUIT_VERIFIERS" = 1 ]; then
    PER_CIRCUIT=""
    for m in src/bin/circuit_verifiers/*/; do
        m=$(basename "$m")
        PER_CIRCUIT="$PER_CIRCUIT $(ls "src/bin/circuit_verifiers/$m"/*.rs | sed "s|.*/||;s|\.rs||;s|\$|_$m|")"
    done
    # shellcheck disable=SC2086
    ./dump_bin.sh --sec 100 $PER_CIRCUIT
fi

echo "==> checksums"
for f in full_statement_verifiers/*.elf full_statement_verifiers/*/*.elf circuit_verifiers/*/*.elf; do
    [ -f "$f" ] && shasum -a 256 "$f"
done | sort -k2 -u
