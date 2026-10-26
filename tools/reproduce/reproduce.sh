#!/bin/sh
# Rebuild every committed verifier guest binary with the native toolchain.
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
cd "$(dirname "$0")/../gkr_verifier"

# Full-statement verifiers in every blake variant the recursion pipeline can select.
./dump_recursive_verifiers.sh

# Standalone per-circuit verifiers (both soundness modes; the pessimistic-conjecture set is the
# one the cost-model drift guard consumes): every binary under src/bin/circuit_verifiers/.
PER_CIRCUIT=""
for m in src/bin/circuit_verifiers/*/; do
    m=$(basename "$m")
    PER_CIRCUIT="$PER_CIRCUIT $(ls "src/bin/circuit_verifiers/$m"/*.rs | sed "s|.*/||;s|\.rs||;s|\$|_$m|")"
done
# shellcheck disable=SC2086
./dump_bin.sh --sec 100 $PER_CIRCUIT

echo "==> checksums"
for f in full_statement_verifiers/*.elf circuit_verifiers/*/*.elf; do
    [ -f "$f" ] && shasum -a 256 "$f"
done | sort -k2 -u
