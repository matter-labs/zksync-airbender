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
# .bin / .text / .elf files; compare with `git status` / `git diff --stat` afterwards.
set -eu
cd "$(dirname "$0")/../gkr_verifier"

# Full-statement verifiers in every blake variant the recursion pipeline can select.
./dump_recursive_verifiers.sh

# Standalone circuit verifiers consumed by the cost-model drift guard. Keep this list in
# sync with the generated Rust code.
./dump_bin.sh --sec 100 \
    add_sub_lui_auipc_mop_sec_100 jump_branch_slt_sec_100 shift_binop_sec_100 \
    unsigned_mul_div_sec_100 mem_word_only_sec_100 mem_subword_only_sec_100 \
    inits_and_teardowns_sec_100 blake2_with_extended_control_sec_100 \
    bigint_with_extended_control_sec_100 keccak_special5_sec_100 keccak_column_parity_sec_100 \
    keccak_theta_rho_sec_100 keccak_chi5_sec_100 blake2_g_function_sec_100 \
    blake2_with_extended_control_sec_100_pack4

echo "==> checksums"
for f in fsv_*_sec_100_*.bin fsv_*_sec_100_*.elf fsv_*_sec_100_*.text *_sec_100.bin *_sec_100.elf *_sec_100.text *_sec_100_pack4.bin *_sec_100_pack4.elf *_sec_100_pack4.text; do
    [ -f "$f" ] && shasum -a 256 "$f"
done | sort -k2 -u
