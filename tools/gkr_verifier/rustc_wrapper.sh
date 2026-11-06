#!/bin/sh
# cargo `build.rustc-wrapper` for the guest builds: pin `-C metadata` for riscv32 units.
#
# cargo derives `-C metadata` (which rustc turns into the StableCrateId that is baked into
# every mangled symbol name) from the absolute path of the out-of-workspace path
# dependencies (`../../*`) and, through build-script and proc-macro units, from the host
# triple. rustc and LLVM order items by symbol name, and that order decides where each
# function and anonymous constant lands in the image, so the ROM bytes differed between
# hosts and checkout paths (same code, different placement).
# Replacing the hash with a value built only from the crate's identity makes the guest
# binaries reproducible with the native toolchain on any host.
#
# Host units (build scripts, proc-macros, anything without --target riscv32i...) and
# cargo's `rustc -vV` / `--print` probes pass through untouched.
set -eu
rustc="$1"; shift
is_guest=0; has_meta=0
for a in "$@"; do
    case "$a" in
        riscv32i-unknown-none-elf|--target=riscv32i-unknown-none-elf) is_guest=1 ;;
        metadata=*) has_meta=1 ;;
    esac
done
if [ "$is_guest" -eq 0 ] || [ "$has_meta" -eq 0 ]; then
    exec "$rustc" "$@"
fi
features=""; crate_type=""; prev=""
for a in "$@"; do
    case "$prev" in
        --cfg) case "$a" in feature=*) features="${features}${a#feature=},";; esac ;;
        --crate-type) crate_type="$a" ;;
    esac
    prev="$a"
done
features=$(printf '%s' "$features" | tr -d '"')
# basename of the manifest dir keeps registry crates (`serde-1.0.219`) and same-named
# packages apart without depending on where the checkout, registry or sysroot lives.
pkg_dir=$(basename "${CARGO_MANIFEST_DIR:-.}")
new="airbender-guest:${CARGO_PKG_NAME:-?}:${CARGO_PKG_VERSION:-?}:${pkg_dir}:${CARGO_CRATE_NAME:-?}:${crate_type}:${features}"
for a in "$@"; do
    shift
    case "$a" in
        metadata=*) set -- "$@" "metadata=$new" ;;
        *) set -- "$@" "$a" ;;
    esac
done
exec "$rustc" "$@"
