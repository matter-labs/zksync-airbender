#!/usr/bin/env bash
# Require a clean compiler path, loader cache and device namespace.
set -euo pipefail
fail() { echo "Not CUDA-free: $*" >&2; exit 1; }
command -v sh >/dev/null
if command -v nvcc >/dev/null 2>&1; then
    fail "nvcc is on PATH"
fi
cache="$(ldconfig -p)"
# Match SONAME prefixes: substring matching also catches ICU's libicudata.
cuda_libs="$(printf '%s\n' "$cache" | awk '
    NR > 1 && $1 ~ /^lib(cuda|cudart|nvrtc|nvJitLink|cublas|cufft|curand|cusolver|cusparse|cupti|nvidia)/ { print $1 }
')"
test -z "$cuda_libs" || fail "CUDA libraries in loader cache: $cuda_libs"
[[ -r /dev && -x /dev ]]
shopt -s nullglob
devices=(/dev/nvidia* /dev/dri/render*)
test "${#devices[@]}" -eq 0 || fail "device nodes: ${devices[*]}"
echo "environment is CUDA-free"
