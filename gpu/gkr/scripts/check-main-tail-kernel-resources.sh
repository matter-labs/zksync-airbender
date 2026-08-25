#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 || "$1" != "--release" ]]; then
  echo "usage: $0 --release" >&2
  exit 2
fi

script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo_root=$(cd -- "$script_dir/../../.." && pwd)
build_log="$repo_root/target/main-tail-build-diag.log"
symbol=ab_gkr_bwd_main_tail_kernel

if [[ ! -f "$build_log" ]]; then
  echo "missing captured diagnostic build log: $build_log" >&2
  exit 1
fi

mapfile -t link_dirs < <(
  sed -nE \
    's@.*cargo:rustc-link-search=native=([^[:space:]]*/release/build/gpu_gkr/[^[:space:]]*/out).*@\1@p' \
    "$build_log" | sort -u
)
if [[ ${#link_dirs[@]} -ne 1 ]]; then
  echo "expected one current gpu_gkr link-search directory in $build_log, found ${#link_dirs[@]}" >&2
  printf '%s\n' "${link_dirs[@]}" >&2
  exit 1
fi

archive="${link_dirs[0]}/libgpu_gkr_native.a"
if [[ ! -f "$archive" ]]; then
  echo "captured current-build archive does not exist: $archive" >&2
  exit 1
fi

resource_dump=$(mktemp)
symbol_dump=$(mktemp)
trap 'rm -f -- "$resource_dump" "$symbol_dump"' EXIT
cuobjdump --dump-resource-usage "$archive" >"$resource_dump"
cuobjdump --dump-elf-symbols "$archive" >"$symbol_dump"

symbol_count=$(awk -v symbol="$symbol" '
  /^member .*:cmake_device_link\.o:$/ { linked = 1; next }
  /^member / { linked = 0 }
  linked && $1 == "STT_FUNC" && $2 == "STB_GLOBAL" && $3 == "STO_ENTRY" && $4 == symbol { ++count }
  END { print count + 0 }
' "$symbol_dump")
if [[ "$symbol_count" -ne 1 ]]; then
  echo "expected exactly one $symbol entry in cmake_device_link.o, found $symbol_count" >&2
  exit 1
fi

linked_resource_dump=$(awk '
  /^member .*:cmake_device_link\.o:$/ { linked = 1; next }
  /^member / { linked = 0 }
  linked { print }
' "$resource_dump")
record_count=$(grep -Ec "Function[[:space:]]*${symbol}:$" <<<"$linked_resource_dump" || true)
if [[ "$record_count" -ne 1 ]]; then
  echo "expected exactly one linked resource record for $symbol, found $record_count" >&2
  exit 1
fi

resource_record=$(awk -v symbol="$symbol" '
  $0 ~ "Function[[:space:]]*" symbol ":$" { emit = 1 }
  emit && $0 ~ /Function[[:space:]]*/ && $0 !~ symbol && lines > 0 { exit }
  emit { print; ++lines }
' <<<"$linked_resource_dump")
if ! grep -Eq 'STACK:[[:space:]]*0([,[:space:]]|$)' <<<"$resource_record"; then
  echo "$symbol has nonzero or unreported stack storage" >&2
  printf '%s\n' "$resource_record" >&2
  exit 1
fi
if ! grep -Eq 'LOCAL:[[:space:]]*0([,[:space:]]|$)' <<<"$resource_record"; then
  echo "$symbol has nonzero or unreported local storage" >&2
  printf '%s\n' "$resource_record" >&2
  exit 1
fi

ptxas_block=$(awk -v symbol="$symbol" '
  index($0, "Compiling entry function") && index($0, symbol) { emit = 1; ++records }
  emit { print }
  emit && /Used [0-9]+ registers/ { emit = 0 }
  END { if (records != 1) exit 7 }
' "$build_log") || {
  echo "expected exactly one ptxas diagnostic block for $symbol" >&2
  exit 1
}
if ! grep -Eq '0 bytes spill stores' <<<"$ptxas_block"; then
  echo "$symbol reports spill stores" >&2
  printf '%s\n' "$ptxas_block" >&2
  exit 1
fi
if ! grep -Eq '0 bytes spill loads' <<<"$ptxas_block"; then
  echo "$symbol reports spill loads" >&2
  printf '%s\n' "$ptxas_block" >&2
  exit 1
fi

printf 'archive: %s\n' "$archive"
printf 'symbol-count: %s\n' "$symbol_count"
printf '%s\n' "$ptxas_block"
printf '%s\n' "$resource_record"
