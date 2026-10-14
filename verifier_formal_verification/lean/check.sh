#!/usr/bin/env bash
# Build Lean modules under the project's hard limits: 60 s wall clock, 4 GB RAM (cgroup), report time and peak RSS.
# usage: ./check.sh Slop.RV.Mem [more modules]
cd "$(dirname "$0")"
../sail/fetch-lean-sail.sh
exec systemd-run --user --scope -q -p MemoryMax=4G -p MemorySwapMax=0 \
  /usr/bin/time -f "time %es  peak %MKB" timeout 60 lake build "$@"
