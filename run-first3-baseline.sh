#!/usr/bin/env bash
set -euo pipefail
cd /home/rr/code/zksync-airbender/zksync-airbender-worktrees/av-gkr-first3-timing
out=target/gkr-first3-baseline-v2
mkdir -p $out
export GPU_LOCK_OWNER=gkr-first3-baseline
export GKR_BWD_FIRST3_TIMING_OUT=$PWD/$out/first3-rows.jsonl
export RUST_LOG=debug
rm -f $out/first3-rows.jsonl
{
  echo "commit=$(git rev-parse HEAD)"
  echo "cli_sha256=$(sha256sum target/release/cli | cut -d' ' -f1)"
  nvidia-smi --query-gpu=uuid,name,driver_version,persistence_mode,clocks.gr,clocks.mem --format=csv,noheader
} > $out/bindings.txt
start=$(date +%s)
/home/rr/code/zksync-airbender/orange/.agents/bin/with_gpu_lock.sh \
  target/release/cli prove \
    --bin riscv_transpiler/examples/zksync_os/app.bin \
    --text riscv_transpiler/examples/zksync_os/app.text \
    --input-file riscv_transpiler/examples/zksync_os/23620012_witness \
    --backend gpu \
    --target recursion-unified \
    --output-dir $out/output \
  > $out/prove.debug.log 2>&1
echo "wall_seconds=$(( $(date +%s) - start ))" >> $out/bindings.txt
wc -l $out/first3-rows.jsonl >> $out/bindings.txt
echo FIRST3_DONE
