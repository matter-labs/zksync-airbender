#!/usr/bin/env bash
# Optional experiment. The official kernel validation gate remains required.
set -euo pipefail

project_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_dir"
tool_revision=2896cfd092758b8d0fc9977502dc036b0ab79921
tool_root="$project_dir/.lake/turbo-lean"
tool_source="$tool_root/source"
tool_binary="$tool_root/target/release/turbo-lean"
export ELAN_TOOLCHAIN
ELAN_TOOLCHAIN="$(cat lean-toolchain)"
[[ "$ELAN_TOOLCHAIN" == leanprover/lean4:v4.35.0 ]]
toolchain_root="$(elan run "$ELAN_TOOLCHAIN" lean --print-prefix)"
export PATH="$toolchain_root/bin:$PATH"
export TURBO_LEAN_BIN="$toolchain_root/bin/lean"
export TURBO_LEAN_HOME="$tool_root/cache"
export TURBO_LEAN_TELEMETRY=off
export CARGO_TARGET_DIR="$tool_root/target"
export CARGO_BUILD_JOBS=1 LEAN_NUM_THREADS=1
unset TURBO_LEAN_ALLOWED_AXIOMS TURBO_LEAN_ALLOWED_AXIOMS_FROM_CONFIG

if [[ "${1:-}" == install ]]; then
  mkdir -p "$tool_root"
  if [[ ! -d "$tool_source/.git" ]]; then
    git clone --filter=blob:none --no-checkout https://github.com/Th0rgal/turbo-lean.git "$tool_source"
    git -C "$tool_source" checkout --detach "$tool_revision"
  fi
  [[ "$(git -C "$tool_source" rev-parse HEAD)" == "$tool_revision" ]]
  git -C "$tool_source" diff --quiet HEAD --
  cd "$tool_source"
  cargo check --locked -p turbo-lean
  cargo build --locked --release -p turbo-lean
  exit
fi

if [[ ! -x "$tool_binary" ]]; then
  echo 'Run scripts/turbo_lean.sh install under the verification resource guard first.' >&2
  exit 2
fi
[[ "$(git -C "$tool_source" rev-parse HEAD)" == "$tool_revision" ]]
git -C "$tool_source" diff --quiet HEAD --
exec "$tool_binary" --cache-dir "$TURBO_LEAN_HOME" --no-auto-worktree-link \
  --no-daemon --no-telemetry --max-memory-mb 2560 "$@"
