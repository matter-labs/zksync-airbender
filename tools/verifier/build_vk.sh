#!/bin/bash

# Regenerates the verification keys from the verifier binaries.
#
# Same failure-swallowing problem as build.sh: these ran with `&` and a bare `wait`, so
# when the CLI failed to build every invocation below printed "No such file or directory"
# and the script still exited 0, leaving the previous keys in place while the binaries
# next to them had changed. Failures now abort the run.
set -euo pipefail

# Concurrency limit for key generation. Defaults to AIRBENDER_BUILD_JOBS, but can be set
# separately: generate-vk is far more memory-hungry than a rustc invocation, so a machine
# that comfortably compiles three binaries at once can still be OOM-killed running three
# key generations. 0 (default, and CI) runs them all at once.
JOBS="${AIRBENDER_VK_JOBS:-${AIRBENDER_BUILD_JOBS:-0}}"

CLI=target/vk_cli/release/cli

(cd ../cli && CARGO_TARGET_DIR=../verifier/target/vk_cli cargo build --release --no-default-features)

if [ ! -x "$CLI" ]; then
  echo "ERROR: $CLI was not produced; cannot regenerate verification keys" >&2
  exit 1
fi

pids=()

reap() {
  local p rc=0
  # Guard on length rather than using "${pids[@]:-}": on an empty array that fallback
  # expands to a single empty string, and `wait ""` then fails, reporting a failure that
  # did not happen. With a job limit that divides the number of builds, the final reap
  # always sees an empty array.
  if [ "${#pids[@]}" -gt 0 ]; then
    for p in "${pids[@]}"; do
      wait "$p" || rc=1
    done
  fi
  pids=()
  if [ "$rc" -ne 0 ]; then
    echo "ERROR: a verification key failed to generate" >&2
    exit 1
  fi
}

launch() {
  "$@" &
  pids+=("$!")
  if [ "$JOBS" -gt 0 ] && [ "${#pids[@]}" -ge "$JOBS" ]; then
    reap
  fi
}

launch "$CLI" generate-vk --bin ../verifier/universal.bin --machine reduced --output ../verifier/universal.reduced.vk.json
launch "$CLI" generate-vk --bin ../verifier/universal.bin --machine reduced-log23 --output ../verifier/universal.reduced_log23.vk.json
launch "$CLI" generate-vk --bin ../verifier/universal_no_delegation.bin --machine reduced-final --output ../verifier/universal_no_delegation.final.vk.json

launch "$CLI" generate-vk --bin ../verifier/base_layer.bin --machine reduced --output ../verifier/base_layer.reduced.vk.json
launch "$CLI" generate-vk --bin ../verifier/recursion_layer.bin --machine reduced --output ../verifier/recursion_layer.reduced.vk.json
launch "$CLI" generate-vk --bin ../verifier/recursion_layer.bin --machine reduced-log23 --output ../verifier/recursion_log_23_layer.reduced.vk.json
launch "$CLI" generate-vk --bin ../verifier/recursion_layer_no_delegation.bin --machine reduced-final --output ../verifier/recursion_layer_no_delegation.final.vk.json
launch "$CLI" generate-vk --bin ../verifier/final_recursion_layer.bin --machine reduced-final --output ../verifier/final_recursion_layer.final.vk.json

reap
