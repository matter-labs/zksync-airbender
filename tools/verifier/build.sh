#!/bin/bash

# Builds the verifier binaries, then regenerates the verification keys.
#
# Every build below used to run with `&` and a bare `wait`, whose exit status ignores
# the background jobs. A failed build therefore left its .bin missing (they are deleted
# at the start of this script) and the run continued: `build_vk.sh` then produced no
# keys, yet the script -- and the Docker RUN step wrapping it -- still reported success.
# That is how partially-built verifier artifacts could reach a commit. Failures are now
# checked and abort the run.
set -euo pipefail

# Concurrency limit. 0 (the default, and what CI uses) launches every build at once.
# Each job is a full rustc, several with -Z build-std, so twelve at once needs a lot of
# memory; on a smaller machine set e.g. AIRBENDER_BUILD_JOBS=3 to bound it. Builds are
# independent -- each has its own CARGO_TARGET_DIR -- so this only affects wall time.
JOBS="${AIRBENDER_BUILD_JOBS:-0}"

pids=()

# Waits for every launched job, failing the script if any of them failed.
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
    echo "ERROR: a verifier build failed; not continuing to the verification keys" >&2
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

# -f: these may legitimately be absent on a clean tree, and `set -e` would abort.
rm -f base_layer.bin
rm -f recursion_layer.bin
rm -f final_recursion_layer.bin
rm -f base_layer_with_output.bin
rm -f recursion_layer_with_output.bin
rm -f final_recursion_layer_with_output.bin
rm -f universal.bin
rm -f universal_no_delegation.bin
rm -f verifier_test.bin

launch env CARGO_TARGET_DIR=target/one cargo objcopy --release -Z build-std=core,panic_abort,alloc -Z build-std-features=panic_immediate_abort --features base_layer --no-default-features -- -O binary base_layer.bin

launch env CARGO_TARGET_DIR=target/two cargo objcopy --release -Z build-std=core,panic_abort,alloc -Z build-std-features=panic_immediate_abort --features recursion_step --no-default-features -- -O binary recursion_layer.bin

launch env CARGO_TARGET_DIR=target/three cargo objcopy --release -Z build-std=core,panic_abort,alloc -Z build-std-features=panic_immediate_abort --features recursion_log_23_step --no-default-features -- -O binary recursion_log_23_layer.bin

launch env CARGO_TARGET_DIR=target/four cargo objcopy --release -Z build-std=core,panic_abort,alloc -Z build-std-features=panic_immediate_abort --features recursion_step_no_delegation --no-default-features -- -O binary recursion_layer_no_delegation.bin

launch env CARGO_TARGET_DIR=target/five cargo objcopy --release -Z build-std=core,panic_abort,alloc -Z build-std-features=panic_immediate_abort --features final_recursion_step --no-default-features -- -O binary final_recursion_layer.bin

launch env CARGO_TARGET_DIR=target/six cargo objcopy --release --features base_layer,panic_output --no-default-features -- -O binary base_layer_with_output.bin

launch env CARGO_TARGET_DIR=target/seven cargo objcopy --release --features recursion_step,panic_output --no-default-features -- -O binary recursion_layer_with_output.bin

launch env CARGO_TARGET_DIR=target/eight cargo objcopy --release --features recursion_log_23_step,panic_output --no-default-features -- -O binary recursion_log_23_layer_with_output.bin

launch env CARGO_TARGET_DIR=target/nine cargo objcopy --release --features recursion_step_no_delegation,panic_output --no-default-features -- -O binary recursion_layer_no_delegation_with_output.bin

launch env CARGO_TARGET_DIR=target/ten cargo objcopy --release --features final_recursion_step,panic_output --no-default-features -- -O binary final_recursion_layer_with_output.bin

launch env CARGO_TARGET_DIR=target/eleven cargo objcopy --release -Z build-std=core,panic_abort,alloc --features universal_circuit,panic_output --no-default-features -- -O binary universal.bin

launch env CARGO_TARGET_DIR=target/twelve cargo objcopy --release -Z build-std=core,panic_abort,alloc --features universal_circuit_no_delegation,panic_output --no-default-features -- -O binary universal_no_delegation.bin

reap

# now update verification keys.
#
# Skipped when AIRBENDER_SKIP_VK is set, so the Docker build can run the binaries and the
# keys as two separate layers: key generation is the more fragile stage, and when it fails
# as part of this same RUN the binaries layer is not cached and all twelve are rebuilt from
# scratch on the next attempt. Direct callers of build.sh still get keys by default.
if [ -n "${AIRBENDER_SKIP_VK:-}" ]; then
  echo "AIRBENDER_SKIP_VK set; skipping verification keys (run build_vk.sh separately)"
  exit 0
fi

./build_vk.sh
