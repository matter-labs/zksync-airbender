#!/usr/bin/env bash
set -euo pipefail

# The first optional argument is the expected version of rust compiler. If it's provided,
# check that `rustc --version` matches the expected version.
if [[ $# -gt 0 ]]; then
  expected_version="$1"
  # Note: `rustc` version might not match the version name in `rustup`
  actual_version="$(rustup show active-toolchain)"
  if [[ "$actual_version" != *"$expected_version"* ]]; then
    echo "Error: Expected rustc version to contain '$expected_version', but got '$actual_version'"
    exit 1
  fi
fi

artifact_names=(
  "recursion_in_unrolled_layer"
  "recursion_in_unified_layer"
  "recursion_in_unrolled_layer_security_100_bits"
  "recursion_in_unified_layer_security_100_bits"
)

# Determine feature set based on artifact name
detect_features() {
  local name="$1"

  case "$name" in
    recursion_in_unrolled_layer)
      echo "recursion_in_unrolled_layer,security_80"
      ;;
    recursion_in_unified_layer)
      echo "recursion_in_unified_layer,security_80"
      ;;
    recursion_in_unrolled_layer_security_100_bits)
      echo "recursion_in_unrolled_layer,security_100"
      ;;
    recursion_in_unified_layer_security_100_bits)
      echo "recursion_in_unified_layer,security_100"
      ;;
    *)
      echo "Unknown artifact name: $name" >&2
      exit 1
      ;;
  esac
}

# Function to remove bin/elf/text files for a provided argument
remove_build_artifacts() {
  local prefix="$1"
  rm -f "${prefix}.bin" "${prefix}.elf" "${prefix}.text"
}

# Build artifacts with the provided set of features and save with provided name
build_artifacts() {
  local features="$1"
  local name="$2"

  # Each artifact has its own target directory to not collide with each other, allowing parallel building & reproducible builds.
  local artifact_target_dir="target/${name}"
  local objcopy_args=(-Z build-std=core,panic_abort,alloc --features "${features}" --no-default-features)

  CARGO_TARGET_DIR="$artifact_target_dir" cargo objcopy --release "${objcopy_args[@]}" -- -O binary "${name}.bin"
  CARGO_TARGET_DIR="$artifact_target_dir" cargo objcopy --release "${objcopy_args[@]}" -- -R .text "${name}.elf"
  CARGO_TARGET_DIR="$artifact_target_dir" cargo objcopy --release "${objcopy_args[@]}" -- -O binary --only-section=.text "${name}.text"
}

# 1) Clean old artifacts
for artifact in "${artifact_names[@]}"; do
  remove_build_artifacts "${artifact}"
done

# 2) Build artifacts
for artifact in "${artifact_names[@]}"; do
  features="$(detect_features "$artifact")"
  # Build in parallel.
  ( build_artifacts "$features" "$artifact" ) &
done

wait

# now update verification keys.
# ./build_vk.sh
