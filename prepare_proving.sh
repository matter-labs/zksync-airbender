#!/bin/sh

set -e

./recreate_verifiers.sh
cargo test --profile test-release -p cs
cargo test --profile test-release -p witness_eval_generator