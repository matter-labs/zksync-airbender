#!/usr/bin/env bash
# Backup check (docs/lean-strategies.md 1.5): the kernel_replay CI job run by hand, every few months at most.
# `lake check --paranoid` re-checks every declaration of the default targets (everything except the two files that
# import Clean) through Lean's kernel and the independent checkers bundled with the toolchain, and checks their
# axioms; leanchecker then replays the two Clean-importing modules (ci/lean-ci.sh kernel-check). Not part of
# verify.sh.
#
#   ./backup-check.sh                 Linux: here, on this checkout (needs bwrap with user namespaces; builds first)
#   ./backup-check.sh <rev> [log]     macOS (or anywhere with Docker): in the ci/ Docker harness (ci/sim.sh), on commit
#                                     <rev> (default HEAD), cold caches in the volume fvci-backup
#
# Environment: KERNEL_CHECKER (default paranoid; leanchecker = the pre-4.35 replay of our modules only).
# Docker: `lake check`'s bwrap sandbox needs user and mount namespaces, which Docker's default profiles deny, so this
# script (and only this one; the CI jobs never) runs the container privileged by default, inside Docker Desktop's VM
# (user decision, 2026-11-09). FVCI_DOCKER_OPTS overrides the `docker run` options. FVCI_CPUS / FVCI_MEM / LEAN_NUM_THREADS size the container
# (default 8 / 15g / 8). On the shared machine run it under the build lock (rvlock/lb.sh ./backup-check.sh ...).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
export KERNEL_CHECKER=${KERNEL_CHECKER:-paranoid}

if [[ "$(uname -s)" == Linux && $# -eq 0 ]]; then
  "$HERE/ci/lean-ci.sh" build
  "$HERE/ci/lean-ci.sh" kernel-check
else
  command -v docker >/dev/null || { echo "backup-check.sh: needs Linux (bwrap) or Docker" >&2; exit 2; }
  rev=${1:-HEAD} log=${2:-/dev/stdout}
  docker image inspect "${FVCI_IMAGE:-fvci:local}" >/dev/null 2>&1 || "$HERE/ci/sim.sh" image
  FVCI_DOCKER_OPTS=${FVCI_DOCKER_OPTS-"--privileged"} FVCI_JOB=kernel_replay "$HERE/ci/sim.sh" run fvci-backup "${FVCI_CPUS:-8}" "${FVCI_MEM:-15g}" \
    "${LEAN_NUM_THREADS:-8}" "$rev" - - "$log"
fi
