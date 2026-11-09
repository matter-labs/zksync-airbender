#!/usr/bin/env bash
# Reproduce the Lean CI job locally in Docker (ubuntu:24.04, native arch), with CPU/memory limits.
#
#   ci/sim.sh image                                  build the image fvci:local (Dockerfile next to this script)
#   ci/sim.sh run <store> <cpus> <mem> <threads> <rev> <from> <to> [log]
#       run the job on commit <rev> of this repo, with --cpus <cpus> --memory <mem> (no swap) and
#       LEAN_NUM_THREADS=<threads>. <store> is the named volume holding the simulated actions/cache entries
#       (a fresh name = cold caches). The build cache is restored from entry <from> and saved as <to> ("-" = none).
#   ci/sim.sh clean <store>...                       remove the given store volumes
#
# Example (cold, then warm no-op on the same commit):
#   ci/sim.sh run fvci-small 4 16g 4 HEAD - head  cold.log
#   ci/sim.sh run fvci-small 4 16g 4 HEAD head - warm.log
# FVCI_STOP=sail stops after the Sail model step (to seed or time the sail cache alone).
# Each run is a build: on the shared machine run it under the build lock (rvlock/lb.sh ci/sim.sh run ...).
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(git -C "$HERE" rev-parse --show-toplevel)"
IMAGE=${FVCI_IMAGE:-fvci:local}

src_tar() { # rev out.tar: what actions/checkout gives the job (only the paths the Lean build reads)
  local jsons
  jsons=$(git -C "$REPO" show "$1:cs_formal_verification/lean/lakefile.toml" |
    grep -oE '"(\.\./)+cs/compiled_circuits/[A-Za-z0-9_.-]+\.json"' | tr -d '"' | sed -E 's|^(\.\./)+||' | sort -u)
  # shellcheck disable=SC2086
  git -C "$REPO" archive --format=tar -o "$2" "$1" cs_formal_verification $jsons
}

case "${1:-}" in
  image)
    docker build -t "$IMAGE" "$HERE" ;;
  run)
    store=$2 cpus=$3 mem=$4 threads=$5 rev=$6 from=$7 to=$8 log=${9:-/dev/stdout}
    tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
    src_tar "$rev" "$tmp/src.tar"
    docker volume create "$store" >/dev/null
    t0=$(date +%s)
    set +e
    docker run --rm --name "fvci-run-$$" --cpus "$cpus" --memory "$mem" --memory-swap "$mem" \
      -e LEAN_NUM_THREADS="$threads" -e MODULE_BUDGET_JOBS="${MODULE_BUDGET_JOBS:-4}" -e FVCI_STOP="${FVCI_STOP:-}" \
      -v "$store:/store" -v "$tmp:/in:ro" -v "$HERE:/opt/fvci:ro" \
      "$IMAGE" bash /opt/fvci/sim-job.sh "$from" "$to" > "$log" 2>&1
    rc=$?
    set -e
    echo "SIM rev=$(git -C "$REPO" rev-parse --short "$rev") cpus=$cpus mem=$mem threads=$threads from=$from to=$to" \
      "rc=$rc wall=$(( $(date +%s) - t0 ))s$([[ $rc == 137 ]] && echo ' (killed: OOM?)')" | tee -a "$log"
    exit "$rc" ;;
  clean)
    shift; docker volume rm "$@" ;;
  *)
    sed -n 2,15p "$0"; exit 2 ;;
esac
