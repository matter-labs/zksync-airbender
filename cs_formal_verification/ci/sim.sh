#!/usr/bin/env bash
# Reproduce the Lean CI job locally in Docker (ubuntu:24.04, native arch), with CPU/memory limits.
#
#   ci/sim.sh image                                  build the image fvci:local (Dockerfile next to this script)
#   ci/sim.sh run <store> <cpus> <mem> <threads> <rev> <from> <to> [log]
#       run the job on commit <rev> of this repo, with --cpus <cpus> --memory <mem> (no swap) and
#       LEAN_NUM_THREADS=<threads>. <store> is the named volume holding the simulated actions/cache entries
#       (a fresh name = cold caches; an absolute host path keeps the store and the work tree on the host disk).
#       The build cache is restored from entry <from> and saved as <to> ("-" = none).
#   ci/sim.sh clean <store>...                       remove the given store volumes
#
# Example (cold, then warm no-op on the same commit):
#   ci/sim.sh run fvci-small 4 16g 4 HEAD - head  cold.log
#   ci/sim.sh run fvci-small 4 16g 4 HEAD head - warm.log
# FVCI_STOP=sail stops after the Sail model step (to seed or time the sail cache alone). VERIFY_AUDITS (fresh|replay)
# is passed to verify.sh; FVCI_KERNEL=1 adds the kernel replay (the kernel_replay job's check) after verify.sh.
# Each run is a build: on the shared machine run it under the build lock (rvlock/lb.sh ci/sim.sh run ...).
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(git -C "$HERE" rev-parse --show-toplevel)"
IMAGE=${FVCI_IMAGE:-fvci:local}

src_tar() { # rev out.tar: what actions/checkout gives the job (only the paths the Lean build reads)
  local jsons  # the circuit JSONs the Lean sources and the lakefile name (the tests also read a cached layout)
  jsons=$(git -C "$REPO" grep -ohE 'compiled_circuits/[A-Za-z0-9_.-]+\.json' "$1" -- cs_formal_verification/lean |
    sort -u | sed 's|^|cs/|')
  local linked  # the files outside cs_formal_verification that its guides link (the review check resolves them)
  linked=$(python3 - "$REPO" "$1" <<'PY'
import posixpath, re, subprocess, sys
repo, rev = sys.argv[1], sys.argv[2]
git = lambda *a: subprocess.run(["git", "-C", repo, *a], capture_output=True, text=True).stdout
out = set()
for f in git("ls-tree", "-r", "--name-only", rev, "cs_formal_verification").split():
    if f.endswith(".md"):
        for t in re.findall(r"\]\(([^)\s#]+)", git("show", f"{rev}:{f}")):
            p = posixpath.normpath(posixpath.join(posixpath.dirname(f), t))
            if "://" not in t and not p.startswith(("cs_formal_verification", "..")) and git("cat-file", "-t", f"{rev}:{p}").strip():
                out.add(p)
print("\n".join(sorted(out)))
PY
)
  # shellcheck disable=SC2086
  git -C "$REPO" archive --format=tar -o "$2" "$1" cs_formal_verification $(printf '%s\n' $jsons $linked | sort -u)
}

case "${1:-}" in
  image)
    docker build -t "$IMAGE" "$HERE" ;;
  run)
    store=$2 cpus=$3 mem=$4 threads=$5 rev=$6 from=$7 to=$8 log=${9:-/dev/stdout}
    tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
    src_tar "$rev" "$tmp/src.tar"
    if [[ "$store" == /* ]]; then
      # a host directory instead of a named volume: the store and the work tree live on the host disk (for a Docker VM
      # whose disk is too small; file I/O through the VM share is slower, so the times are not comparable)
      mkdir -p "$store/store"; [[ -d "$store/w" ]] && rm -rf "${store:?}/w"; mkdir -p "$store/w"
      mounts=(-v "$store/store:/store" -v "$store/w:/w")
    else
      docker volume create "$store" >/dev/null
      mounts=(-v "$store:/store")
    fi
    t0=$(date +%s)
    set +e
    docker run --name "fvci-run-$$" --cpus "$cpus" --memory "$mem" --memory-swap "$mem" \
      -e LEAN_NUM_THREADS="$threads" -e MODULE_BUDGET_JOBS="${MODULE_BUDGET_JOBS:-4}" -e FVCI_STOP="${FVCI_STOP:-}" \
      -e VERIFY_AUDITS="${VERIFY_AUDITS:-fresh}" -e FVCI_KERNEL="${FVCI_KERNEL:-0}" \
      -e KERNEL_CHECK_THREADS="${KERNEL_CHECK_THREADS:-2}" \
      "${mounts[@]}" -v "$tmp:/in:ro" -v "$HERE:/opt/fvci:ro" \
      "$IMAGE" bash /opt/fvci/sim-job.sh "$from" "$to" > "$log" 2>&1
    rc=$?
    oom=$(docker inspect -f '{{.State.OOMKilled}}' "fvci-run-$$" 2>/dev/null || echo "?")
    docker rm "fvci-run-$$" >/dev/null 2>&1
    set -e
    echo "SIM rev=$(git -C "$REPO" rev-parse --short "$rev") cpus=$cpus mem=$mem threads=$threads from=$from to=$to" \
      "rc=$rc oom_killed=$oom wall=$(( $(date +%s) - t0 ))s" | tee -a "$log"
    exit "$rc" ;;
  clean)
    shift; docker volume rm "$@" ;;
  *)
    sed -n 2,15p "$0"; exit 2 ;;
esac
