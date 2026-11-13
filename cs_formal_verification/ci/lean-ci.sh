#!/usr/bin/env bash
# The Lean CI job, one step per subcommand. Called by .github/workflows/lean-formal-verification.yml and by the
# local Docker reproduction (ci/sim.sh), so both run the same commands.
#
#   ci/lean-ci.sh deps          apt packages the job needs (ubuntu:24.04, as root)
#   ci/lean-ci.sh sail-deps     extra apt packages for generating the Sail model (only on a sail cache miss)
#   ci/lean-ci.sh elan          elan (pinned) + the toolchain in lean/lean-toolchain
#   ci/lean-ci.sh sail-key      hash of everything sail/regen.sh consumes (the sail cache key)
#   ci/lean-ci.sh sail-gen      sail/regen.sh --bootstrap-sail, then check it reproduced the committed files
#   ci/lean-ci.sh lean-sail     sail/fetch-lean-sail.sh (pinned lean-sail, never cached: no upstream licence)
#   ci/lean-ci.sh mathlib       lake exe cache get (Mathlib's prebuilt .olean files)
#   ci/lean-ci.sh lean-deps     build the dependencies (Sail model, Clean imports, the test executable's dependency
#                               objects) apart from our code (ci/dep_targets.py)
#   ci/lean-ci.sh verify        ./verify.sh, each of its steps timed
#   ci/lean-ci.sh build         lake build of the spec, proofs and tests (kernel_replay job)
#   ci/lean-ci.sh kernel-deps   bubblewrap, for `lake check` (kernel_replay job)
#   ci/lean-ci.sh kernel-probe  prints the KERNEL_CHECKER usable here: paranoid if bwrap can sandbox, else leanchecker
#   ci/lean-ci.sh kernel-check  replay our modules' constants in the kernel (kernel_replay job; KERNEL_CHECKER)
#   ci/lean-ci.sh report        what the build did: modules compiled, slowest modules, peak memory
#   ci/lean-ci.sh time <step>   run a step, then print its wall time, CPU time and peak memory (container cgroup)
#
# Environment: LEAN_NUM_THREADS (threads of each Lean process, and how many modules Lake compiles at once; the
# job's memory scales with it), MODULE_BUDGET_JOBS (modules the budget check compiles at once, default 4).
set -euo pipefail

CI_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
FV="${FV_DIR:-$(cd "$CI_DIR/.." && pwd)}"   # cs_formal_verification (FV_DIR: the copy run by ci/sim.sh)
LEAN="$FV/lean"
ELAN_VERSION=v4.2.4
export PATH="$HOME/.elan/bin:$PATH"
# Clean (v4.35.0) asks Lake to download its GitHub release's prebuilt .olean files; build it from source instead
export LAKE_NO_CACHE=${LAKE_NO_CACHE:-1}

log() { echo ">> $*" >&2; }
# apt-get and system directories: as root in the jobs' containers, through sudo on a host runner (kernel_replay job)
SUDO=; (( EUID == 0 )) || SUDO="sudo DEBIAN_FRONTEND=noninteractive"
sub() { awk -v a="$1" -v b="$2" -v d="${3:-1}" 'BEGIN { printf "%.1f", (a - b) / d }'; }

sail_inputs() { # every file sail/regen.sh reads (pins are in regen.sh and fetch-lean-sail.sh)
  find "$FV/sail/regen.sh" "$FV/sail/opam-packages.txt" "$FV/sail/fetch-lean-sail.sh" "$FV/sail/patches" "$FV/sail/config" "$FV/sail/smoke" \
    -type f | LC_ALL=C sort
}

step_deps() {
  export DEBIAN_FRONTEND=noninteractive
  $SUDO apt-get update -q
  # procps: module_budget.py samples `ps` during the build (without it every module is compiled a second time)
  $SUDO apt-get install -y -q --no-install-recommends ca-certificates curl git python3 procps zstd xz-utils
}

step_sail_deps() {
  export DEBIAN_FRONTEND=noninteractive
  $SUDO apt-get update -q
  $SUDO apt-get install -y -q --no-install-recommends opam build-essential m4 pkg-config libgmp-dev zlib1g-dev z3 \
    unzip bzip2 rsync patch
}

step_elan() {
  if ! command -v elan >/dev/null; then
    # the pinned elan release itself (elan-init.sh would fetch "latest"); GitHub's release downloads answered 504 for
    # minutes at a time here, so retry
    local d digest; d=$(mktemp -d)
    case "$(uname -m)" in
      x86_64) digest=42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63 ;;
      aarch64) digest=05febd124d84ebf994b2e7479922a5650b1e950c17ae3bd1ddd776b65bb72bf9 ;;
      *) echo "Unsupported elan installer architecture" >&2; return 1 ;;
    esac
    curl -sSfL --retry 8 --retry-all-errors --retry-delay 20 -o "$d/elan.tar.gz" \
      "https://github.com/leanprover/elan/releases/download/$ELAN_VERSION/elan-$(uname -m)-unknown-linux-gnu.tar.gz"
    printf '%s  %s\n' "$digest" "$d/elan.tar.gz" | sha256sum --check
    tar -xzf "$d/elan.tar.gz" -C "$d"
    "$d/elan-init" -y --no-modify-path --default-toolchain none
    rm -rf "$d"
  fi
  local i  # up to six attempts: the release download (GitHub) answered 504 for minutes at a time here
  for i in 1 2 3 4 5 6; do
    elan toolchain install "$(cat "$LEAN/lean-toolchain")" && break
    (( i < 6 )) || return 1
    log "toolchain download failed (attempt $i)"; sleep 30
  done
  (cd "$LEAN" && lean --version)
}

step_sail_key() {
  sail_inputs | xargs sha256sum | sed "s|$FV/||" | sha256sum | cut -c1-16
}

step_sail_gen() {
  # Keep the generated files for the diff. Only the Lake manifest is not emitted by regen.sh.
  "$FV/sail/regen.sh" --bootstrap-sail
  git -C "$FV" restore --source=HEAD -- lean/sail-rv32/lake-manifest.json
  git -C "$FV" diff --exit-code HEAD -- lean/sail-rv32 || {
    echo "sail/regen.sh changed committed files" >&2; exit 1;
  }
  [[ -z "$(git -C "$FV" ls-files --others --exclude-standard -- lean/sail-rv32)" ]] || {
    echo "sail/regen.sh added files" >&2; exit 1;
  }
  (cd "$LEAN/sail-rv32" && find SailRV32 SailRV32.lean -type f | LC_ALL=C sort | xargs sha256sum | sha256sum)
}

step_lean_sail() { "$FV/sail/fetch-lean-sail.sh"; }

step_mathlib() {
  # Mathlib's prebuilt files, only for the modules the build imports (ci/dep_targets.py --cache-args, ~1750 of 8908
  # files: the cache tool adds their imports). Anything missed would be compiled from source by the build; lean-deps
  # reports it. The cache tool binary is kept next to the downloaded archives (same cache key: the manifest), so a
  # warm run does not rebuild it. Up to three attempts: a retry fetches only what a flaky transfer left missing.
  cd "$LEAN"
  local dir=${MATHLIB_CACHE_DIR:-${XDG_CACHE_HOME:-$HOME/.cache}/mathlib} i args
  local bin=$dir/cache-exe
  for i in 1 2 3; do
    lake env true || { log "resolving the dependencies failed (attempt $i)"; sleep 10; continue; }
    args=$(python3 "$CI_DIR/dep_targets.py" --cache-args)
    if [[ -x $bin ]]; then
      lake env "$bin" get $args && return 0
    else
      lake exe cache get $args && { mkdir -p "$dir"; cp .lake/packages/mathlib/.lake/build/bin/cache "$bin"; return 0; }
    fi
    log "Mathlib cache get failed (attempt $i)"; sleep 10
  done
  return 1
}

step_lean_deps() { # the dependencies of the build (ci/dep_targets.py), built apart from our code
  cd "$LEAN"
  mkdir -p .lake
  python3 "$CI_DIR/dep_targets.py" > .lake/dep-targets.txt
  local rc=0
  xargs lake build < .lake/dep-targets.txt > .lake/dep-build.log 2>&1 || rc=$?
  grep -E '^(error|Build completed|Some required)' .lake/dep-build.log | tail -20 || true
  local src
  src=$(grep -cE 'Built (Mathlib|Batteries|Aesop|Qq|ProofWidgets|Plausible|ImportGraph|LeanSearchClient)[.A-Za-z0-9_]* \(' \
    .lake/dep-build.log || true)
  (( src == 0 )) || log "WARNING: $src modules of Mathlib's cache were compiled from source (missing from cache get)"
  return "$rc"
}

# the default targets (what `lake check` checks) and the two Clean-importing libraries
step_build() { (cd "$LEAN" && lake build && lake build CleanEquivalence CleanAudit); }

step_kernel_deps() { # bubblewrap: `lake check` builds and exports the project in a bwrap sandbox
  export DEBIAN_FRONTEND=noninteractive
  $SUDO apt-get update -q
  $SUDO apt-get install -y -q --no-install-recommends bubblewrap
  $SUDO mkdir -p /run/user /home   # the sandbox mounts a tmpfs on each; bwrap cannot create them in a read-only root
}

# kernel-probe: can bwrap create the namespaces `lake check` uses here? Prints the KERNEL_CHECKER to use: paranoid,
# or leanchecker with a loud warning (e.g. Ubuntu 24.04's AppArmor restriction of unprivileged user namespaces, or a
# container whose profiles deny them).
step_kernel_probe() {
  local err
  if err=$(bwrap --ro-bind / / --dev /dev --proc /proc --tmpfs /tmp --unshare-all --die-with-parent true 2>&1); then
    echo paranoid
  else
    log "bwrap cannot create the sandbox lake check needs: $err"
    [[ -n "${GITHUB_ACTIONS:-}" ]] && echo "::error title=kernel replay::bwrap cannot create a sandbox here ($err); lake check --paranoid skipped, falling back to leanchecker" >&2
    echo leanchecker
  fi
}

# The kernel replay (CI job kernel_replay nightly; backup-check.sh): every constant re-added to a kernel.
# KERNEL_CHECKER selects the tool:
#   paranoid: `lake check --paranoid` (Lean 4.35) on the default targets (lakefile.toml: everything except
#     human/CleanCore/Equivalence.lean and test/Checks/Axioms.lean, which import Clean's native_decide prime
#     instances, and which it would reject: it fails on any non-standard axiom in the exported environment). It
#     builds and exports them in a bwrap sandbox (Linux, user namespaces), replays the export through Lean's kernel
#     and the independent checkers bundled with the toolchain (leanchecker-paranoid, lean4lean, nanoda, con-leche,
#     con-ron), and checks the axioms. Then the two
#     Clean-importing modules, which it leaves out, are replayed by leanchecker (their own constants only).
#   leanchecker (default when unset; the fallback where bwrap cannot sandbox, see kernel-probe): the toolchain's
#     leanchecker over our module prefixes.
# lake check's sandbox clears the environment (LAKE_NO_CACHE does not reach it) and can write only lean/.lake: build
# first (step_build), so Clean is already built from source and sail-rv32/.lake and lean-sail/.lake are up to date.
# The kernel_replay job runs on the runner host (no container: Docker's default profiles deny bwrap the user and mount
# namespaces it needs) and sets KERNEL_CHECKER from kernel-probe; backup-check.sh sets paranoid.
# leanchecker replays KERNEL_CHECK_THREADS (default 2) modules at a time, each on top of its own import of the
# environment; memory grows fast with that count (container: 1 -> 1.3 GB, 2 -> 5.8-10.1 GB, 4 -> over 15 GB), so it
# does not follow LEAN_NUM_THREADS.
step_kernel_check() {
  cd "$LEAN"
  local t=${KERNEL_CHECK_THREADS:-2}
  case "${KERNEL_CHECKER:-leanchecker}" in
    paranoid)
      lake check --paranoid
      LEAN_NUM_THREADS=$t lake env leanchecker CleanCore.Equivalence Checks.Axioms ;;
    leanchecker)
      if (( $# )); then LEAN_NUM_THREADS=$t lake env leanchecker "$@"
      else LEAN_NUM_THREADS=$t lake env leanchecker CleanCore Human Proven Tests Checks; fi ;;
    *) echo "unknown KERNEL_CHECKER" >&2; return 2 ;;
  esac
}

step_verify() {
  # each verify.sh step ("== N. ...") gets the elapsed seconds since the previous one
  local t0 prev now line rc
  t0=$(date +%s.%N); prev=$t0
  set +e
  "$FV/verify.sh" 2>&1 | while IFS= read -r line; do
    if [[ "$line" == "== "* || "$line" == "OK" || "$line" == FAIL* ]]; then
      now=$(date +%s.%N)
      printf '[verify +%7.1fs, step took %7.1fs]\n' "$(sub "$now" "$t0")" "$(sub "$now" "$prev")"
      prev=$now
    fi
    printf '%s\n' "$line"
  done
  rc=${PIPESTATUS[0]}
  set -e
  return "$rc"
}

step_report() {
  set +o pipefail  # `| head` closes pipes early; the report must not fail the job
  local since=${1:-}
  cd "$LEAN"
  echo "== report"
  if [[ -n "$since" && -f "$since" ]]; then
    echo "olean files written since the start (ours / sail_rv32 / other packages):" \
      "$(find .lake/build -name '*.olean' -newer "$since" 2>/dev/null | wc -l) /" \
      "$(find sail-rv32/.lake sail-rv32/lean-sail/.lake -name '*.olean' -newer "$since" 2>/dev/null | wc -l) /" \
      "$(find .lake/packages -path '*/.lake/build/*' -name '*.olean' -newer "$since" 2>/dev/null | wc -l)"
    local ledger=.lake/module-cpu.tsv t
    t=$(stat -c %Y "$since")
    if [[ -f $ledger ]]; then
      echo "modules compiled by lake build (timed): $(awk -F'\t' -v t="$t" '$4=="build" && $5>=t' $ledger | wc -l);" \
        "re-measured by the budget check: $(awk -F'\t' -v t="$t" '$4!="build" && $5>=t' $ledger | wc -l)"
      echo "slowest modules compiled in this run (CPU s, how):"
      awk -F'\t' -v t="$t" '$5>=t {print $3"\t"$4"\t"$1}' $ledger | sort -rn | head -10
    fi
  fi
  [[ -f .lake/module-budget.tsv ]] && { echo "budget table top 5:"; sed -n 2,6p .lake/module-budget.tsv; }
  local cg=/sys/fs/cgroup
  [[ -r $cg/memory.peak ]] && echo "container memory.peak (with page cache): $(( $(cat $cg/memory.peak) / 1048576 )) MiB"
  [[ -r $cg/memory.events ]] && echo "container memory.events: $(tr '\n' ' ' < $cg/memory.events)"
  du -sh .lake/build sail-rv32/.lake .lake/packages 2>/dev/null || true
}

# time <step>: wall, CPU (the container's cgroup cpu.stat) and peak memory, sampled every second from the cgroup:
# `anon` is process memory (what runs out first; page cache is reclaimed), `current` includes the page cache.
# (The cgroup's memory.peak cannot be reset per step.) lean_procs: concurrent `lean` processes (max, mean).
step_time() {
  local name=$1; shift
  local cg=/sys/fs/cgroup t0 c0 c1 rc peakf
  t0=$(date +%s.%N)
  c0=$(awk '/^usage_usec/ {print $2}' $cg/cpu.stat 2>/dev/null || echo 0)
  peakf=$(mktemp)
  ( a=0 m=0 p=0 ps=0 k=0
    while :; do
      c=$(cat $cg/memory.current 2>/dev/null || echo 0); n=$(awk '$1=="anon" {print $2}' $cg/memory.stat 2>/dev/null || echo 0)
      l=$(pgrep -cx lean || true); l=${l:-0}
      (( c > m )) && m=$c; (( n > a )) && a=$n; (( l > p )) && p=$l; ps=$((ps + l)); k=$((k + 1))
      echo "$a $m $p $ps $k" > "$peakf.t"; mv -f "$peakf.t" "$peakf"; sleep 1
    done ) &
  local sampler=$!
  set +e; "$0" "$name" "$@"; rc=$?; set -e
  kill $sampler 2>/dev/null; wait $sampler 2>/dev/null || true
  c1=$(awk '/^usage_usec/ {print $2}' $cg/cpu.stat 2>/dev/null || echo 0)
  local pk; read -r -a pk < "$peakf" 2>/dev/null || pk=(0 0 0 0 1)
  printf 'STEP %-10s rc=%d wall=%ss cpu=%ss peak_anon=%sMiB peak_with_cache=%sMiB lean_procs_max=%s lean_procs_avg=%s disk_used=%sMiB\n' \
    "$name" "$rc" "$(sub "$(date +%s.%N)" "$t0")" "$(sub "$c1" "$c0" 1000000)" "$(( ${pk[0]:-0} / 1048576 ))" \
    "$(( ${pk[1]:-0} / 1048576 ))" "${pk[2]:-0}" "$(sub "${pk[3]:-0}" 0 "${pk[4]:-1}")" \
    "$(df -Pm / 2>/dev/null | awk 'NR==2 {print $3}')"
  rm -f "$peakf" "$peakf.t"
  return "$rc"
}

cmd=${1:?usage: lean-ci.sh <step>}; shift
case "$cmd" in
  deps) step_deps ;;
  sail-deps) step_sail_deps ;;
  elan) step_elan ;;
  sail-key) step_sail_key ;;
  sail-gen) step_sail_gen ;;
  lean-sail) step_lean_sail ;;
  mathlib) step_mathlib ;;
  lean-deps) step_lean_deps ;;
  kernel-check) step_kernel_check "$@" ;;
  build) step_build ;;
  kernel-deps) step_kernel_deps ;;
  kernel-probe) step_kernel_probe ;;
  verify) step_verify ;;
  report) step_report "$@" ;;
  time) step_time "$@" ;;
  *) echo "unknown step: $cmd" >&2; exit 2 ;;
esac
