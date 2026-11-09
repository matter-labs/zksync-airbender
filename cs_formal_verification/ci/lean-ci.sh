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
#   ci/lean-ci.sh kernel-check  leanchecker: replay our modules' constants in the kernel (cold runs)
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

log() { echo ">> $*" >&2; }
sub() { awk -v a="$1" -v b="$2" -v d="${3:-1}" 'BEGIN { printf "%.1f", (a - b) / d }'; }

sail_inputs() { # every file sail/regen.sh reads (pins are in regen.sh and fetch-lean-sail.sh)
  find "$FV/sail/regen.sh" "$FV/sail/fetch-lean-sail.sh" "$FV/sail/patches" "$FV/sail/config" "$FV/sail/smoke" \
    -type f | LC_ALL=C sort
}

step_deps() {
  export DEBIAN_FRONTEND=noninteractive
  apt-get update -q
  # procps: module_budget.py samples `ps` during the build (without it every module is compiled a second time)
  apt-get install -y -q --no-install-recommends ca-certificates curl git python3 procps zstd xz-utils
}

step_sail_deps() {
  export DEBIAN_FRONTEND=noninteractive
  apt-get update -q
  apt-get install -y -q --no-install-recommends opam build-essential m4 pkg-config libgmp-dev zlib1g-dev z3 \
    unzip bzip2 rsync patch
}

step_elan() {
  if ! command -v elan >/dev/null; then
    # the pinned elan release itself (elan-init.sh would fetch "latest"); GitHub's release downloads answered 504 for
    # minutes at a time here, so retry
    local d; d=$(mktemp -d)
    curl -sSfL --retry 8 --retry-all-errors --retry-delay 20 -o "$d/elan.tar.gz" \
      "https://github.com/leanprover/elan/releases/download/$ELAN_VERSION/elan-$(uname -m)-unknown-linux-gnu.tar.gz"
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
  # regen.sh rebuilds lean/sail-rv32/ from scratch (deleting the committed lake-manifest.json); restore the
  # committed files, then require that regen.sh reproduced them exactly.
  "$FV/sail/regen.sh" --bootstrap-sail
  git -C "$FV" checkout -- lean/sail-rv32
  git -C "$FV" diff --exit-code -- lean/sail-rv32 || { echo "sail/regen.sh changed committed files" >&2; exit 1; }
  (cd "$LEAN/sail-rv32" && find SailRV32 SailRV32.lean -type f | LC_ALL=C sort | xargs sha256sum | sha256sum)
}

step_lean_sail() { "$FV/sail/fetch-lean-sail.sh"; }

step_mathlib() { # up to three attempts: a retry fetches only the files a flaky transfer left missing
  local i
  for i in 1 2 3; do
    (cd "$LEAN" && lake exe cache get) && return 0
    log "lake exe cache get failed (attempt $i)"; sleep 10
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
  return "$rc"
}

step_kernel_check() { # leanchecker (bundled with the toolchain): replay every constant of our modules in the kernel
  # One process; it replays the modules under these prefixes in parallel (LEAN_NUM_THREADS), each on top of its
  # imports. (A process per module costs ~1.5x the CPU: every process loads the imports again.)
  cd "$LEAN"
  lake env leanchecker CleanCore Human Slop Tests Checks
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
  kernel-check) step_kernel_check ;;
  verify) step_verify ;;
  report) step_report "$@" ;;
  time) step_time "$@" ;;
  *) echo "unknown step: $cmd" >&2; exit 2 ;;
esac
