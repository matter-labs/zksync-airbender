#!/usr/bin/env bash
# Backup checker (rare; not part of verify.sh): replay every declaration of human/ and slop/ through a second, fresh
# Lean kernel with `leanchecker`, which ships with the toolchain pinned in lean/lean-toolchain. It catches anything a
# tactic or metaprogram might have added without the kernel. Slow (tens of minutes): run it only at major
# milestones, e.g. before tagging or publishing a result, not per commit.
#   ./backup-check.sh           # our modules, on top of their (trusted) imports
#   ./backup-check.sh --fresh   # also replay all imports, Mathlib and Sail included (much longer)
#
# Memory: one module's check needs about 1 GB of private memory (a name given to the checker also selects every
# module below it, each with its own copy of the environment: that is what made `Human` take 18 GB), so modules run
# one per process and a new one starts only while the running ones' private memory plus the largest
# peak seen so far fits a budget: MEM_FRACTION (default 0.6) of the memory available at the start, or MEM_BUDGET_GB.
# A process running alone always may (large modules run alone); above a hard cap (90% of the memory available at the
# start) every checker is stopped and the run fails. At most JOBS (default 2) run at once: a check is mostly the
# system mapping the imported .olean files, and more processes at once slowed each one down more than they gained
# (14 at once: 2 h 37 min for 246 modules; about 10 s per module alone).
set -euo pipefail
cd "$(dirname "$0")/lean"

GB=$((1024 * 1024 * 1024))
avail_bytes() {
  if [[ -r /proc/meminfo ]]; then
    awk '/^MemAvailable:/ {print $2 * 1024}' /proc/meminfo
  else  # macOS: free + inactive + speculative + purgeable pages
    vm_stat | awk -v ps="$(sysctl -n hw.pagesize)" '
      /Pages (free|inactive|speculative|purgeable):/ {gsub(/\./, "", $NF); n += $NF} END {print n * ps}'
  fi
}
# Private (not file-backed) memory of the given processes, in bytes: the total and the largest. Resident size would count the mapped .olean
# files, which all checkers share.
private_bytes() {
  (( $# )) || { echo 0 0; return; }
  if [[ -r /proc/self/status ]]; then
    for p; do awk '/^RssAnon:/ {print $2 * 1024}' "/proc/$p/status" 2>/dev/null || true; done \
      | awk '{s += $1; if ($1 > m) m = $1} END {print s + 0, m + 0}'
  else  # macOS: top's MEM (physical footprint), e.g. 812K, 63M, 18G
    local args=(); for p; do args+=(-pid "$p"); done
    top -l 1 -stats pid,mem "${args[@]}" 2>/dev/null | awk '
      $1 ~ /^[0-9]+$/ { v = $2; sub(/[+-]$/, "", v); u = substr(v, length(v)); n = substr(v, 1, length(v) - 1)
        x = n * (u == "G" ? 2^30 : u == "M" ? 2^20 : u == "K" ? 2^10 : 1); s += x; if (x > m) m = x }
      END { printf "%d %d\n", s, m }'
  fi
}

AVAIL=$(avail_bytes)
if [[ -n "${MEM_BUDGET_GB:-}" ]]; then BUDGET=$((MEM_BUDGET_GB * GB))
else BUDGET=$(awk -v a="$AVAIL" -v f="${MEM_FRACTION:-0.6}" 'BEGIN {printf "%d", a * f}'); fi
HARD=$(awk -v a="$AVAIL" 'BEGIN {printf "%d", a * 0.9}')
JOBS="${JOBS:-2}"
echo "== available $((AVAIL / GB)) GB: budget $((BUDGET / GB)) GB, hard cap $((HARD / GB)) GB, at most $JOBS at once"

ROOTS=(Human HumanSail Slop Slop.RV.FinalPlain Slop.RV.FinalMop Slop.Equiv.Decode Slop.Equiv.Final Slop.Deleg)
echo "== build (the checker reads the compiled .olean files)"
lake build "${ROOTS[@]}" 2>&1 | grep -E "error|Build completed"

# run the checker directly (not under `lake env`), so its pid is the one we watch
export LEAN_PATH="$(lake env printenv LEAN_PATH)"
CHECKER="$(lake env which leanchecker)"

if [[ "${1:-}" == "--fresh" ]]; then
  MODS=(Slop.RV.FinalPlain Slop.RV.FinalMop Slop.Equiv.Final Slop.Deleg)  # each replays everything it imports
  FLAGS=(--fresh)
else
  # The checker covers only the modules it is given, so list every module. A name also selects every module below it
  # (`Human` selects all `Human.*`), each replayed with its own copy of the environment: so a module with modules
  # below it is skipped if it only imports (`Human`, `Slop`, …: nothing of its own), else run once for them all.
  ALL=($({ cd human && find . -name '*.lean'; cd ../slop && find . -name '*.lean'; } \
    | sed 's#^\./##; s#\.lean$##; s#/#.#g' | sort))
  src() { local f="${1//.//}.lean"; [[ -e "human/$f" ]] && echo "human/$f" || echo "slop/$f"; }
  MODS=(); covered=""
  for m in "${ALL[@]}"; do
    [[ -n "$covered" && "$m" == "$covered".* ]] && continue
    if printf '%s\n' "${ALL[@]}" | grep -q "^${m//./\\.}\\."; then
      if ! grep -qvE '^(import |[[:space:]]*$)' "$(src "$m")"; then echo "skip $m: imports only"; continue; fi
      covered="$m"
    fi
    MODS+=("$m")
  done
  FLAGS=()
fi

pids=(); names=(); peak=$((2 * GB)); failed=0   # peak: a first guess, raised as processes are measured
reap() {  # collect finished checkers; track the largest private memory seen
  local keep_p=() keep_n=() i
  for i in "${!pids[@]}"; do
    if kill -0 "${pids[$i]}" 2>/dev/null; then keep_p+=("${pids[$i]}"); keep_n+=("${names[$i]}")
    elif wait "${pids[$i]}"; then echo "ok ($(date +%H:%M:%S)): ${names[$i]}"
    else echo "FAIL: ${names[$i]}" >&2; failed=1; fi
  done
  pids=("${keep_p[@]+"${keep_p[@]}"}"); names=("${keep_n[@]+"${keep_n[@]}"}")
}
measure() {  # U: the running checkers' private memory; peak: the largest one process has used
  local m; read -r U m < <(private_bytes "${pids[@]+"${pids[@]}"}")
  if (( m > peak )); then peak=$m; fi
  if (( U > HARD )); then echo "FAIL: checkers use $((U / GB)) GB, over the hard cap: stopping" >&2
    kill "${pids[@]}" 2>/dev/null || true; exit 1; fi
}
for m in "${MODS[@]}"; do
  while :; do
    reap
    (( ${#pids[@]} == 0 )) && break
    measure
    # every running process may still grow to `peak`, and so may the new one
    (( ${#pids[@]} < JOBS && (${#pids[@]} + 1) * peak <= BUDGET && U + peak <= BUDGET )) && break
    sleep 2
  done
  "$CHECKER" "${FLAGS[@]+"${FLAGS[@]}"}" "$m" > /dev/null & pids+=($!); names+=("$m")
done
while (( ${#pids[@]} )); do reap; (( ${#pids[@]} )) && { measure; sleep 2; }; done
(( failed == 0 )) || { echo "FAIL: the backup checker rejected a module (above)"; exit 1; }
echo "OK: the backup checker accepted every declaration (${#MODS[@]} modules; largest process $((peak / 2**20)) MB)"
