#!/usr/bin/env bash
# v3 R6 carveout-probe gates, executable rather than transcribed.
#
#   matrix      the `--carveout-hint` / `--carveout-probe` rejection matrix against the
#               release binary. Every row exits NON-ZERO in the CLI's flag matrix, before
#               the config echo and therefore before any CUDA call — so this lane needs no
#               GPU and no lock, and it asserts that (empty stdout) rather than assuming it.
#   fixtures    the emitter's fixture matrix — every preregistered decision edge and every
#               fail-closed guard of tools/r6_probe_table.py. Self-contained: the fixture
#               logs are generated into a temp dir by the suite itself, so this lane runs on
#               a clean checkout (its one row that replays the real session logs SKIPs when
#               they are absent).
#   cpu         the crate's GPU-free unit tests (the probe lane set and its rotation balance)
#   all         the three lanes above
#
# What this script does NOT own: SASS identity and the full R3/R4/R5 regression. The R6 code
# change is host-only, so those are exactly R5's gates and `tools/r5_gates.sh all` runs them
# — it rebuilds the binary and needs the GPU lock, so it is NEVER invoked from here.
#
# Usage, from the repo root:
#   cargo build --release -p gpu_gkr_uniskip_bench
#   gpu/gkr_uniskip_bench/tools/r6_gates.sh all
#
# Exit status is the gate verdict: non-zero if any cell fails.
#
# NOTE for any build a future lane adds here: it must close fd 9 (`9>&-`). This script can
# run under `.agents/bin/with_gpu_lock.sh`, which holds the GPU lock on fd 9; a `cargo`
# invocation spawns the sccache SERVER, a long-lived daemon that inherits every open fd —
# including that one — and the lock then outlives the script. See r5_gates.sh's header.
set -uo pipefail

B=${B:-target/release/gpu_gkr_uniskip_bench}
DIR=$(cd "$(dirname "$0")" && pwd)
FIXTURES=$DIR/r6_fixtures/check.sh
# The whole-matrix reporting layer, shared by every gate script here: nothing is rejected on a gate
# prematurely, the run always ends with the full board (RR, 2026-08-13).
# shellcheck source=gate_report.sh
. "$DIR/gate_report.sh"

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

# ---------------------------------------------------------------- matrix

rows=0
ok=0

# reject <expected-substring> <args...>
# Three assertions per row, not one: non-zero exit, the stated reason, and NOTHING on
# stdout. The last one is what makes this lane GPU-free — `pass_config` runs before the
# config echo, which is the first thing main() prints and the first thing that touches the
# device, so a row that printed anything reached past the flag matrix into a real run.
reject() {
  local want=$1; shift
  local out rc
  rows=$((rows + 1))
  out=$("$B" --mode lsb-pair --log-trace 12 "$@" 2>"$TMP/err"); rc=$?
  local row_ok=1
  if [ "$rc" = 0 ]; then
    # Accepted, so there is no rejection message to compare against: nothing further computes.
    notrun "reject [$*]" "the CLI accepted the flags, so there is no rejection message to read"
    bad "the flags [$*] were accepted" "a non-zero exit" "exit 0"
    return
  fi
  if [ -n "$out" ]; then
    bad "reject [$*] printed on stdout — it reached the config echo, so CUDA was already initialized" \
        "nothing on stdout" "$(head -1 <<< "$out")"
    row_ok=0
  fi
  if ! grep -qF -- "$want" "$TMP/err"; then
    bad "reject [$*] message" "$want" "$(head -1 "$TMP/err")"
    row_ok=0
  fi
  [ "$row_ok" = 1 ] && ok=$((ok + 1))
}

matrix() {
  lane_is matrix
  if [ ! -x "$B" ]; then
    notrun "the whole matrix lane" "no binary at $B — cargo build --release -p gpu_gkr_uniskip_bench"
    return
  fi
  note "### --carveout-hint composes with the probe and with ONE cached 128 arm, nothing else"
  local compose="--carveout-hint steers the bounded 128-thread cached kernel; it composes"
  reject "$compose" --carveout-hint 25 --frontier-factorial
  # `--iterations 11` only so the cache-factorial's own balance gate (11 lanes) does not
  # fire first; the row is still about the hint.
  reject "$compose" --carveout-hint 25 --cache-factorial --iterations 11
  reject "$compose" --carveout-hint 25 --factorial
  reject "$compose" --carveout-hint 25 --pair-arm control
  reject "$compose" --carveout-hint 25 --cache-arm control
  reject "$compose" --carveout-hint 25 --cache-arm hot16 --block-threads 256
  reject "$compose" --carveout-hint 25 --cache-arm hot16 --block-threads 128 \
                    --no-cache-launch-bounds
  reject "$compose" --carveout-hint 25
  # The percentage RANGE is checked on the surface where the pct is still free — the probe
  # pins it to 16 before the range is ever reached.
  reject "is a percent of the maximum shared memory" \
         --carveout-hint 101 --cache-arm hot16 --block-threads 128 --profile
  reject "--carveout-probe's preregistered hint is 16" \
         --carveout-hint 101 --carveout-probe --term-order locality

  note "### the runner's own contract pin (the same one the emitter enforces on the logs)"
  reject "--carveout-probe is preregistered locality-only" --carveout-probe --term-order census
  reject "--carveout-probe is preregistered at 100 rounds / 10 warmup" \
         --carveout-probe --term-order locality --iterations 50
  reject "--carveout-probe is preregistered at 100 rounds / 10 warmup" \
         --carveout-probe --term-order locality --warmup 5
  reject "--carveout-probe's preregistered hint is 16" \
         --carveout-probe --term-order locality --carveout-hint 25

  note "### the single-arm hint surface is the ncu gate, and only that"
  reject "--carveout-hint on a single cached arm is the ncu gate surface" \
         --carveout-hint 16 --cache-arm hot16 --block-threads 128
  reject "--carveout-hint is a profiling knob" \
         --carveout-hint 16 --cache-arm hot16 --block-threads 128 --profile --validate

  note "### --carveout-probe owns its rotation"
  # The runner's literal gained "and every lane's body" in 824c53ff, when the pair-body selector
  # arrived and joined this rejection list; this pin was not moved with it and had been red since.
  local owns="--carveout-probe owns the arm set, both block sizes and every lane's body"
  reject "$owns; --cache-arm would change what the rotation runs" \
         --carveout-probe --cache-arm hot16
  reject "$owns; --block-threads would change what the rotation runs" \
         --carveout-probe --block-threads 128
  reject "$owns; --pair-arm would change what the rotation runs" \
         --carveout-probe --pair-arm control
  reject "--carveout-probe rotates lanes, so --profile would wrap whichever lane" \
         --carveout-probe --profile
  reject "--carveout-probe is a timing run; use --cache-arm" --carveout-probe --validate
  reject "--sources changes the program and invalidates every slope" \
         --carveout-probe --sources 400
  reject "--carveout-probe needs --iterations a multiple of 5" \
         --carveout-probe --iterations 99

  # POSITIVE CONTROLS. A matrix of rejections passes just as well when the flag is rejected
  # ALWAYS, so each accepted surface is proved by a row that reaches PAST the carveout gate
  # and fails on something downstream of it.
  note "### positive controls: the two accepted surfaces reach past the carveout gate"
  # Each fails on a gate DOWNSTREAM of the carveout ones, which is what proves the carveout
  # gates accepted it.
  reject "--carveout-probe is preregistered at 100 rounds / 10 warmup" \
         --carveout-hint 16 --carveout-probe --term-order locality --iterations 50
  reject "--cache-arm and --pair-arm select different rungs" \
         --carveout-hint 25 --cache-arm hot16 --block-threads 128 --profile --pair-arm control

  note "  rows=$rows passed=$ok"
  cellrow "the --carveout-hint rejection matrix" "$rows" "$ok"
  [ "$rows" = 25 ] || bad "matrix rows count; a row is missing; a check that never ran is not a verdict either way" "25" "${rows}"
  [ "$rows" = "$ok" ] || bad "rejection matrix incomplete"
}

# ---------------------------------------------------------------- fixtures

fixtures() {
  lane_is fixtures
  note "### emitter fixture matrix (tools/r6_probe_table.py)"
  if bash "$FIXTURES" > "$TMP/fixtures.log" 2>&1; then
    note "  $(tail -1 "$TMP/fixtures.log")"
    cellrow "r6 emitter fixtures" 1 1
  else
    # The sub-suite printed its own summary; carry it into this one and reproduce its transcript, so
    # nothing it found is lost behind a single red cell.
    bad "r6 emitter fixtures" "0 failed" "$(tail -1 "$TMP/fixtures.log")"
    cellrow "r6 emitter fixtures" 1 0
    cat "$TMP/fixtures.log"
  fi
}

# ---------------------------------------------------------------- cpu

cpu() {
  lane_is cpu
  note "### GPU-free unit tests (cpu_*)"
  # `9>&-`: see the header. This is the one lane here that invokes cargo.
  local result
  if RUSTFLAGS=-Awarnings cargo test -p gpu_gkr_uniskip_bench --lib --release cpu_ \
       > "$TMP/cpu.log" 2>&1 9>&-; then
    result=$(grep -E '^test result:' "$TMP/cpu.log" | tail -1)
    note "  $result"
    cellrow "cpu unit tests" 1 1
  else
    result=$(grep -E '^test result:' "$TMP/cpu.log" | tail -1)
    bad "cpu unit tests" "test result: ok" "${result:-<the run produced no test result line>}"
    cellrow "cpu unit tests" 1 0
    grep -E 'FAILED|panicked|^error|^test result:' "$TMP/cpu.log" | tail -20
  fi
}

case "${1:-all}" in
  matrix) matrix ;;
  fixtures) fixtures ;;
  cpu) cpu ;;
  all)
    matrix; fixtures; cpu
    note ""
    note "REMINDER: SASS identity and the full R3/R4/R5 regression are NOT in this script."
    note "The R6 change is host-only, so they are R5's gates unchanged:"
    note "  .agents/bin/with_gpu_lock.sh gpu/gkr_uniskip_bench/tools/r5_gates.sh all"
    note "(it rebuilds the binary and needs the GPU lock — run it yourself, not from here)"
    ;;
  *) echo "usage: $0 {matrix|fixtures|cpu|all}" >&2; exit 2 ;;
esac
gate_summary
exit "$fail"
