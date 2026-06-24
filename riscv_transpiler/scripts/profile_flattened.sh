#!/usr/bin/env bash
#
# Profile the JIT-executed body (`runner.run` -> the generated machine code in
# `run_program`) of the `test_jit_full_block_with_flattened_responder` test.
#
# The hot region is the JIT-compiled `run_program` call inside `JittedCode::run`.
# Test setup (reading fixtures, hex-decoding the witness, JIT-compiling the text
# section) is negligible next to the ~6e8 emulated RISC-V instructions executed
# by `run_program`, so whole-process counters are a faithful proxy for it.
#
# Measurement back-ends:
#
#   1. macOS Instruments (`xctrace`) with a CUSTOM "CPU Counters" template that
#      records hardware PMCs in "Sample by Time" mode (so they are CLI-exportable).
#      The built-in "CPU Counters" template uses "CPU Bottlenecks" mode whose PMC
#      values are GUI-only and CANNOT be exported by `xctrace export`. Create the
#      custom template once (see RECIPE below); pass its name with --template.
#
#   2. Wall-clock fallback (always works, --no-instruments): the test prints
#          "Frequency is <MHz> MHz over <N> instructions (<ns> ns run time)".
#
# RECIPE -- create the custom template ONCE (needs the Instruments GUI):
#   1. Open Instruments (Xcode > Open Developer Tool > Instruments).
#   2. New trace -> choose "CPU Counters" (or Blank, then add the "CPU Counters"
#      instrument).
#   3. Select the "CPU Counters" instrument and open its recording configuration
#      (counter configuration editor / Recording Options).
#   4. Switch the sampling strategy from the "CPU Bottlenecks" preset to
#      "Sample by Time" (e.g. 1 ms) and add the events:
#          Instructions  (INST_RETIRED / FIXED_INSTRUCTIONS)
#          Cycles        (CPU_CLK_UNHALTED / CORE_ACTIVE_CYCLES / FIXED_CYCLES)
#   5. File > Save As Template... and name it exactly:  CPU Counters Raw
#
# Usage:
#   scripts/profile_flattened.sh [RUNS] [--template=NAME] [--no-instruments] [--debug]
#       RUNS               number of repetitions (default 10)
#       --template=NAME    Instruments template name (default "CPU Counters Raw")
#       --no-instruments   skip xctrace, only collect wall-clock timing
#       --debug            dump the exported counter-table schema/columns/rows
#
set -uo pipefail

RUNS=10
USE_INSTRUMENTS=1
TEMPLATE="CPU Counters Raw"
DEBUG=0
for arg in "$@"; do
  case "$arg" in
    --no-instruments) USE_INSTRUMENTS=0 ;;
    --debug) DEBUG=1 ;;
    --template=*) TEMPLATE="${arg#--template=}" ;;
    [0-9]*) RUNS="$arg" ;;
    *) echo "unknown arg: $arg" >&2; exit 2 ;;
  esac
done

CRATE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$CRATE_DIR"

TEST_NAME="test_jit_full_block_with_flattened_responder"
TEST_FILTER="jit::tests::${TEST_NAME}"
OUT_DIR="${CRATE_DIR}/target/profile_flattened"
mkdir -p "$OUT_DIR"

print_recipe() {
  sed -n '/^# RECIPE/,/CPU Counters Raw$/p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
}

echo "==> Building release test binary"
# Build (don't run) and capture the test executable path from cargo's JSON output.
TEST_BIN="$(
  cargo test --features jit --release --no-run --message-format=json 2>/dev/null \
    | /usr/bin/python3 -c '
import sys, json
path = None
for line in sys.stdin:
    line = line.strip()
    if not line.startswith("{"): continue
    try: m = json.loads(line)
    except Exception: continue
    # the lib unittest binary (kind ["lib"], profile.test == true) carries jit::tests
    if m.get("reason") == "compiler-artifact" and m.get("executable") \
       and m.get("target", {}).get("name") == "riscv_transpiler" \
       and m.get("profile", {}).get("test"):
        path = m["executable"]
print(path or "")
'
)"

if [[ -z "$TEST_BIN" || ! -x "$TEST_BIN" ]]; then
  echo "ERROR: could not locate test binary" >&2
  exit 1
fi
echo "    test binary: $TEST_BIN"

# Run a command with a hard timeout (macOS has no coreutils `timeout`).
with_timeout() { # $1 = seconds, rest = command
  local secs="$1"; shift
  perl -e 'my $s=shift; alarm $s; exec @ARGV or exit 127' "$secs" "$@"
}

# Decide whether Instruments is usable. The probe is time-boxed because on a
# misconfigured machine `xctrace` can hang in an uninterruptible state.
HAVE_XCTRACE=0
if [[ "$USE_INSTRUMENTS" == "1" ]] && command -v xcrun >/dev/null 2>&1; then
  if with_timeout 10 xcrun xctrace version >/dev/null 2>&1; then
    HAVE_XCTRACE=1
  else
    echo "    NOTE: 'xctrace' is unavailable/unauthorized (need 'sudo DevToolsSecurity -enable'"
    echo "          and a non-headless session). Falling back to wall-clock timing only."
  fi
fi

run_plain() { # $1 = log file
  "$TEST_BIN" --exact "$TEST_FILTER" --nocapture >"$1" 2>&1
}

run_instruments() { # $1 = log file, $2 = trace dir
  rm -rf "$2"
  xcrun xctrace record \
    --template "$TEMPLATE" \
    --output "$2" \
    --target-stdout - \
    --launch -- "$TEST_BIN" --exact "$TEST_FILTER" --nocapture >"$1" 2>&1
}

# Pull "<N> instructions (<ns> ns run time)" out of the test stdout.
parse_log() { # $1 = log file  -> echoes "N_instr ns"
  /usr/bin/python3 - "$1" <<'PY'
import re, sys
txt = open(sys.argv[1]).read()
m = re.search(r"over\s+(\d+)\s+instructions\s+\((\d+)\s+ns", txt)
print(f"{m.group(1)} {m.group(2)}" if m else "")
PY
}

# Record a setup-only run (RISCV_PROFILE_SKIP_RUN=1): same decode + JIT compile +
# allocations as a full run, but `run_program` is skipped. Subtracting its counters
# from a full run isolates run_program (setup is ~half the process here).
run_instruments_skip() { # $1 = log, $2 = trace dir
  rm -rf "$2"
  xcrun xctrace record \
    --template "$TEMPLATE" \
    --output "$2" \
    --env RISCV_PROFILE_SKIP_RUN=1 \
    --target-stdout - \
    --launch -- "$TEST_BIN" --exact "$TEST_FILTER" --nocapture >"$1" 2>&1
}

# Echo "INSTR CYCLES" extracted from a trace (0 0 if unavailable).
counters_of() { # $1 = trace dir
  local out i c
  out="$(/usr/bin/python3 "$SCRIPT_DIR/extract_counters.py" "$1" 2>/dev/null)"
  i="$(grep -m1 '^instructions=' <<<"$out" | cut -d= -f2)"
  c="$(grep -m1 '^cycles=' <<<"$out" | cut -d= -f2)"
  echo "${i:-0} ${c:-0}"
}

median() { /usr/bin/python3 -c "import sys,statistics as s; xs=[int(x) for x in sys.argv[1:] if x and x!='0']; print(int(s.median(xs)) if xs else 0)" "$@"; }

# Probe the template on a full run 1: confirm it runs and yields PMC counters.
if [[ "$HAVE_XCTRACE" == "1" ]]; then
  echo "==> Probing template \"$TEMPLATE\" (full run 1)"
  run_instruments "$OUT_DIR/run_1.log" "$OUT_DIR/run_1.trace"
  if ! grep -q "instructions (" "$OUT_DIR/run_1.log" 2>/dev/null; then
    echo "ERROR: Instruments recording with template \"$TEMPLATE\" did not run the test" >&2
    echo "       (template missing, or xctrace failed). Last log lines:" >&2
    tail -n 5 "$OUT_DIR/run_1.log" | sed 's/^/         /' >&2
    echo >&2; print_recipe >&2; echo >&2
    echo "Then re-run, or pass --template=\"<your name>\" / use --no-instruments." >&2
    exit 1
  fi
  [[ $DEBUG == 1 ]] && PROFILE_DEBUG=1 /usr/bin/python3 "$SCRIPT_DIR/extract_counters.py" "$OUT_DIR/run_1.trace" --debug >/dev/null 2>&1
  if ! grep -q "^instructions=" <<<"$(/usr/bin/python3 "$SCRIPT_DIR/extract_counters.py" "$OUT_DIR/run_1.trace" 2>/dev/null)"; then
    echo "WARNING: no usable PMC counter table from \"$TEMPLATE\" (probably still in" >&2
    echo "         'CPU Bottlenecks' mode; PMCs are then GUI-only). Recipe:" >&2
    echo >&2; print_recipe >&2; echo >&2
    echo "(continuing with wall-clock timing only)"
    HAVE_XCTRACE=0
  fi
fi

# --- Baseline (setup-only) phase, for run_program isolation -------------------
# run_program and the setup are both deterministic; per-core PMC noise only ADDS
# counts. So we record several setup-only baselines and several full runs and use
# MIN(full) - MIN(baseline): each min picks the least-perturbed (cleanest) window,
# which is the robust estimate of run_program's true host-instruction/cycle cost.
BI=(); BC=()
if [[ "$HAVE_XCTRACE" == "1" ]]; then
  BASE_RUNS=5
  echo "==> Recording ${BASE_RUNS} setup-only baselines (skip run_program)"
  for k in $(seq 1 "$BASE_RUNS"); do
    run_instruments_skip "$OUT_DIR/base_${k}.log" "$OUT_DIR/base_${k}.trace"
    read -r I C <<<"$(counters_of "$OUT_DIR/base_${k}.trace")"
    BI+=("$I"); BC+=("$C")
    printf "  baseline %d: x86=%'d cycles=%'d\n" "$k" "$I" "$C"
  done
fi

# --- Full runs ---------------------------------------------------------------
echo "==> Running ${RUNS}x full ($([[ $HAVE_XCTRACE == 1 ]] && echo "$TEMPLATE; gross = whole process" || echo 'wall-clock only'))"
if [[ "$HAVE_XCTRACE" == "1" ]]; then
  printf "%4s  %14s  %16s  %16s  %6s\n" "run" "riscv_instr" "x86_gross" "cyc_gross" "ipc"
else
  printf "%4s  %14s  %14s  %12s\n" "run" "riscv_instr" "ns" "ns/instr"
fi

SUM_NS=0; SUM_RISCV=0; N_OK=0; N_CNT=0; X86S=(); CYCS=()
for i in $(seq 1 "$RUNS"); do
  LOG="$OUT_DIR/run_${i}.log"; TRACE="$OUT_DIR/run_${i}.trace"
  if [[ "$HAVE_XCTRACE" == "1" ]]; then
    [[ "$i" == "1" && -d "$TRACE" ]] || run_instruments "$LOG" "$TRACE"
  else
    [[ "$i" == "1" && -s "$LOG" ]] || run_plain "$LOG"
  fi

  read -r N NS <<<"$(parse_log "$LOG")"
  if [[ -z "${N:-}" ]]; then printf "%4s  %14s\n" "$i" "FAILED (see $LOG)"; continue; fi
  SUM_RISCV=$((SUM_RISCV + N)); SUM_NS=$((SUM_NS + NS)); N_OK=$((N_OK + 1))

  if [[ "$HAVE_XCTRACE" == "1" ]]; then
    read -r X86G CYCG <<<"$(counters_of "$TRACE")"
    if [[ "${X86G:-0}" != "0" ]]; then
      IPC="$( [[ "${CYCG%.*}" != 0 ]] && /usr/bin/python3 -c "print(f'{$X86G/$CYCG:.3f}')" || echo "-" )"
      printf "%4s  %14s  %16d  %16d  %6s\n" "$i" "$N" "$X86G" "$CYCG" "$IPC"
      X86S+=("$X86G"); CYCS+=("$CYCG"); N_CNT=$((N_CNT + 1))
    else
      printf "%4s  %14s  %16s\n" "$i" "$N" "(no counters; see $TRACE)"
    fi
  else
    NSPI="$(/usr/bin/python3 -c "print(f'{$NS/$N:.3f}')")"
    printf "%4s  %14s  %14s  %12s\n" "$i" "$N" "$NS" "$NSPI"
  fi
done

echo "==> Summary (run_program only = MIN(full) - MIN(setup baseline))"
if [[ "$N_CNT" -gt 0 ]]; then
  X86STR="${X86S[*]}"; CYCSTR="${CYCS[*]}"; BISTR="${BI[*]}"; BCSTR="${BC[*]}"
  /usr/bin/python3 -c "
riscv=$SUM_RISCV/$N_OK
xs=[int(v) for v in '$X86STR'.split()]; cs=[int(v) for v in '$CYCSTR'.split()]
bi=[int(v) for v in '$BISTR'.split()] or [0]; bc=[int(v) for v in '$BCSTR'.split()] or [0]
fx,fc=min(xs),min(cs); bx,bcy=min(bi),min(bc)
nx,nc=fx-bx,fc-bcy
print(f'  emulated RISC-V instructions : {riscv:,.0f}  (deterministic)')
print(f'  MIN full gross   : x86={fx:,}  cyc={fc:,}')
print(f'  MIN setup base   : x86={bx:,}  cyc={bcy:,}')
print(f'  run_program net  : x86={nx:,}  cyc={nc:,}')
print(f'  host x86 / emulated instr    : {nx/riscv:.2f}')
print(f'  host cycles / emulated instr : {nc/riscv:.2f}')
print(f'  IPC                          : {nx/nc:.3f}' if nc>0 else '  IPC: n/a')
"
elif [[ "$N_OK" -gt 0 ]]; then
  /usr/bin/python3 -c "
ns=$SUM_NS/$N_OK; n=$SUM_RISCV/$N_OK
print(f'  emulated RISC-V instructions : {n:,.0f}')
print(f'  run_program wall time        : {ns:,.0f} ns ({ns/1e6:.1f} ms)')
print(f'  ns per emulated instruction  : {ns/n:.4f}')
print(f'  emulated MHz                 : {n/ns*1e3:.1f}')
"
fi

if [[ "$HAVE_XCTRACE" == "1" ]]; then
  echo "==> Traces in $OUT_DIR/run_*.trace + base_*.trace (open in Instruments for top-down detail)"
fi
