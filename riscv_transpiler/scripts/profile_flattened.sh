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
# Two measurement back-ends:
#
#   1. macOS Instruments (`xctrace`) "CPU Counters" template -> hardware
#      "Instructions Retired" / "Cycles". This needs Developer Mode enabled:
#          sudo DevToolsSecurity -enable
#      and may require approving a one-time authorization dialog. It does NOT
#      work in a headless/SSH session.
#
#   2. Wall-clock fallback (always works): the test itself prints
#          "Frequency is <MHz> MHz over <N> instructions (<ns> ns run time)"
#      from which we derive ns and host-cycles per emulated instruction.
#
# Usage:
#   scripts/profile_flattened.sh [RUNS] [--no-instruments]
#       RUNS              number of repetitions (default 10)
#       --no-instruments  skip xctrace, only collect wall-clock timing
#
set -uo pipefail

RUNS=10
USE_INSTRUMENTS=1
for arg in "$@"; do
  case "$arg" in
    --no-instruments) USE_INSTRUMENTS=0 ;;
    [0-9]*) RUNS="$arg" ;;
    *) echo "unknown arg: $arg" >&2; exit 2 ;;
  esac
done

CRATE_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$CRATE_DIR"

TEST_NAME="test_jit_full_block_with_flattened_responder"
TEST_FILTER="jit::tests::${TEST_NAME}"
OUT_DIR="${CRATE_DIR}/target/profile_flattened"
mkdir -p "$OUT_DIR"

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
  # CPU Counters records hardware PMCs (Instructions Retired, Cycles, ...).
  xcrun xctrace record \
    --template "CPU Counters" \
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

echo "==> Running ${RUNS}x ($([[ $HAVE_XCTRACE == 1 ]] && echo 'Instruments CPU Counters' || echo 'wall-clock only'))"
printf "%4s  %16s  %14s  %12s\n" "run" "riscv_instr" "ns" "ns/instr"

SUM_NS=0
SUM_INSTR=0
N_OK=0
for i in $(seq 1 "$RUNS"); do
  LOG="$OUT_DIR/run_${i}.log"
  if [[ "$HAVE_XCTRACE" == "1" ]]; then
    run_instruments "$LOG" "$OUT_DIR/run_${i}.trace"
  else
    run_plain "$LOG"
  fi
  read -r N NS <<<"$(parse_log "$LOG")"
  if [[ -z "${N:-}" ]]; then
    printf "%4s  %16s\n" "$i" "FAILED (see $LOG)"
    continue
  fi
  NSPI="$(/usr/bin/python3 -c "print(f'{$NS/$N:.3f}')")"
  printf "%4s  %16s  %14s  %12s\n" "$i" "$N" "$NS" "$NSPI"
  SUM_NS=$((SUM_NS + NS)); SUM_INSTR=$((SUM_INSTR + N)); N_OK=$((N_OK + 1))
done

if [[ "$N_OK" -gt 0 ]]; then
  echo "==> Averages over ${N_OK} successful runs"
  /usr/bin/python3 -c "
ns=$SUM_NS/$N_OK; n=$SUM_INSTR/$N_OK
print(f'  emulated RISC-V instructions : {n:,.0f}')
print(f'  run_program wall time        : {ns:,.0f} ns ({ns/1e6:.1f} ms)')
print(f'  ns per emulated instruction  : {ns/n:.4f}')
print(f'  emulated MHz                 : {n/ns*1e3:.1f}')
# Assuming a ~3.0 GHz host core, host cycles per emulated instruction:
print(f'  ~host cycles/instr @3.0GHz   : {ns/n*3.0:.2f}')
"
fi

if [[ "$HAVE_XCTRACE" == "1" ]]; then
  echo "==> Instruments traces in $OUT_DIR/run_*.trace"
  echo "    Open in Instruments GUI, or export Instructions Retired with e.g.:"
  echo "      xcrun xctrace export --input $OUT_DIR/run_1.trace --toc"
  echo "      xcrun xctrace export --input $OUT_DIR/run_1.trace \\"
  echo "        --xpath '/trace-toc/run[@number=\"1\"]/data/table[@schema=\"counters-profile\"]'"
fi
