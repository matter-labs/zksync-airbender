#!/bin/sh
# Six-way bench: 3 compilers × 2 memory-safety modes. The `memory-safe`
# tag on the assembly block in gkr.sol is toggled between modes because
# solc has no flag/env-var to override it (solx has
# EVM_DISABLE_MEMORY_SAFE_ASM_CHECK, but it only suppresses the
# stack-too-deep error and doesn't help the solc rows).
#
# SPEED / how it works:
#   * The six (mode × compiler) cells are independent, so each gets its own
#     snapshot dir and they all run IN PARALLEL.
#   * Each cell does exactly ONE forge invocation: `forge test`. Gas comes
#     from its stdout; the runtime bytecode size is read straight from the
#     compiled artifact (.foundry/out/gkr.sol/GKRVerifier.json ->
#     deployedBytecode) — so there is no second `forge build --sizes` pass.
#     6 compiles total (was 13 in the serial original, 12 in earlier parallel
#     versions that rebuilt for --sizes).
#   * Each cell runs forge from inside its own dir (cd), so forge's out/cache
#     (which it resolves relative to CWD) are per-cell — no shared-cache race.
#   * circuit.yul is regenerated with `cargo run -Zscript parse.rs` (build +
#     run in one step), skipping parse.sh's extra forge-build sanity pass.
#     Falls back to ./parse.sh if that errors.
#
# OUTPUT: each cell's full compiler output (forge test: compile status, test
# result, gas logs) is printed in FIXED order — no-spill (solc, solc no-remat,
# solx) then spill (same) — streaming each cell as soon as it AND all earlier
# cells finish (a cell that finishes early waits its turn). Then the summary
# table. gkr.sol is never modified in place; the temp dir is deleted on exit.
#
# Options:
#   --skip-parse      reuse the existing circuit.yul (skip regeneration).
#
# Env knob (optional):
#   STATS_SKIP_PARSE=1  reuse the existing circuit.yul (skip regeneration) —
#                       fast re-bench when only compiler settings changed.
#
# Portable across BSD (macOS) and GNU (Linux): POSIX sh, no arrays, the
# `sed -i.tmp` / `mktemp -d -t` forms work on both, ordered streaming uses
# `wait <pid>` (POSIX), no `wait -n` / no bashisms.
RUNTIME_LIMIT=24576
GKR=gkr.sol
SKIP_PARSE=${STATS_SKIP_PARSE:-0}

while [ "$#" -gt 0 ]; do
    case "$1" in
        --skip-parse)
            SKIP_PARSE=1
            ;;
        -h|--help)
            echo "usage: ./stats.sh [--skip-parse]"
            exit 0
            ;;
        *)
            echo "usage: ./stats.sh [--skip-parse]" >&2
            echo "unknown option: $1" >&2
            exit 2
            ;;
    esac
    shift
done

START=$(date +%s)
SOLX=$(command -v solx 2>/dev/null)

WORK=$(mktemp -d -t stats.XXXXXX)
trap 'rm -rf "$WORK"' EXIT INT TERM HUP
cp "$GKR" "$WORK/base.sol"

# ─── Prep: regenerate circuit.yul, then inline it once ────────────────────
# `cargo run -Zscript` builds parse.rs incrementally and runs it; the run
# writes a fresh circuit.yul to cwd. Returns 0 on success.
regen_circuit() {
    cargo -Zscript run --quiet --manifest-path parse.rs >/dev/null 2>"$WORK/cargo.err"
}

have_yul=0
if [ "$SKIP_PARSE" = 1 ]; then
    echo "skipping parse, reusing existing circuit.yul" >&2
    have_yul=1
elif regen_circuit; then
    have_yul=1
elif ./parse.sh >"$WORK/parse.log" 2>&1; then
    echo "note: regenerated circuit.yul via parse.sh fallback." >&2
    have_yul=1
else
    echo "circuit.yul regeneration failed; continuing so the table still renders. Diagnostics:" >&2
    [ -s "$WORK/cargo.err" ] && cat "$WORK/cargo.err" >&2
    [ -s "$WORK/parse.log" ] && cat "$WORK/parse.log" >&2
fi

if [ "$have_yul" = 1 ] && [ -s circuit.yul ] && grep -q '__INLINE_CIRCUIT_YUL__' "$WORK/base.sol"; then
    awk '
        /\/\/ __INLINE_CIRCUIT_YUL__/ {
            while ((getline line < "circuit.yul") > 0) print line
            close("circuit.yul")
            next
        }
        { print }
    ' "$WORK/base.sol" > "$WORK/base.injected" && mv "$WORK/base.injected" "$WORK/base.sol"
fi

# ─── Build the two memory-safety source variants from the injected base ───
# Idempotent flippers, parametrized by target file. Each is two seds:
# (1) uncomment the target form, (2) comment out the other form — gated on
# `not already //`. -i.tmp + immediate rm is portable across BSD/GNU sed.
set_unsafe() {
    sed -i.tmp -E \
        -e 's|^([[:space:]]*)//[[:space:]]*(assembly[[:space:]]*\{[[:space:]]*)$|\1\2|' \
        -e '/^[[:space:]]*\/\//!s|^([[:space:]]*)(assembly[[:space:]]*\("memory-safe"\)[[:space:]]*\{[[:space:]]*)$|\1// \2|' \
        "$1"
    rm -f "$1.tmp"
}
set_safe() {
    sed -i.tmp -E \
        -e 's|^([[:space:]]*)//[[:space:]]*(assembly[[:space:]]*\("memory-safe"\)[[:space:]]*\{[[:space:]]*)$|\1\2|' \
        -e '/^[[:space:]]*\/\//!s|^([[:space:]]*)(assembly[[:space:]]*\{[[:space:]]*)$|\1// \2|' \
        "$1"
    rm -f "$1.tmp"
}
cp "$WORK/base.sol" "$WORK/unsafe.sol"; set_unsafe "$WORK/unsafe.sol"
cp "$WORK/base.sol" "$WORK/safe.sol";   set_safe   "$WORK/safe.sol"

# ─── Run one cell: a single `forge test` from inside its own dir ──────────
# Args: <label> <src.sol> <celldir> <foundry-profile|""> <wantsolx 0|1>
# Gas is parsed later from <dir>/test.out; size from the compiled artifact.
# Buffers the cell's forge-test output to <dir>/cell.log for ordered display.
one_cell() {
    label=$1; src=$2; dir=$3; prof=$4; wantsolx=$5
    mkdir -p "$dir"
    cp "$src" "$dir/$GKR"
    [ -f foundry.toml ] && cp foundry.toml "$dir/foundry.toml"
    : > "$dir/test.out"

    skip=0; set --
    if [ "$wantsolx" = 1 ]; then
        if [ -z "$SOLX" ]; then skip=1; else set -- --use "$SOLX"; fi
    fi

    if [ "$skip" = 1 ]; then
        { echo; echo "═══ $label — solx not found on PATH; skipped ═══"; } > "$dir/cell.log"
    else
        t0=$(date +%s)
        # cd into the cell dir so forge's out/cache land here (per-cell, no race).
        # Only set FOUNDRY_PROFILE when non-empty (an empty value makes forge
        # warn about a missing profile before falling back to default).
        if [ -n "$prof" ]; then
            ( cd "$dir" && FOUNDRY_PROFILE="$prof" forge test -vv --force --color always "$@" ) >"$dir/test.out" 2>&1
        else
            ( cd "$dir" && forge test -vv --force --color always "$@" ) >"$dir/test.out" 2>&1
        fi
        trc=$?
        el=$(( $(date +%s) - t0 ))
        {
            echo
            if [ "$trc" -eq 0 ]; then
                echo "═══ $label  (${el}s) ═══"
            else
                echo "═══ $label  (${el}s)  ✗ forge test FAILED (rc=$trc) ═══"
            fi
            cat "$dir/test.out"
        } > "$dir/cell.log" 2>&1
    fi
}

# ─── Launch all six cells in parallel ─────────────────────────────────────
[ -z "$SOLX" ] && echo "note: solx not found on PATH — its two cells will be skipped." >&2
echo "Compiling 6 cells (2 modes × 3 compilers) in parallel; streaming in order as each finishes…" >&2

one_cell "unsafe / solc"          "$WORK/unsafe.sol" "$WORK/u_solc"  ""                 0 & P_u_solc=$!
one_cell "unsafe / solc no-remat" "$WORK/unsafe.sol" "$WORK/u_remat" no_rematerializer 0 & P_u_remat=$!
one_cell "unsafe / solx"          "$WORK/unsafe.sol" "$WORK/u_solx"  ""                 1 & P_u_solx=$!
one_cell "safe / solc"            "$WORK/safe.sol"   "$WORK/s_solc"  ""                 0 & P_s_solc=$!
one_cell "safe / solc no-remat"   "$WORK/safe.sol"   "$WORK/s_remat" no_rematerializer 0 & P_s_remat=$!
one_cell "safe / solx"            "$WORK/safe.sol"   "$WORK/s_solx"  ""                 1 & P_s_solx=$!

# Stream each cell's output in FIXED order, as soon as it (and all earlier
# cells) have finished: `wait <pid>` blocks for that cell, returns instantly
# if it already finished. So a cell that finished early still waits its turn.
for entry in "$P_u_solc:u_solc" "$P_u_remat:u_remat" "$P_u_solx:u_solx" \
             "$P_s_solc:s_solc" "$P_s_remat:s_remat" "$P_s_solx:s_solx"; do
    wait "${entry%%:*}" 2>/dev/null
    cat "$WORK/${entry#*:}/cell.log" 2>/dev/null
done >&2
wait

# Gas inputs: each cell's captured forge-test output.
out1_u=$(cat "$WORK/u_solc/test.out"  2>/dev/null)
out2_u=$(cat "$WORK/u_remat/test.out" 2>/dev/null)
out3_u=$(cat "$WORK/u_solx/test.out"  2>/dev/null)
out1_s=$(cat "$WORK/s_solc/test.out"  2>/dev/null)
out2_s=$(cat "$WORK/s_remat/test.out" 2>/dev/null)
out3_s=$(cat "$WORK/s_solx/test.out"  2>/dev/null)

# ─── Results table ────────────────────────────────────────────────────
strip() { sed 's/\x1b\[[0-9;]*m//g; s/\r//g'; }

# Extract a logged value plus its trailing parenthesized percent. For lines
# like "  init_gas: 25853 (4%)" returns "25853 (4%)"; for plain values like
# "  gas/round: 321.14" returns "321.14".
val() {
    echo "$1" | strip | grep "  $2:" | head -1 | awk '{
        if (NF >= 3) print $2 " " $3
        else if (NF >= 2) print $2
    }'
}

data_kb() {
    awk -v bytes="$(val "$1" calldata_bytes)" 'BEGIN {
        gsub(/[^0-9].*/, "", bytes)
        if (bytes ~ /^[0-9]+$/) {
            printf "%.0f", bytes / 1024
        } else {
            printf "-"
        }
    }'
}

data_gas_with_kb() {
    awk -v gas="$(val "$1" calldata_gas)" -v kb="$(data_kb "$1")" 'BEGIN {
        if (gas != "" && kb != "-") {
            printf "%s (%skB)", gas, kb
        } else {
            printf "-"
        }
    }'
}

# Runtime bytecode size read directly from the cell's compiled artifact
# (deployedBytecode is a hex string; size = bytes), formatted with percent of
# the 24,576-byte EIP-170 cap. Returns "" (rendered as "—") if the cell didn't
# produce a clean artifact (e.g. compile failure).
size() {
    f="$1/.foundry/out/$GKR/GKRVerifier.json"
    [ -f "$f" ] || return
    hex=$(jq -r '.deployedBytecode.object // empty' "$f" 2>/dev/null)
    hex=${hex#0x}
    case "$hex" in ''|*[!0-9a-fA-F]*) return ;; esac
    awk -v b="$(( ${#hex} / 2 ))" -v lim="$RUNTIME_LIMIT" 'BEGIN { printf "%d (%.0f%%)", b, b * 100 / lim }'
}

# Keep the placeholder ASCII: awk implementations differ on whether printf
# widths count bytes or characters for UTF-8 strings.
row() {
    awk -v ms="$1" -v n="$2" -v d="${3:--}" -v i="${4:--}" -v r="${5:--}" -v m="${6:--}" -v b="${7:--}" 'BEGIN {
        printf "│ %-5s │ %-13s │ %16s │ %10s │ %12s │ %12s │ %12s │\n", ms, n, d, i, r, m, b
    }'
}

echo
echo '┌───────┬───────────────┬──────────────────┬────────────┬──────────────┬──────────────┬──────────────┐'
awk 'BEGIN{ printf "│ %-5s │ %-13s │ %16s │ %10s │ %12s │ %12s │ %12s │\n", "spill", "compiler", "eip7623 data_gas", "init_gas", "compress_gas", "main_gas", "bytecode" }'
echo '├───────┼───────────────┼──────────────────┼────────────┼──────────────┼──────────────┼──────────────┤'
row "NO"  "solc"       "$(data_gas_with_kb "$out1_u")" "$(val "$out1_u" init_gas)" "$(val "$out1_u" compress_gas)" "$(val "$out1_u" main_gas)" "$(size "$WORK/u_solc")"
row "NO"  "solc no-remat" "$(data_gas_with_kb "$out2_u")" "$(val "$out2_u" init_gas)" "$(val "$out2_u" compress_gas)" "$(val "$out2_u" main_gas)" "$(size "$WORK/u_remat")"
row "NO"  "solx"       "$(data_gas_with_kb "$out3_u")" "$(val "$out3_u" init_gas)" "$(val "$out3_u" compress_gas)" "$(val "$out3_u" main_gas)" "$(size "$WORK/u_solx")"
echo '├───────┼───────────────┼──────────────────┼────────────┼──────────────┼──────────────┼──────────────┤'
row "YES" "solc"       "$(data_gas_with_kb "$out1_s")" "$(val "$out1_s" init_gas)" "$(val "$out1_s" compress_gas)" "$(val "$out1_s" main_gas)" "$(size "$WORK/s_solc")"
row "YES" "solc no-remat" "$(data_gas_with_kb "$out2_s")" "$(val "$out2_s" init_gas)" "$(val "$out2_s" compress_gas)" "$(val "$out2_s" main_gas)" "$(size "$WORK/s_remat")"
row "YES" "solx"       "$(data_gas_with_kb "$out3_s")" "$(val "$out3_s" init_gas)" "$(val "$out3_s" compress_gas)" "$(val "$out3_s" main_gas)" "$(size "$WORK/s_solx")"
echo '└───────┴───────────────┴──────────────────┴────────────┴──────────────┴──────────────┴──────────────┘'

echo "Total wall time: $(( $(date +%s) - START ))s" >&2
