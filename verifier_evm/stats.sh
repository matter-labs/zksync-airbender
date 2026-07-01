# Six-way bench: 3 compilers × 2 memory-safety modes. The `memory-safe`
# tag on the assembly block in gkr.sol is toggled between modes because
# solc has no flag/env-var to override it (solx has
# EVM_DISABLE_MEMORY_SAFE_ASM_CHECK, but it only suppresses the
# stack-too-deep error and doesn't help the solc rows).
#
# To avoid ever modifying gkr.sol in place, we snapshot it into a temp
# directory at script start and run forge from there via `-C <tempdir>`.
# The real gkr.sol is never touched — you're free to edit it during the
# run; your edits won't affect the script and the script won't affect
# your edits. On exit (incl. Ctrl-C) the temp dir is just deleted.
#
# Per profile we capture:
#   - `forge build --sizes --force` -> runtime bytecode size (with % of cap)
#   - `forge test -vv --force`      -> init_gas, compress_gas, main_gas
# Failures show "—" in their cells.
RUNTIME_LIMIT=24576
GKR=gkr.sol

# Snapshot dir. Forge reads sources from here (-C $WORK); the original
# gkr.sol stays read-only as far as this script is concerned.
WORK=$(mktemp -d -t stats.XXXXXX)
trap 'rm -rf "$WORK"' EXIT INT TERM HUP
cp "$GKR" "$WORK/$GKR"

if ./parse.sh >/dev/null; then
    if [ -s circuit.yul ] && grep -q '__INLINE_CIRCUIT_YUL__' "$WORK/$GKR"; then
        awk '
            /\/\/ __INLINE_CIRCUIT_YUL__/ {
                while ((getline line < "circuit.yul") > 0) print line
                close("circuit.yul")
                next
            }
            { print }
        ' "$WORK/$GKR" > "$WORK/$GKR.with_circuit"
        mv "$WORK/$GKR.with_circuit" "$WORK/$GKR"
    fi
else
    echo "parse.sh failed; continuing without circuit inline Yul injection."
fi

detect_mode() {
    if grep -qE '^[[:space:]]*assembly[[:space:]]*\("memory-safe"\)[[:space:]]*\{' "$WORK/$GKR"; then
        echo 'memory-safe (assembly ("memory-safe") {)'
    elif grep -qE '^[[:space:]]*assembly[[:space:]]*\{' "$WORK/$GKR"; then
        echo 'memory-unsafe (assembly {)'
    else
        echo 'unknown — neither assembly form is active'
    fi
}
echo "Snapshotted $GKR -> $WORK; initial state: $(detect_mode)"

# Idempotent flippers. Each is two seds: (1) uncomment the target form,
# (2) comment out the other form — gated on `not already //` so reruns
# are no-ops. -i.tmp + immediate rm is portable across BSD/GNU sed.
# Both operate on the SNAPSHOT copy, never the real file.
set_unsafe() {
    sed -i.tmp -E \
        -e 's|^([[:space:]]*)//[[:space:]]*(assembly[[:space:]]*\{[[:space:]]*)$|\1\2|' \
        -e '/^[[:space:]]*\/\//!s|^([[:space:]]*)(assembly[[:space:]]*\("memory-safe"\)[[:space:]]*\{[[:space:]]*)$|\1// \2|' \
        "$WORK/$GKR"
    rm -f "$WORK/$GKR.tmp"
}
set_safe() {
    sed -i.tmp -E \
        -e 's|^([[:space:]]*)//[[:space:]]*(assembly[[:space:]]*\("memory-safe"\)[[:space:]]*\{[[:space:]]*)$|\1\2|' \
        -e '/^[[:space:]]*\/\//!s|^([[:space:]]*)(assembly[[:space:]]*\{[[:space:]]*)$|\1// \2|' \
        "$WORK/$GKR"
    rm -f "$WORK/$GKR.tmp"
}

# Pre-build sanity check. Never abort here: even if the snapshot currently
# fails to compile, we still want the per-profile runs below to execute and
# the final table to render with empty cells for failing variants.
build_log=$(forge build -C "$WORK" 2>&1)
if [ $? -ne 0 ]; then
    echo "Initial forge build failed; continuing so the results table can still render."
    echo "$build_log"
fi

# `--color always` forces ANSI colors when stdout isn't a TTY (which it
# isn't, since `$(...)` captures it). Earlier versions wrapped each call
# in `script` to fake a TTY, but that also dragged in foundry's progress
# spinner — which leaves residue (and large blank lines) when a test
# fails mid-compile. Running forge directly skips the spinner; the
# captured `out*` strings still get color codes stripped before parsing.

# ─── Mode 1/2: memory-unsafe ──────────────────────────────────────────
set_unsafe
echo
echo '═══ Mode 1/2: memory-unsafe (assembly {) ═══'
out1_u=$(forge test -C "$WORK" -vv --force --color always 2>&1 | tee /dev/stderr)
out2_u=$(FOUNDRY_PROFILE=no_rematerializer forge test -C "$WORK" -vv --force --color always 2>&1 | tee /dev/stderr)
out3_u=$(forge test -C "$WORK" -vv --force --color always --use "$(which solx)" 2>&1 | tee /dev/stderr)

echo
echo "Computing builds (memory-unsafe):"
echo "  default solc..."
build1_u=$(forge build -C "$WORK" --sizes --force 2>/dev/null)
echo "  no_rematerializer..."
build2_u=$(FOUNDRY_PROFILE=no_rematerializer forge build -C "$WORK" --sizes --force 2>/dev/null)
echo "  solx..."
build3_u=$(forge build -C "$WORK" --sizes --force --use "$(which solx)" 2>/dev/null)

# ─── Mode 2/2: memory-safe ────────────────────────────────────────────
set_safe
echo
echo '═══ Mode 2/2: memory-safe (assembly ("memory-safe") {) ═══'
out1_s=$(forge test -C "$WORK" -vv --force --color always 2>&1 | tee /dev/stderr)
out2_s=$(FOUNDRY_PROFILE=no_rematerializer forge test -C "$WORK" -vv --force --color always 2>&1 | tee /dev/stderr)
out3_s=$(forge test -C "$WORK" -vv --force --color always --use "$(which solx)" 2>&1 | tee /dev/stderr)

echo
echo "Computing builds (memory-safe):"
echo "  default solc..."
build1_s=$(forge build -C "$WORK" --sizes --force 2>/dev/null)
echo "  no_rematerializer..."
build2_s=$(FOUNDRY_PROFILE=no_rematerializer forge build -C "$WORK" --sizes --force 2>/dev/null)
echo "  solx..."
build3_s=$(forge build -C "$WORK" --sizes --force --use "$(which solx)" 2>/dev/null)

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

# Pull GKRVerifier runtime size from `forge build --sizes` table, formatted
# with percent of the 24,576-byte EIP-170 cap.
size() {
    echo "$1" | strip | awk -F'|' -v lim="$RUNTIME_LIMIT" '
        / GKRVerifier / {
            gsub(/[ ,]/, "", $3)
            if ($3 ~ /^[0-9]+$/) {
                printf "%d (%.0f%%)", $3, $3 * 100 / lim
                exit
            }
        }
    '
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
row "NO"  "solc"       "$(data_gas_with_kb "$out1_u")" "$(val "$out1_u" init_gas)" "$(val "$out1_u" compress_gas)" "$(val "$out1_u" main_gas)" "$(size "$build1_u")"
row "NO"  "solc no-remat" "$(data_gas_with_kb "$out2_u")" "$(val "$out2_u" init_gas)" "$(val "$out2_u" compress_gas)" "$(val "$out2_u" main_gas)" "$(size "$build2_u")"
row "NO"  "solx"       "$(data_gas_with_kb "$out3_u")" "$(val "$out3_u" init_gas)" "$(val "$out3_u" compress_gas)" "$(val "$out3_u" main_gas)" "$(size "$build3_u")"
echo '├───────┼───────────────┼──────────────────┼────────────┼──────────────┼──────────────┼──────────────┤'
row "YES" "solc"       "$(data_gas_with_kb "$out1_s")" "$(val "$out1_s" init_gas)" "$(val "$out1_s" compress_gas)" "$(val "$out1_s" main_gas)" "$(size "$build1_s")"
row "YES" "solc no-remat" "$(data_gas_with_kb "$out2_s")" "$(val "$out2_s" init_gas)" "$(val "$out2_s" compress_gas)" "$(val "$out2_s" main_gas)" "$(size "$build2_s")"
row "YES" "solx"       "$(data_gas_with_kb "$out3_s")" "$(val "$out3_s" init_gas)" "$(val "$out3_s" compress_gas)" "$(val "$out3_s" main_gas)" "$(size "$build3_s")"
echo '└───────┴───────────────┴──────────────────┴────────────┴──────────────┴──────────────┴──────────────┘'
