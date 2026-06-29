#!/bin/sh
# Fast solx compile check (~5s vs ~11.7s for the old forge-based one).
#
# Why NOT `forge build --use solx`: forge fails to deserialize solx's JSON output
# ("Error: missing field `start`") and exits nonzero EVEN WHEN solx compiled the
# contract successfully — a forge<->solx version incompatibility. Because solx's
# diagnostic output is emitted from worker threads, whether forge chokes varies
# run-to-run, so the forge wrapper reported spurious ("sometimes") failures. solx's
# OWN exit code is authoritative, so we invoke it directly. Bonus: on a real failure,
# solx prints the actual stack-too-deep explanation instead of forge's opaque error.
#
# Speedups vs the original: (1) regenerate circuit.yul from parse.rs inline, skipping
# parse.sh's redundant solc `forge build` (~4.6s); (2) one direct solx compile.
set -e

GKR=gkr.sol
WORK=$(mktemp -d -t gkr-solx.XXXXXX)
trap 'rm -rf "$WORK"' EXIT INT TERM HUP

# --- regenerate circuit.yul from parse.rs (cargo script), surfacing only parse.rs diagnostics ---
CARGO_JSON="$WORK/cargo.json"
if ! cargo -Zscript build --manifest-path parse.rs --message-format=json 2>"$WORK/cargo.err" >"$CARGO_JSON"; then
    jq -r 'select(.message.spans[]?.file_name == "parse.rs") | .message.rendered' "$CARGO_JSON" >&2
    cat "$WORK/cargo.err" >&2
    exit 1
fi
jq -r 'select(.message.spans[]?.file_name == "parse.rs") | .message.rendered' "$CARGO_JSON"
EXE=$(jq -r 'select(.executable != null) | .executable' "$CARGO_JSON" | tail -1)
[ -z "$EXE" ] && { echo "no parse executable produced" >&2; exit 1; }
"$EXE" >/dev/null   # writes circuit.yul

# --- inject circuit.yul into gkr.sol ---
cp "$GKR" "$WORK/$GKR"
[ -f foundry.toml ] && cp foundry.toml "$WORK/foundry.toml"
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
else
    echo "missing circuit.yul or injection marker" >&2
    exit 1
fi

# --- compile with solx directly; its exit code is the verdict ---
echo "Compiling $GKR with $(solx --version | head -1)"
if solx -O3 --via-ir --bin "$WORK/$GKR" >/dev/null 2>"$WORK/solx.log"; then
    nwarn=$(grep -ci 'warning' "$WORK/solx.log" 2>/dev/null || echo 0)
    if [ "$nwarn" -gt 0 ]; then
        echo "solx: Compiler run successful ($nwarn warning(s))"
    else
        echo "solx: Compiler run successful"
    fi
else
    cat "$WORK/solx.log" >&2
    echo "solx: COMPILATION FAILED" >&2
    exit 1
fi
