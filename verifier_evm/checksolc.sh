#!/bin/sh
set -e

GKR=gkr.sol
WORK=$(mktemp -d -t gkr-solc.XXXXXX)
trap 'rm -rf "$WORK"' EXIT INT TERM HUP

cp "$GKR" "$WORK/$GKR"
[ -f foundry.toml ] && cp foundry.toml "$WORK/foundry.toml"

PARSE_LOG="$WORK/parse.log"
if ! ./parse.sh >"$PARSE_LOG" 2>&1; then
    echo "parse.sh failed:" >&2
    cat "$PARSE_LOG" >&2
    exit 1
fi

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

forge build -C "$WORK" --force --color never
