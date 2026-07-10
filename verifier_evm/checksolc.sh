#!/bin/sh
set -e

GKR=gkr.sol
SKIP_PARSE=0

while [ "$#" -gt 0 ]; do
    case "$1" in
        --skip-parse)
            SKIP_PARSE=1
            ;;
        -h|--help)
            echo "usage: ./checksolc.sh [--skip-parse]"
            exit 0
            ;;
        *)
            echo "usage: ./checksolc.sh [--skip-parse]" >&2
            echo "unknown option: $1" >&2
            exit 2
            ;;
    esac
    shift
done

WORK=$(mktemp -d -t gkr-solc.XXXXXX)
trap 'rm -rf "$WORK"' EXIT INT TERM HUP

cp "$GKR" "$WORK/$GKR"
[ -f foundry.toml ] && cp foundry.toml "$WORK/foundry.toml"

PARSE_LOG="$WORK/parse.log"
if [ "$SKIP_PARSE" = 1 ]; then
    echo "skipping parse, reusing existing circuit.yul" >&2
elif ! ./parse.sh >"$PARSE_LOG" 2>&1; then
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
