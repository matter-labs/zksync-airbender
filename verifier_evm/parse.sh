#!/bin/sh
set -e

out=$(mktemp)
# Keep Cargo JSON so we can show only diagnostics whose spans touch parse.rs.
# On failure, print those diagnostics to stderr so stats.sh can suppress normal
# parse output without hiding Rust errors.
if ! cargo -Zscript build --manifest-path parse.rs --message-format=json 2>/dev/null >"$out"; then
    jq -r 'select(.message.spans[]?.file_name == "parse.rs") | .message.rendered' "$out" >&2
    rm -f "$out"
    exit 1
fi
jq -r 'select(.message.spans[]?.file_name == "parse.rs") | .message.rendered' "$out"
exe=$(jq -r 'select(.executable != null) | .executable' "$out" | tail -1)
rm -f "$out"

if [ -z "$exe" ]; then
    exit 1
fi

"$exe"

work=$(mktemp -d -t parse-check.XXXXXX)
trap 'rm -rf "$work"' EXIT INT TERM HUP
cp gkr.sol "$work/gkr.sol"
[ -f foundry.toml ] && cp foundry.toml "$work/foundry.toml"

awk '
    /\/\/ __INLINE_CIRCUIT_YUL__/ {
        while ((getline line < "circuit.yul") > 0) print line
        close("circuit.yul")
        next
    }
    { print }
' "$work/gkr.sol" > "$work/gkr.injected.sol"
mv "$work/gkr.injected.sol" "$work/gkr.sol"

forge build -C "$work" --force
