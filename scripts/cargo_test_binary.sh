#!/usr/bin/env bash
# Print the sole test executable from Cargo JSON; paths vary by toolchain.
set -euo pipefail
json="$(cargo test "$@" --no-run --message-format=json)"
executable="$(printf '%s\n' "$json" | python3 -c '
import json, sys
messages = [json.loads(line) for line in sys.stdin if line.strip()]
paths = [m["executable"] for m in messages
         if m["reason"] == "compiler-artifact" and m["profile"]["test"] and m["executable"]]
assert len(paths) == 1, f"expected one test executable, got {paths}; select --lib or --test"
print(paths[0])
')"
test -x "$executable"
printf '%s\n' "$executable"
