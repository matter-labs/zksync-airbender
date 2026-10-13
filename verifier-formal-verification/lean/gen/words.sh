#!/usr/bin/env bash
# Regenerate slop/Slop/RV/Code/<block>.lean from the image (run after rust/build.sh).
# Files whose content is unchanged are not touched, so only the proofs of changed blocks are rebuilt.
set -e
cd "$(dirname "$0")/.."
lake build Image Human.RV32 >/dev/null
out=$(mktemp -d)
lake env lean gen/Words.lean | awk -v d="$out" '/^=== .* ===$/ { f = d "/" $2 ".lean"; next } { print > f }'
mkdir -p slop/Slop/RV/Code
for f in "$out"/*.lean; do
  t=slop/Slop/RV/Code/$(basename "$f")
  cmp -s "$f" "$t" || cp "$f" "$t"
done
for t in slop/Slop/RV/Code/*.lean; do [ -e "$out/$(basename "$t")" ] || rm "$t"; done
rm -r "$out"
