#!/usr/bin/env bash
# Regenerate the Blake2s cluster lemmas (slop/Slop/RV/Blake/{Cuts,G*,Steps}.lean) from the symbolic run of
# blake2s_compress (gen/Dag.lean) and the compression in gen/blake.py. Run after its code changes.
set -e
cd "$(dirname "$0")/.."
lake build Slop.RV.Blake.Block >/dev/null
out=$(mktemp -d)
lake env lean --run gen/Dag.lean Blake > "$out/dag.txt"
python3 gen/blake.py "$out" < "$out/dag.txt"
for f in "$out"/*.lean; do
  t=slop/Slop/RV/Blake/$(basename "$f")
  cmp -s "$f" "$t" || cp "$f" "$t"
done
rm -r "$out"
