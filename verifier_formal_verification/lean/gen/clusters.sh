#!/usr/bin/env bash
# Regenerate the cluster lemmas of a plain-Rust block from its symbolic run (gen/Dag.lean) and the op sequence in
# gen/clusters.py: slop/Slop/RV/<dir>/<prefix>{Raw,Nodes<k>,Values}.lean. Run after the block's code changes.
# usage: gen/clusters.sh MulAdd | PolyA | PolyB
set -e
cd "$(dirname "$0")/.."
b=${1:?block}
case $b in
  MulAdd) d=MulAdd ;;
  PolyA | PolyB) d=Ext4Poly ;;
  *) echo "unknown block $b" >&2; exit 1 ;;
esac
lake build "Slop.RV.$d.Block" >/dev/null
out=$(mktemp -d)
lake env lean --run gen/Dag.lean "$b" > "$out/dag.txt"
python3 gen/clusters.py "$b" "$out" < "$out/dag.txt"
for f in "$out"/*.lean; do
  t=slop/Slop/RV/$d/$(basename "$f")
  cmp -s "$f" "$t" || cp "$f" "$t"
done
rm -r "$out"
