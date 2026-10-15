#!/usr/bin/env bash
# Regenerate the cluster lemmas of a plain-Rust block (slop/Slop/RV/<Block>/{Raw,Nodes1,Nodes2,Values}.lean) from its
# symbolic run (gen/Dag.lean) and the op sequence in gen/clusters.py. Run after the block's code changes.
# usage: gen/clusters.sh MulAdd
set -e
cd "$(dirname "$0")/.."
b=${1:?block}
lake build "Slop.RV.$b.Block" >/dev/null
out=$(mktemp -d)
lake env lean --run gen/Dag.lean "$b" > "$out/dag.txt"
python3 gen/clusters.py "$b" "$out" < "$out/dag.txt"
for f in Raw Nodes1 Nodes2 Values; do
  cmp -s "$out/$f.lean" "slop/Slop/RV/$b/$f.lean" || cp "$out/$f.lean" "slop/Slop/RV/$b/$f.lean"
done
rm -r "$out"
