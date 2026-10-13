#!/usr/bin/env bash
# One-command check: rebuild the binary, check the Lean copy of it, check every proof, check the final theorem's
# statement and axioms. Everything generated must be identical to what is committed.
set -euo pipefail
cd "$(dirname "$0")"

echo "== 1. Rust build (deterministic) + Lean image"
(cd rust && ./build.sh >/dev/null 2>&1)
git diff --exit-code -- build/app.sha256 lean/image/Image.lean \
  || { echo "FAIL: binary or Image.lean differs from the committed one"; exit 1; }
cat build/app.sha256

echo "== 2. Generated decode lemmas / code lists"
lean/gen/words.sh
git add -N lean/slop/Slop/RV/Code
git diff --exit-code -- lean/slop/Slop/RV/Code || { echo "FAIL: generated code files are stale"; exit 1; }

echo "== 3. Lean build (spec + proofs)"
(cd lean && lake build Human Slop.RV.Final 2>&1 | grep -E "error|Build completed" )

echo "== 4. Final theorem: statement and axioms"
out=$(cd lean && lake env lean --stdin <<'LEAN'
import Slop.RV.Final
#check (RV.program_correct : RV.ProgramCorrect)
#print axioms RV.program_correct
LEAN
)
echo "$out"
echo "$out" | grep -q "^RV.program_correct : RV.ProgramCorrect$" || { echo "FAIL: statement"; exit 1; }
echo "$out" | grep -q "depends on axioms: \[propext, Classical.choice, Quot.sound\]$" \
  || { echo "FAIL: unexpected axioms"; exit 1; }
echo "== 5. Sanity (not a proof): run the image on the RV32 spec for a few inputs"
(cd lean && lake build run_image >/dev/null && lake exe run_image)
echo "OK: the image at build/app.bin satisfies RV.ProgramCorrect (lean/human/Human/Theorems.lean)"
