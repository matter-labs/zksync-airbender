#!/usr/bin/env bash
# One-command check: rebuild the binary, check the Lean copy of it, check every proof, check the final theorem's
# statement and axioms. Everything generated must be identical to what is committed.
set -euo pipefail
cd "$(dirname "$0")"

echo "== 0. lean-sail (pinned, fetched on demand; not committed)"
sail/fetch-lean-sail.sh

echo "== 1. Rust build (deterministic, both variants) + Lean images"
(cd rust && ./build.sh >/dev/null 2>&1)
git diff --exit-code -- build/app.sha256 build/app_mop.sha256 lean/image/Image.lean lean/image/ImageMop.lean \
  || { echo "FAIL: a binary or Image*.lean differs from the committed one"; exit 1; }
cat build/app.sha256 build/app_mop.sha256

echo "== 2. Generated decode lemmas / code lists"
lean/gen/words.sh
git add -N lean/slop/Slop/RV/Code
git diff --exit-code -- lean/slop/Slop/RV/Code || { echo "FAIL: generated code files are stale"; exit 1; }

echo "== 3. Lean build (spec + proofs)"
(cd lean && lake build Human Slop.RV.FinalPlain Slop.RV.FinalMop Slop.Deleg 2>&1 | grep -E "error|Build completed" )

echo "== 4. Final theorems (plain-Rust image, field-opcode image) and delegation runs: statements and axioms"
thms=("program_correct : RV.ProgramCorrect" "program_correct_mop : RV.ProgramCorrectMop"
  "blake_compress_run : RV.BlakeCompressRun" "blake_hash_run : RV.BlakeHashRun" "blake_g_run : RV.BlakeGRun")
out=$(cd lean && { printf 'import Slop.RV.FinalPlain\nimport Slop.RV.FinalMop\nimport Slop.Deleg\n'
  for t in "${thms[@]}"; do printf '#check (RV.%s : %s)\n#print axioms RV.%s\n' "${t%% *}" "${t##* }" "${t%% *}"; done
  } | lake env lean --stdin)
echo "$out"
for t in "${thms[@]}"; do
  echo "$out" | grep -q "^RV.$t$" || { echo "FAIL: statement $t"; exit 1; }
  echo "$out" | grep -q "'RV.${t%% *}' depends on axioms: \[propext, Classical.choice, Quot.sound\]$" \
    || { echo "FAIL: unexpected axioms (${t%% *})"; exit 1; }
done
echo "== 5. Our spec vs Sail (needs the generated Sail model: sail/regen.sh)"
if [[ -d lean/sail-rv32/SailRV32 ]]; then
  out=$(cd lean && lake build HumanSail Slop.Sail.Config Slop.Equiv.Decode Slop.Equiv.Final 2>&1 \
    | grep -E "error|Build completed" ; lake env lean --stdin <<'LEAN'
import Slop.Equiv.Decode
import Slop.Equiv.Final
#check (Slop.Equiv.decode_is_sail : Airbender.DecodeIsSail)
#print axioms Slop.Equiv.decode_is_sail
#check (Slop.Equiv.step_is_airbender : Airbender.StepIsAirbender)
#print axioms Slop.Equiv.step_is_airbender
#check (Slop.Equiv.program_correct_airbender : Airbender.ProgramCorrect)
#print axioms Slop.Equiv.program_correct_airbender
#check (Slop.Equiv.program_correct_airbender_mop : Airbender.ProgramCorrectMop)
#print axioms Slop.Equiv.program_correct_airbender_mop
LEAN
)
  echo "$out"
  echo "$out" | grep -q "^Slop.Equiv.decode_is_sail : Airbender.DecodeIsSail$" || { echo "FAIL: DecodeIsSail"; exit 1; }
  echo "$out" | grep -q "decode_is_sail' depends on axioms: \[propext, Classical.choice, Quot.sound\]$" \
    || { echo "FAIL: unexpected axioms (DecodeIsSail)"; exit 1; }
  echo "$out" | grep -q "^Slop.Equiv.step_is_airbender : Airbender.StepIsAirbender$" \
    || { echo "FAIL: StepIsAirbender"; exit 1; }
  echo "$out" | grep -q "step_is_airbender' depends on axioms: \[propext, Classical.choice, Quot.sound\]$" \
    || { echo "FAIL: unexpected axioms (StepIsAirbender)"; exit 1; }
  echo "$out" | grep -q "^Slop.Equiv.program_correct_airbender : Airbender.ProgramCorrect$" \
    || { echo "FAIL: Airbender.ProgramCorrect"; exit 1; }
  echo "$out" | grep -q "program_correct_airbender' depends on axioms: \[propext, Classical.choice, Quot.sound\]$" \
    || { echo "FAIL: unexpected axioms (Airbender.ProgramCorrect)"; exit 1; }
  echo "$out" | grep -q "^Slop.Equiv.program_correct_airbender_mop : Airbender.ProgramCorrectMop$" \
    || { echo "FAIL: Airbender.ProgramCorrectMop"; exit 1; }
  echo "$out" | grep -q "program_correct_airbender_mop' depends on axioms: \[propext, Classical.choice, Quot.sound\]$" \
    || { echo "FAIL: unexpected axioms (Airbender.ProgramCorrectMop)"; exit 1; }
  sail_ok=1
else
  echo "skipped: no generated Sail model (run sail/regen.sh)"
fi


echo "== 6. Sanity (not a proof): run both images on the RV32 spec for a few inputs"
(cd lean && lake build run_image >/dev/null && lake exe run_image)
echo "OK: the images at build/app.bin, build/app_mop.bin satisfy RV.ProgramCorrect, RV.ProgramCorrectMop (lean/human/Human/Theorems.lean)"
if [[ -n "${sail_ok:-}" ]]; then
  echo "OK: and Airbender.ProgramCorrect, Airbender.ProgramCorrectMop on the Sail-based Airbender machine (lean/human/HumanSail/Theorems.lean)"
fi
