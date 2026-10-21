#!/usr/bin/env bash
# One-command check: fetch the pinned lean-sail, require the generated Sail model, build the spec and every proof,
# check that the spec does not depend on the proofs, run the regressions and the axiom audits (standard axioms only), check the review guides.
set -euo pipefail
cd "$(dirname "$0")/lean"
fail() { echo "FAIL: $*"; exit 1; }

echo "== 0. The Sail model: lean-sail (pinned, fetched on demand; not committed), then the generated model"
../sail/fetch-lean-sail.sh
[[ -f sail-rv32/SailRV32.lean && -d sail-rv32/SailRV32 ]] ||
  fail "the generated Sail model is absent: run sail/regen.sh (needs the pinned Sail compiler; see sail/PINS.md)"

echo "== 1. The spec (human/) imports nothing from the proofs (slop/) or the tests (test/)"
if grep -rnE '^\s*(public\s+)?import\s+(Slop|Tests|Checks)(\.|$)' human; then fail "human/ imports slop/ or test/"; fi

echo "== 2. Lean build (spec + proofs + importer)"
lake build Human Slop airbender_import 2>&1 | tail -1

echo "== 3. Regressions; final statements (each slop/Slop/Final theorem proves its human/ ...Claim, test/Checks/Claims.lean); axiom audits"
lake build Test airbender_tests 2>&1 | tail -1
lake exe airbender_tests
for audit in Claims Axioms TraceAxioms; do
  out=$(lake env lean "test/Checks/$audit.lean")
  # Lean wraps long axiom lists over several lines: join before matching
  lists=$(tr '\n' ' ' <<<"$out" | grep -oE "depends on axioms: \[[^]]*\]" | tr -s ' ' || true)
  n=$(( $(grep -c . <<<"$lists" || true) + $(grep -c "does not depend on any axioms" <<<"$out" || true) ))
  bad=$(grep -vE "^depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]$" \
    <<<"$lists" || true)
  [[ -z "$bad" ]] || { echo "$bad"; fail "non-standard axioms ($audit)"; }
  echo "$audit: $n theorems, standard axioms only"
done

echo "== 4. Review guides: every public claim theorem is audited, guide names and links resolve"
python3 check_review.py

echo "OK"
