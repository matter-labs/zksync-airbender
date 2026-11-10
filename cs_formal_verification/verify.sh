#!/usr/bin/env bash
# One-command check: fetch the pinned lean-sail, require the generated Sail model, build the spec and every proof,
# check that the spec does not depend on the proofs, run the regressions and the axiom audits (standard axioms only),
# check every module's build budget (30 s of CPU), check that our code builds without warnings, check the review guides.
set -euo pipefail
cd "$(dirname "$0")/lean"
fail() { echo "FAIL: $*"; exit 1; }
# Clean (v4.35.0) asks Lake to download its GitHub release's prebuilt .olean files; build it from source instead.
export LAKE_NO_CACHE=${LAKE_NO_CACHE:-1}

echo "== 0. The Sail model: lean-sail (pinned, fetched on demand; not committed), then the generated model"
../sail/fetch-lean-sail.sh
[[ -f sail-rv32/SailRV32.lean && -d sail-rv32/SailRV32 ]] ||
  fail "the generated Sail model is absent: run sail/regen.sh (needs the pinned Sail compiler; see sail/PINS.md)"

echo "== 1. The spec (human/) imports nothing from the proofs (slop/) or the tests (test/)"
if grep -rnE '^\s*(public\s+)?import\s+(Slop|Tests|Checks)(\.|$)' human; then fail "human/ imports slop/ or test/"; fi

echo "== 1b. The circuit JSONs the spec imports: pinned sha256, no duplicate keys, no duplicate circuits"
python3 check_circuit_json.py

echo "== 2. Lean build (spec + proofs), timing each module compiled (full log: lean/.lake/verify-build-*.log)"
python3 scripts/module_budget.py build CleanCore CleanEquivalence Human Slop || fail "lake build"

echo "== 3. Regressions; final statements (each slop/Slop/Final theorem proves its human/ ...Claim, test/Checks/Claims.lean); axiom audits"
python3 scripts/module_budget.py build Test CleanAudit airbender_tests || fail "lake build (tests)"
lake exe airbender_tests
# VERIFY_AUDITS=fresh (default): elaborate each audit file again. replay (CI pull requests): read the messages Lake
# logged for the audit modules in the build above (built now, or replayed from their traces: the same trust as the
# cached .olean files they import). Either way every `#print axioms` must be answered.
audits=${VERIFY_AUDITS:-fresh}
[[ $audits == fresh || $audits == replay ]] || fail "VERIFY_AUDITS must be fresh or replay"
for audit in Claims Axioms TraceAxioms; do
  if [[ $audits == replay ]]; then
    out=$(python3 scripts/audit_log.py .lake/verify-build-Test.log "test/Checks/$audit.lean")
  else
    out=$(lake env lean "test/Checks/$audit.lean")
  fi
  # Lean wraps long axiom lists over several lines: join before matching
  lists=$(tr '\n' ' ' <<<"$out" | grep -oE "depends on axioms: \[[^]]*\]" | tr -s ' ' || true)
  n=$(( $(grep -c . <<<"$lists" || true) + $(grep -c "does not depend on any axioms" <<<"$out" || true) ))
  bad=$(grep -vE "^depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]$" \
    <<<"$lists" || true)
  [[ -z "$bad" ]] || { echo "$bad"; fail "non-standard axioms ($audit)"; }
  want=$(grep -c '^#print axioms' "test/Checks/$audit.lean")
  [[ $n -eq $want ]] || fail "$audit: $n axiom reports for $want #print axioms ($audits; a restored build has no logs: VERIFY_AUDITS=fresh)"
  echo "$audit: $n theorems, standard axioms only ($audits)"
done

echo "== 4. Module budget: every module compiles in at most 30 s of CPU, alone (scripts/module_budget.py;"
echo "   docs/shared/lean-strategies.md 2). Table: lean/.lake/module-budget.tsv"
python3 scripts/module_budget.py check || fail "module budget"

echo "== 4b. No warnings: Lean and Lake report no warning for any module of ours (human/, slop/, test/;"
echo "   scripts/no_warnings.py, README \"No warnings\"); dependencies and the generated Sail model are not ours"
python3 scripts/no_warnings.py .lake/verify-build-CleanCore.log .lake/verify-build-Test.log || fail "warnings in our code"

echo "== 5. Review guides: every public claim theorem is audited, guide names and links resolve"
# replay (CI pull requests): the Lean part is skipped when its inputs (guides, audit file, the claim modules' Lake input
# hashes) equal those of the last passing check, recorded in the build directory; links and layers are always checked
# --built: steps 2 and 3 built every claim module and the audit module it imports
if [[ $audits == replay ]]; then python3 check_review.py --built --key .lake/build/review-pass.key --reuse
else python3 check_review.py --built --key .lake/build/review-pass.key; fi

echo "OK"
