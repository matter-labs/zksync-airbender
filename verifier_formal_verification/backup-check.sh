#!/usr/bin/env bash
# Backup checker (rare; not part of verify.sh): replay every declaration of human/ and slop/ through a second, fresh
# Lean kernel with `leanchecker`, which ships with the toolchain pinned in lean/lean-toolchain. It catches anything a
# tactic or metaprogram might have added without the kernel. Slow (tens of minutes): run it only at major
# milestones, e.g. before tagging or publishing a result, not per commit.
#   ./backup-check.sh           # our modules, on top of their (trusted) imports
#   ./backup-check.sh --fresh   # also replay all imports, Mathlib and Sail included (much longer)
set -euo pipefail
cd "$(dirname "$0")/lean"

ROOTS=(Human HumanSail Slop Slop.RV.FinalPlain Slop.RV.FinalMop Slop.Equiv.Decode Slop.Equiv.Final Slop.Deleg)
echo "== build (the checker reads the compiled .olean files)"
lake build "${ROOTS[@]}" 2>&1 | grep -E "error|Build completed"

if [[ "${1:-}" == "--fresh" ]]; then
  for r in Slop.RV.FinalPlain Slop.RV.FinalMop Slop.Equiv.Final Slop.Deleg; do
    echo "== --fresh $r"; lake env leanchecker --fresh "$r"
  done
else
  # the checker covers only the modules it is given, so list every module; it is single-threaded, so run batches of
  # 10 modules on up to JOBS cores at once (each batch prints when it passes; any failure stops the run)
  JOBS="${JOBS:-6}"
  { cd human && find . -name '*.lean'; cd ../slop && find . -name '*.lean'; } | sed 's#^\./##; s#\.lean$##; s#/#.#g' \
    | sort | xargs -n 10 -P "$JOBS" sh -c 'lake env leanchecker "$@" && echo "ok ($(date +%H:%M:%S)): $1 … ($# modules)"' _
fi
echo "OK: the backup checker accepted every declaration"
