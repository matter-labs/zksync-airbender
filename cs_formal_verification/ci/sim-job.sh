#!/usr/bin/env bash
# Inside the container (ci/sim.sh): the workflow's steps in order, with actions/cache simulated by zstd tarballs in
# /store (a named volume). Arguments: <restore build cache from label> <save build cache as label> (either may be "-").
# The source is /in/src.tar (git archive of the commit under test), unpacked into /w like actions/checkout.
set -euo pipefail
from=${1:--}; to=${2:--}
STORE=/store
mkdir -p "$STORE" /w
cd /w
export FV_DIR=/w/cs_formal_verification
CI=/opt/fvci/lean-ci.sh   # this checkout's ci/lean-ci.sh as mounted by ci/sim.sh (older commits have none)
T() { "$CI" time "$@"; }
restore() { # name dir
  [[ -f "$STORE/$1.tar.zst" ]] || { echo "cache miss: $1"; return 1; }
  local t0=$(date +%s); zstd -dc -T0 "$STORE/$1.tar.zst" | tar -xf - -C "$2"
  echo "cache hit: $1 ($(du -h "$STORE/$1.tar.zst" | cut -f1), restored in $(( $(date +%s) - t0 )) s)"
}
save() { # name dir paths...
  local name=$1 dir=$2; shift 2
  local t0=$(date +%s)
  (cd "$dir" && tar -cf - --ignore-failed-read "$@" 2>/dev/null) | zstd -q -T0 -3 -o "$STORE/$name.tar.zst.tmp" -f
  mv "$STORE/$name.tar.zst.tmp" "$STORE/$name.tar.zst"
  echo "cache saved: $name ($(du -h "$STORE/$name.tar.zst" | cut -f1), in $(( $(date +%s) - t0 )) s)"
}

df -h / | tail -1 | awk '{print "disk at start: used " $3 " of " $2}'
echo "== checkout"
t0=$(date +%s)
tar -xf /in/src.tar -C /w
git init -q && git add -A && git -c user.email=ci@local -c user.name=ci commit -qm src
echo "checkout: $(( $(date +%s) - t0 )) s"
FV=/w/cs_formal_verification
L=$FV/lean
marker=/tmp/job-start; touch "$marker"

echo "== elan (cache: elan-<toolchain>)"
ekey="elan-$(tr ':/' '__' < "$L/lean-toolchain")"
restore "$ekey" / || { T elan; save "$ekey" / root/.elan; }
"$CI" elan >/dev/null 2>&1   # no-op on a hit; puts nothing new on PATH

echo "== sail model (cache: sail-<inputs hash>)"
skey="sail-$("$CI" sail-key)"
restore "$skey" "$L/sail-rv32" || { T sail-deps; T sail-gen; save "$skey" "$L/sail-rv32" SailRV32 SailRV32.lean; }
T lean-sail
[[ "${FVCI_STOP:-}" == sail ]] && { echo "JOB stopped after the sail model (FVCI_STOP=sail)"; exit 0; }

echo "== Mathlib cache (downloads cached: mathlib-<manifest hash>)"
mkey="mathlib-$(sha256sum "$L/lake-manifest.json" | cut -c1-16)"
mkdir -p /root/.cache/mathlib "$L/.lake/packages"
mhit=0; restore "$mkey" /root/.cache/mathlib && mhit=1
# the dependencies' git checkouts (sources and .git, no build outputs): without them Lake clones Mathlib (0.5 GB of
# history) and the rest on every run
pkey="packages-$(sha256sum "$L/lake-manifest.json" | cut -c1-16)"
phit=0; restore "$pkey" "$L/.lake/packages" && phit=1
T mathlib
(( mhit )) || save "$mkey" /root/.cache/mathlib .
(( phit )) || save "$pkey" "$L/.lake/packages" --exclude='./*/.lake' .

echo "== Lake build cache (restore: $from)"
[[ "$from" == "-" ]] || restore "build-$from" "$L" || true

echo "== dependencies (Sail model, Clean imports, the test executable's dependency objects)"
T lean-deps

echo "== verify.sh (VERIFY_AUDITS=${VERIFY_AUDITS:-fresh})"
set +e; T verify; rc=$?; set -e
if [[ "${FVCI_KERNEL:-0}" == 1 && $rc == 0 ]]; then
  echo "== kernel replay (leanchecker)"
  set +e; T kernel-check; rc=$?; set -e
fi
"$CI" report "$marker"

if [[ "$to" != "-" ]]; then
  echo "== save build cache as $to"
  (cd "$L" && find .lake/packages -path '*/.lake/build/ir/*' -name '*.c.o*' > /tmp/dep-objects)
  save "build-$to" "$L" .lake/build .lake/module-cpu.tsv sail-rv32/.lake .lake/packages/Clean/.lake -T /tmp/dep-objects
fi
du -sh /root/.elan /root/.cache/mathlib "$L/.lake/packages" "$L/.lake/build" "$L/sail-rv32/.lake" "$FV/build" 2>/dev/null || true
df -h / | tail -1 | awk '{print "disk at end: used " $3 " of " $2}'
echo "JOB rc=$rc"
exit "$rc"
