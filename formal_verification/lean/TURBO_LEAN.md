# Lean 4.35 and turbo-lean experiment

Branch: `codex/lean-turbo-upgrade`.
Fork: `100c270a0ec1837701e7b0bf2b7385e5cdee2cab`.
The original branch and PR #585 keep Lean 4.31 and their build caches.

## Current state

Lean and Mathlib target version 4.35.0.
The dependency lock resolves with that toolchain.
All 52 source generator checks pass.
The Clean and lean-sail reference revisions stay unchanged.
The existing hash-checked Clean compatibility patches remain.
The proof port and runtime measurements are pending.
The earlier proof and validation reports describe Lean 4.31.

Turbo-lean is pinned to commit
`2896cfd092758b8d0fc9977502dc036b0ab79921`.
Its source, binary and cache stay in this worktree's ignored `.lake/turbo-lean/`.
The launcher disables telemetry, daemons and automatic worktree cache links.
Its axiom policy adds no axioms to `propext`, `Classical.choice` and `Quot.sound`.
The official frontend, axiom audit and transitive kernel replay remain required.
Turbo receipts do not replace those gates.

## Trial

Use a free verification worker. Keep the existing validation runs active.
Install the pinned tool under the resource guard:

```sh
python3 scripts/bounded_fv.py --mib 2560 --resident-mib 5120 --seconds 900 \
  --log /tmp/airbender-turbo-install.log -- bash scripts/turbo_lean.sh install
```

After the port builds, select an existing checker module:

```sh
bash scripts/turbo_lean.sh check Airbender/Proofs/Tables/FiniteGridChecks.lean \
  --project-dir . --jobs 1 --timeout 900 --kernel standard
```

Measure cold builds and warm proof edits separately.
Compare stock Lean 4.35 and turbo-lean on the same source and imports.
Report time, peak memory, cache state and checked declarations.
Keep target statements, imported data and exact matching premises unchanged.
Use the official kernel to check every accepted proof result.

Sources: [turbo-lean](https://github.com/Th0rgal/turbo-lean/tree/2896cfd092758b8d0fc9977502dc036b0ab79921),
[Lean 4.35](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/).
