# Lean 4.35 and turbo-lean experiment

Branch: `codex/lean-turbo-upgrade`.
Fork: `100c270a0ec1837701e7b0bf2b7385e5cdee2cab`.
PR #585 keeps Lean 4.31 and its separate CI validation.

## Current state

Lean and Mathlib resolve at version 4.35.0.
All 54 generator checks pass.
The Clean and lean-sail reference revisions stay unchanged.
The hash-checked Clean compatibility patches apply.
Stock Lean builds the numeric query-frame checker and its strict importer.
The complete cached AddSub query-frame certificate also builds.
All 11 cached native witness consumers also build.
Their exact source bindings and original semantic finalizers pass.
The pinned Sail interpreter and RV32 snapshot compile.
The basic RISC-V step, register-read and load proofs also compile.
The decoder-frame and decoded-offset proofs also compile.
Both proofs reuse each shared continuation of the original generated decoder.
The exact latest-read trace predicate also compiles.
The failed table and offline-memory proof modules now compile.
Their compatibility settings stay local to proof declarations.
Controller geometry uses a symbolic index before specializing the native row.
Its recursion and resource limits stay unchanged.
Definitions and theorem statements stay unchanged.
The register-read proofs use explicit reductions of the original state operations.
The compatibility patch annotates the existing natural-number choice binder.
A local syntax adapter uses Sail's original assertion and monad lift.
The original compiler-output hash and all 13 instruction fingerprints stay unchanged.
The port fixes proof reductions and deprecated theorem names.
The Clean patches limit elaborator compatibility settings to affected proofs.
They preserve reference definitions and theorem statements.
Library options disable the new `defProp` style warning for shared proof definitions.
A weak Airbender argument suppresses unused-tactic style checks in inherited proofs.
Other warnings remain errors. Kernel checks stay unchanged.
The full proof port remains unqualified.

Turbo-lean is pinned to `2896cfd092758b8d0fc9977502dc036b0ab79921`.
Its source, binary and cache use this worktree's ignored `.lake/turbo-lean/`.
The launcher disables telemetry, daemons and automatic worktree cache links.
Its axiom policy adds no axioms to `propext`, `Classical.choice` and `Quot.sound`.
The serial `cargo check` and release build pass in 264.39 seconds.
Their aggregate footprint peaks at 1,030.80 MiB.

The pinned tool rejects `lean_lib.needs` in the real Lake configuration.
These dependencies track native artifact freshness. Keep them unchanged.
Direct turbo checks of the whole project are not ready.
The smoke command copies the exact core-only `FiniteGridChecks` source to a
separate temporary project. It checks source and policy hashes after each command.
Stock Lean checks the complete source. Turbo uses its standard kernel.
The source has one proof declaration. The repeat uses its checked cache entry.

| Smoke command | Time (s) | Result |
| --- | ---: | --- |
| Stock Lean 4.35 | 1.45 | Source passes |
| Turbo with an empty theorem cache | 2.46 | Theorem verified |
| Turbo repeat | 0.84 | Theorem cache hit |

The tool setup was warm for this table. The initial setup trial took 18.37 seconds
for its first turbo check. These tiny checks do not measure cold project builds
or warm proof edits. They establish no whole-project speed gain.
The hardened smoke group takes 5.27 seconds and peaks at 143.08 MiB footprint.
Reports remain in `/tmp/airbender-turbo-2026-11-02/` and the printed smoke directory.

## Commands

The user approved host execution of the pinned tool after the focused review.
The resource guard limits time and memory. It does not isolate the filesystem
or network. The earlier host smoke preceded the focused security review.
That review is not a complete audit of the tool or its dependencies.
The launcher now also clears inherited compiler-simplification exceptions.
The hardened host smoke passes with the recorded pinned binary.

Use one free verification worker:

```sh
python3 scripts/bounded_fv.py --mib 2560 --resident-mib 5120 --seconds 900 \
  --log /tmp/airbender-turbo-install.log -- bash scripts/turbo_lean.sh install
python3 scripts/bounded_fv.py --mib 2560 --resident-mib 5120 --seconds 900 \
  --log /tmp/airbender-turbo-smoke.log -- bash scripts/turbo_lean.sh smoke
```

Continue with the three machine target source builds on Lean 4.35.
Keep target statements, exact imported data and matching premises unchanged.
Resolve the tool's artifact-dependency support before measuring real project edits.
The official frontend, axiom audit and kernel replay remain the adoption gate.
Turbo receipts do not replace those gates.

Sources: [turbo-lean](https://github.com/Th0rgal/turbo-lean/tree/2896cfd092758b8d0fc9977502dc036b0ab79921),
[Lean 4.35](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/).
