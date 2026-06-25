# `llzk_backend` Handoff Notes

This document is for future users, agents, and sessions working inside
`zksync-airbender/llzk_backend`.

It captures:
- what the backend does
- how the code is organized
- how to generate and validate outputs
- what is currently supported
- what is still incomplete or fragile

The goal is to make follow-on work faster and to avoid repeating the same false starts.

## Scope

`llzk_backend` lowers circuits from the Airbender/Picus/prover stack into LLZK IR.

It currently supports:
- logical LLZK lowering
- compiled-constraint LLZK lowering
- executor/unrolled circuits
- standalone non-unrolled op harnesses
- several delegation circuits
- bytecode emission for LLZK and PCL-MLIR outputs

It does **not** own the source circuit definitions. It is a backend-only translation layer.

Important project constraint:
- keep changes local to `llzk_backend` when possible
- avoid modifying upstream circuit metadata or circuit crates unless explicitly requested

## Working Rules

Run project commands inside the nix dev shell.

Typical shell wrapper:

```bash
source /nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh
mkdir -p /tmp/nix-cache
XDG_CACHE_HOME=/tmp/nix-cache nix develop -c <command>
```

Examples:

```bash
XDG_CACHE_HOME=/tmp/nix-cache nix develop -c cargo build -p llzk_backend
XDG_CACHE_HOME=/tmp/nix-cache nix develop -c cargo test -p llzk_backend --lib
XDG_CACHE_HOME=/tmp/nix-cache nix develop -c target/debug/llzk_backend gen-all-circuits --output llzk_backend/output --format llzk --debug-location-style file-line-col
XDG_CACHE_HOME=/tmp/nix-cache nix develop -c target/debug/llzk_backend gen-circuit --output llzk_backend/output_bytecode --circuit optimized-decoder --format llzk --emit-bytecode
```

## High-Level Architecture

The main pipeline is:

1. choose a `CircuitRecipe`
2. build a `CircuitOutput` and explicit LLZK boundary spec
3. optionally compile with the one-row compiler
4. extract witness SSA for `@compute`
5. emit LLZK `struct.def`, `@compute`, and `@constrain`
6. serialize as `.llzk` or PCL

The central entrypoint is:
- [`src/lib.rs`](src/lib.rs)

CLI entrypoint:
- [`src/main.rs`](src/main.rs)

### Main types

`CircuitGenerationConfig`
- top-level generation options
- used by both `gen-circuit` and `gen-all-circuits`
- also controls text vs bytecode emission for MLIR-based formats

`CircuitRecipe`
- one recipe per supported circuit family
- includes name, build kind, and build function

`CircuitBuildKind`
- determines which one-row compiler entrypoint is used
- variants:
  - `ExecutorPreprocessedBytecode`
  - `PlainCircuit`
  - `Delegation`

`CircuitBundle`
- final lowering bundle that owns:
  - `CircuitOutput`
  - compiled artifact
  - boundary spec
  - witness computation

## File Guide

### `src/main.rs`

User-facing CLI.

Important responsibilities:
- enumerates all supported circuit names in `Circuits`
- maps enum values to `recipes::*_recipe()`
- exposes:
  - `gen-circuit`
  - `gen-all-circuits`

If a new circuit recipe exists but the CLI does not recognize it, check this file first.

This has already bitten us with `keccak_special5_delegation`: the recipe existed while the enum wiring was commented out.

### `src/lib.rs`

Top-level generation orchestration.

Important responsibilities:
- build recipe
- select compiler path based on `CircuitBuildKind`
- create `WitnessComputation`
- build and emit `CircuitBundle`
- write output files

Bytecode output:
- `--emit-bytecode` is supported for:
  - `--format llzk`
  - `--format pcl-mlir`
- it is rejected for:
  - `--format pcl`
- directory outputs use:
  - `.llzk.bc`
  - `.mlir.bc`

Compiler dispatch currently works as:
- `ExecutorPreprocessedBytecode`
  - `compile_executor_circuit_assuming_preprocessed_bytecode(...)`
- `PlainCircuit`
  - logical mode: uses `empty_compiled_artifact(...)`
  - compiled mode:
    - stateless plain circuits use `compile_stateless_circuit(...)`
    - memory/shuffle-bearing plain circuits use `compile_output_for_chunked_memory_argument(...)`
- `Delegation`
  - `compile_to_evaluate_delegations(...)`

Standalone plain-circuit compiled mode now covers the full in-scope corpus, including:
- `optimized_decoder`
- standalone arithmetic/binop/shift/mop/jump/mul/div recipes
- `csrrw_op`
- `load_op`
- `store_op`

### `src/recipes.rs`

Recipe definitions and boundary-construction logic.

This file is the main place to add support for a new circuit family.

It contains:
- unrolled/executor recipes
- standalone op recipes
- delegation recipes
- boundary spec extraction logic for circuits that do not have `executor_machine_state`

Key idea:
- non-executor circuits use backend-local explicit boundary specs
- do not try to infer everything from `executor_machine_state`

When adding new circuits:
- add a build function
- add a recipe function
- if needed, add a boundary helper
- then wire the recipe into `main.rs`

### `src/codegen.rs`

Owns LLZK module emission.

This is the most important lowering file.

It handles:
- struct layout
- input/output/internal member extraction
- usage-based intermediate extraction
- compiled storage layout
- compiled logical/column bridges
- `@constrain` generation for both logical and compiled modes

Important current behaviors:
- logical mode can switch between ordinary constraints and Picus `parallel_constraints`
- compiled mode uses compiled degree-1 and degree-2 constraints
- compiled mode keeps the public ABI logical but introduces private dense compiled arrays
- unused logical variables are classified backend-locally

Key concepts in this file:

`LlzkBoundarySpec`
- backend-local explicit boundary description
- used for standalone ops and delegations

`UnusedVariablePolicy`
- `warn`, `error`, `ignore`

Unused variable emission:
- `--emit-suspicious-unused` keeps them declared for compatibility/debugging
- emitting them does **not** make them live

Current usage-based extraction rule:
- inputs/outputs are explicit
- intermediates are extracted only if they are logically live
- compiled mappings do not by themselves make a logical variable live

### `src/witness.rs`

Lowers witness SSA into LLZK `@compute`.

Responsibilities:
- replay witness SSA order
- lower lookup evaluation
- lower runtime/oracle hooks
- mirror writes into logical members and compiled columns

This file is where most `@compute` bugs show up.

Past issues fixed here:
- register-valued outputs were using destination read-modify-write and introducing fake self-dependencies
- aggregate arrays are now built more cleanly
- compiled bridging writes now keep logical and compiled storage aligned
- keccak permutation index tables are now supported

If logical generation fails during `@compute`, this file is usually the first place to inspect.

### `src/lookups.rs`

Logical lookup lowering for `@constrain`.

Responsibilities:
- translate `LookupQuery` semantics table-by-table
- model safe conditional/disjunctive dispatch
- emit LLZK-level constraints for table semantics

This file is where missing table support usually causes logical generation failures.

Recent notable addition:
- support for:
  - `KeccakPermutationIndices12`
  - `KeccakPermutationIndices34`
  - `KeccakPermutationIndices56`

### `src/constraints.rs`

General expression and constraint lowering used in `@constrain`.

Includes:
- algebraic expression lowering
- access lowering for variables
- lookup query integration
- boolean/range-check machinery

### `src/builder.rs`

LLZK builder helpers.

This wraps common IR-building tasks:
- felt ops
- array ops
- struct ops
- semantic debug locations
- conditional equality helpers

Important detail:
- semantic locations use synthetic `llzk://...` paths
- these are for analyzer correlation, not real source navigation

### `src/config.rs`

All generation configuration enums live here.

Important knobs:
- `ConstraintLoweringMode::{Logical, Compiled}`
- `LlzkStructLayout`
- `DebugLocationStyle`
- `UnusedVariablePolicy`

### `src/keccak_tables.rs`

Shared helper for keccak permutation-index lookup tables.

Added to avoid duplicating the table semantics in both:
- `lookups.rs`
- `witness.rs`

Use this pattern again if a future table is:
- deterministic
- total
- small enough to share in a local pure helper

## Current Coverage

### Unrolled/executor families

Supported in logical and compiled modes:
- `add_sub_lui_auipc_mop`
- `jump_branch_slt`
- `load_store_subword_only`
- `load_store_word_only`
- `mul_div`
- `shift_binary_csr`
- `unified_reduced_machine`

### Standalone non-unrolled ops

Supported logically:
- `add_op`
- `sub_op`
- `lui_op`
- `auipc_op`
- `xor_op`
- `or_op`
- `and_op`
- `sll_op`
- `srl_op`
- `sra_op`
- `addmod_op`
- `submod_op`
- `mulmod_op`
- `conditional_op`
- `jump_op_trusted`
- `jump_op_untrusted`
- `mul_op_signed`
- `mul_op_unsigned_only`
- `divrem_op_signed`
- `divrem_op_unsigned_only`
- `csrrw_op`
- `load_op`
- `store_op`

Compiled-mode support for standalone plain circuits is now landed for the full in-scope set:
- `optimized_decoder`
- all standalone non-unrolled op recipes currently exposed by the backend

### Delegations

Currently supported:
- `bigint_with_control_delegation`
- `blake2_with_extended_control_delegation`
- `keccak_special5_delegation`

Still out of scope:
- `blake2_single_round` (deprecated)

### Decoder standalone circuit

Currently supported in logical and compiled modes:
- `optimized_decoder`

## Known Blockers

### 1. Standalone compiled path is no longer the main blocker

The standalone compiled path now works for the full in-scope plain-circuit corpus.

Key fixes that made that work:
- stateless plain circuits bypass the old executor-style shuffle/layout invariant
- non-constant lookup table IDs are accepted in the stateless compiled path
- standalone `mul` / `divrem` harnesses now materialize the fixed tables required by the compiler
- standalone memory recipes now satisfy chunked-memory assumptions around:
  - `3` shuffle-RAM queries
  - variable-backed `is_register`
  - witness-SSA boundary ownership for query values vs derived metadata
  - empty executor-style `public_inputs`
  - odd 16-bit range-check packing
  - preserving public outputs from `OptimizedOut(..)` in standalone chunked-memory compilation

Delegations use a different compiled path and remain unaffected by those standalone fixes.

## Important Historical Fixes

These are worth knowing because they explain some odd-looking code in the backend.

### Compiled-mode logical/compiled bridges

Compiled mode originally constrained only compiled columns and left logical/public members floating.

This caused:
- `underconstrained-outputs`
- `unused-fields`
- `unconstrained-signals`

The fix was:
- explicit bridges from logical members to compiled columns
- explicit bridges from explicit LLZK inputs to compiled columns

This logic lives in `codegen.rs`.

### Sparse compiled storage

Compiled private arrays used to be dense full-width mirrors of the compiled artifact layouts.

This caused dead-slot noise in analyzers.

Current behavior:
- compiled storage is remapped densely to only actually used witness/memory columns

This logic also lives in `codegen.rs`.

### Usage-based extraction

Intermediate extraction used to sweep `0..num_of_variables` and emit all non-I/O vars.

That created stale `internal_var_*` members which were never actually used.

Current behavior:
- variable extraction is usage-based
- suspicious-unused variables can still be emitted optionally

This is also in `codegen.rs`.

### Keccak permutation lookup support

`keccak_special5_delegation` originally failed because both:
- `lookups.rs`
- `witness.rs`

panicked on:
- `KeccakPermutationIndices12`
- `KeccakPermutationIndices34`
- `KeccakPermutationIndices56`

Support is now implemented through `src/keccak_tables.rs`.

### Optimized decoder lookup support

`optimized_decoder` originally failed in two places:
- witness SSA extraction did not mark the instruction input limbs as externally assigned
- LLZK lookup lowering did not support:
  - `QuickDecodeDecompositionCheck4x4x4`
  - `QuickDecodeDecompositionCheck7x3x6`
  - `OpTypeBitmask`

Current behavior:
- quick-decode tables are lowered as width/range checks in `lookups.rs`
- `OpTypeBitmask` gets a coarse constrain-side summary in `lookups.rs`
- compute-side `OpTypeBitmask` evaluation uses the private runtime hook `read_op_type_bitmask`

This is enough for logical LLZK generation of `optimized_decoder`.

## Recommended Validation Workflow

### Basic backend validation

```bash
source /nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh
mkdir -p /tmp/nix-cache
XDG_CACHE_HOME=/tmp/nix-cache nix develop -c cargo build -p llzk_backend
```

If you need tests:

```bash
XDG_CACHE_HOME=/tmp/nix-cache nix develop -c cargo test -p llzk_backend --lib
```

### Generate one circuit

```bash
XDG_CACHE_HOME=/tmp/nix-cache nix develop -c \
  target/debug/llzk_backend gen-circuit \
  --output llzk_backend/output_probe \
  --circuit optimized-decoder \
  --format llzk \
  --debug-location-style file-line-col \
  --constraint-lowering-mode logical
```

Compiled mode:

```bash
XDG_CACHE_HOME=/tmp/nix-cache nix develop -c \
  target/debug/llzk_backend gen-circuit \
  --output llzk_backend/output_probe_compiled \
  --circuit optimized-decoder \
  --format llzk \
  --debug-location-style file-line-col \
  --constraint-lowering-mode compiled
```

### Generate all circuits

Logical:

```bash
XDG_CACHE_HOME=/tmp/nix-cache nix develop -c \
  target/debug/llzk_backend gen-all-circuits \
  --output llzk_backend/output \
  --format llzk \
  --debug-location-style file-line-col \
  --constraint-lowering-mode logical
```

Compiled:

```bash
XDG_CACHE_HOME=/tmp/nix-cache nix develop -c \
  target/debug/llzk_backend gen-all-circuits \
  --output llzk_backend/output_compiled \
  --format llzk \
  --debug-location-style file-line-col \
  --constraint-lowering-mode compiled
```

Expectation today:
- logical all-circuits should succeed for all currently supported circuits
- compiled all-circuits still may stop on standalone plain-circuit recipes

## Common Failure Modes

### “unsupported lookup table in LLZK lookup lowering”

Cause:
- missing case in `lookups.rs`

Fix:
- add table semantics to `add_lookup_constraints_for_table(...)`

### “unsupported lookup table in @compute”

Cause:
- missing case in `witness.rs`

Fix:
- add table semantics to `compute_lookup_for_table(...)`

Always update both sides if the table appears in both logical and witness paths.

### Circuit exists in recipes but CLI rejects it

Cause:
- missing or commented-out enum variant in `main.rs`

Fix:
- add the `Circuits` variant
- add the `match` arm in `Circuits::recipe()`
- rebuild before retrying

### Generation still seems to use an old binary

Cause:
- running `target/debug/llzk_backend` before the rebuild has completed

Fix:
- wait for `cargo build -p llzk_backend` to fully finish
- then rerun generation

This caused confusion more than once with the keccak delegation work.

## How to Add a New Circuit

### New standalone or delegation recipe

1. Implement a build function in `recipes.rs`
2. Build:
   - `CircuitOutput`
   - explicit boundary spec
   - witness SSA
3. Add a `*_recipe()` function
4. Wire it into `main.rs`
5. Validate logical generation first
6. Then validate compiled generation if the compiler path supports that recipe kind

### New lookup table support

1. Find the source table semantics in `cs/src/tables/...` or circuit code
2. Add constrain-side lowering in `lookups.rs`
3. Add compute-side emulation in `witness.rs`
4. If the table semantics are total and deterministic, consider putting the shared logic in a small helper module like `keccak_tables.rs`
5. Validate the target circuit directly before attempting `gen-all-circuits`

## Current Recommendations for Follow-on Work

Most promising next items:

1. Regenerate full logical and compiled corpora with the current backend
2. Keep `blake2_single_round` out of scope unless the upstream deprecation status changes

Order recommendation:
- rerun full generation
- then expand circuit coverage further

## Quick Status Snapshot

As of this handoff:
- `keccak_special5_delegation` generates in both logical and compiled modes
- `optimized_decoder` generates in both logical and compiled modes
- standalone logical coverage is broad
- compiled coverage includes the full in-scope standalone plain-circuit corpus
