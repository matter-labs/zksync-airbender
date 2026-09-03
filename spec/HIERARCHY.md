# Specification hierarchy and profile views

> Durable navigation and migration reference for the proof-system specification.
> This document defines where relations belong and how profiles compose them; it does
> not itself define an accepted proof relation.

- spec revision: TBD
- implementation: TBD
- status: agreed target hierarchy, incremental migration in progress
- current source of truth: the paths linked from [INDEX.md](INDEX.md) until each
  migration step updates that index

## Organizing principle

The specification is component-first and profile-addressable.

- A component directory owns each canonical relation exactly once.
- A component may contain profile-specific variants only when the relation actually
  differs between profiles.
- A profile manifest selects one variant from each applicable component and links to
  its canonical statements.
- The profile manifest does not copy instruction equations, memory arguments, lookup
  relations, recursion transitions, or soundness calculations.
- A profile-specific view may link to shared relations; it does not require a complete
  profile × component matrix.

This provides two complementary ways to read the specification:

1. open a component to compare how that part of the proof system works across
   profiles;
2. open a profile manifest to see the complete configuration selected for one proof
   role.

## Target hierarchy

```text
spec/
├── INDEX.md
├── HIERARCHY.md
├── profiles/
│   ├── INDEX.md
│   ├── base-unrolled-full-unsigned.md
│   ├── recursion-unrolled-reduced.md
│   ├── bridge-unified-reduced.md
│   ├── recursion-unified-reduced.md
│   └── l1-proth120.md
├── isa/
│   ├── INDEX.md
│   ├── unrolled/
│   ├── unified/
│   └── precompiles/
├── execution/
│   ├── INDEX.md
│   ├── unrolled.md
│   └── unified.md
├── memory/
│   ├── INDEX.md
│   ├── common.md
│   ├── init-teardown-unrolled.md
│   └── init-teardown-unified.md
├── lookups/
│   ├── INDEX.md
│   ├── common.md
│   ├── unrolled.md
│   └── unified.md
├── recursion/
└── soundness/
```

The named profile files are the expected first profile manifests. Do not create a
profile subdirectory inside every component or subdivide `recursion/` and
`soundness/` before their contents require it.

## Component ownership

| Component | Canonical responsibility | Profile-specific selection |
|---|---|---|
| `isa` | Instruction transitions, precompile computations, supported-operation sets, and architectural effects | Instruction families, custom operations, precompile admission, and fulfillment relations |
| `execution` | Decoder authentication, register and PC continuity, circuit dispatch, activation, padding, trace segmentation, and chunk cardinality | Unrolled versus unified dispatch, chunk capacity, and the formula for the number of chunks |
| `memory` | ROM/RAM semantics, the global memory argument, initialization, teardown, and final-state closure | Separate initialization/teardown circuit versus initialization/teardown data folded into executor chunks |
| `lookups` | Decoder tables, fixed tables, range checks, timestamp checks, local lookup arguments, and their setup binding | Per-family versus pooled lookup layout and the exact table inventory selected by the executor |
| `recursion` | Base-proof consumption, full-statement verification, recursive continuation, bridge transitions, terminal shape, and L1 acceptance | Which verifier program is proved, its input stream, cycle bound, predecessor proof type, and successor proof type |
| `soundness` | Field assumptions, Fiat–Shamir challenges, GKR/Sumcheck error, WHIR/PCS parameters, lookup and memory-argument error, grinding, and aggregate error budget | A named parameter configuration and any stage-specific deviations |

Decoder semantics belong to `execution`; concrete decoder and fixed-table membership
relations belong to `lookups`. ISA modules state the decoder guarantees they assume but
do not own the decoder implementation.

Precompiles are part of ISA selection. A profile distinguishes carrier admission from
fulfillment-circuit availability, but both remain ISA-level choices. A Blake variant
used to implement a recursive verifier program is represented by selecting that
verifier program under `recursion`, not by inventing another application ISA.

## Profile model

A complete profile is the product of five primary selections plus the lookup layout:

```text
Profile = (
  ISA,
  Execution,
  MemoryBoundary,
  Lookups,
  RecursionRole,
  SoundnessConfiguration,
)
```

Each profile manifest binds these names and links to their owning modules:

```text
ISA        = reduced-unified
Execution  = unified-2²³
Memory     = trailing-unified-init-teardown
Lookups    = unified-pooled-lookups
Recursion  = unified-recursion-layer
Soundness  = babybear-sec100
```

The manifest may add a relation that genuinely exists only at composition time, such
as compatibility between the selected recursion program and execution profile. It
must not restate relations already owned by the selected components.

## Profile data versus proof-instance data

A profile fixes types, capacities, formulas, and accepted variants. A particular
proof supplies the runtime values.

| Profile data | Proof-instance data |
|---|---|
| ISA and precompile inventory | Concrete program and executed operations |
| Trace capacity and chunk-count formula | Actual cycle count and number of chunks |
| Initialization/teardown inclusion method | Touched memory regions and final state |
| Decoder/setup construction method | Program-specific decoder table and setup commitments |
| Recursion program and cycle bound | Concrete predecessor proof and nondeterminism stream |
| Soundness configuration | Sampled transcript challenges and proof messages |

For example, an unrolled profile fixes
`chunks_f = ⌈calls_f / 2²⁴⌉`; the proof instance supplies `calls_f`. A unified profile
fixes `chunks = ⌈cycles / 2²³⌉`; the proof instance supplies `cycles`.

## Initial profile catalog

These rows record the intended profile axes to specify. They are navigation targets,
not a declaration that every relation is already complete.

| Profile | ISA | Execution | Memory boundary | Lookups | Recursion role | Soundness |
|---|---|---|---|---|---|---|
| `base-unrolled-full-unsigned` | Full-unsigned unrolled ISA and its admitted precompiles | Per-family `2²⁴`-row chunks | One separate initialization/teardown proof | Per-family lookup layouts | Application base proof | Named BabyBear security configuration |
| `recursion-unrolled-reduced` | Reduced unrolled ISA and admitted delegations | Per-family `2²⁴`-row chunks | Separate initialization/teardown proof | Per-family lookup layouts | Prove an unrolled base-layer or recursion-layer verifier; bound `2²⁸` cycles | Named BabyBear security configuration |
| `bridge-unified-reduced` | Reduced unified ISA and admitted delegations | Unified `2²³`-row chunks | Folded into trailing unified chunks | Unified pooled lookup layout | Prove the selected unrolled verifier in unified mode; bound `2²⁷` cycles | Named BabyBear security configuration |
| `recursion-unified-reduced` | Reduced unified ISA and admitted delegations | Unified `2²³`-row chunks | Folded into trailing unified chunks | Unified pooled lookup layout | Prove the unified recursion verifier until the terminal shape; bound `2²⁷` cycles | Named BabyBear security configuration |
| `l1-proth120` | Delegation-free reduced unified ISA | One `2²²`-row unified chunk | Folded into the unified chunk | Unified Proth120 lookup layout | Produce the experimental packed L1 proof | Proth120, 100-bit target, `pack_log₂ = 4`, and 20 grinding bits |

The default unrolled-to-unified scheduling threshold is currently `2²⁶` estimated
cycles. It is a selected recursion policy, not an ISA relation or fixed protocol
constant.

Delegated circuit capacities are owned by their circuit modules and imported wherever
the corresponding precompile is selected:

| Fulfillment relation | Rows per chunk |
|---|---:|
| BLAKE2s round/compression | `2²⁰` |
| BLAKE2s G function | `2²²` |
| Bigint | `2²²` |
| Keccak-special5 | `2²²` |

## Canonical ownership and profile views

The same fact must not acquire multiple canonical definitions merely because several
profiles use it.

- Shared memory and lookup relations live in `memory/common.md` and
  `lookups/common.md`.
- Unrolled and unified equations remain separate while their equivalence is unproved
  or their accepted relations differ.
- Profile views contain links and stable IDs, not copied equations.
- Do not add `common/`, `profiles/`, `stages/`, or `configurations/` subdivisions by
  symmetry. Add a subdivision only when concrete modules require one.
- Prefer Markdown links over filesystem symlinks. A symlink may be used as a purely
  navigational convenience, but it never creates a second owner for a relation.
- Operational choices such as CPU versus GPU, worker count, caches, and equivalent
  oracle-storage strategies do not create semantic profiles unless they alter the
  accepted relation, transcript, or proof format.

## Incremental migration

Reorganization proceeds component by component. A move must preserve the meaning,
stable statement IDs, authority, and evidence of the moved module.

### Phase 1 — ISA

1. Inventory every current instruction and precompile module and identify its one
   canonical owner.
2. Add `isa/INDEX.md` over the canonical instruction and precompile relations.
3. Let the top-level manifests under `profiles/` select the required ISA relations.
4. Keep unrolled and unified family modules separate until a reviewed equivalence
   result permits a shared module.
5. Move existing ISA-level `profile.md` contents into the new manifests only after
   their admission sets and dependencies are reconciled.
6. Update links and metadata in the same change as each move; do not use a filesystem
   move as an opportunity for an unrelated semantic rewrite.

### Phase 2 — Execution

1. Separate shared cycle/register/decoder guarantees from unrolled and unified
   dispatch.
2. Specify activation, padding, trace capacity, chunk-count formulas, and circuit
   selection by execution profile.
3. Import ISA profiles rather than enumerating instruction equations again.

### Phase 3 — Memory and lookups

1. Move shared ROM/RAM and global memory relations under `memory/`.
2. Split separate-circuit and folded initialization/teardown packaging into explicit
   variants.
3. Move fixed-table, decoder-table, range-check, timestamp-check, and local lookup
   relations under `lookups/`.
4. Record per-family versus pooled lookup composition without duplicating the lookup
   equations.

### Phase 4 — Recursion

1. Separate base acceptance, unrolled continuation, unified bridge, unified
   continuation, and terminal/L1 relations.
2. For every stage, identify the verifier program, input stream, predecessor proof,
   successor proof, cycle bound, and terminal condition.
3. Keep scheduling heuristics distinct from acceptance relations.

### Phase 5 — Soundness and final aggregation

1. Define the soundness relations and concrete parameter sets actually used.
2. Bind each proof stage to its parameter set and state any deviations.
3. Complete the error budget for the selected end-to-end composition.
4. Complete the top-level profile manifests only from reconciled component
   selections.

## Current-to-target routing

This table guides migration; it does not move the files by itself.

| Current area | Planned owner |
|---|---|
| `isa/unrolled/`, `isa/unified/`, `isa/precompiles/` | Canonical relations under `isa/`; selection in top-level `profiles/` manifests |
| `machine-old/execution.md` | `execution/unrolled.md` and `execution/unified.md` |
| `machine-old/decoder.md` | Decoder authentication under `execution/`; table membership under `lookups/` |
| `machine-old/registers.md`, `machine-old/continuity.md` | Execution state and continuity modules, shared only where the relation is actually common |
| `machine-old/memory.md` | `memory/common.md` plus the two initialization/teardown variants |
| `lookups/common.md` | Integrated common lookup relation; complete the profile-specific layouts in `lookups/unrolled.md` and `lookups/unified.md` |
| `recursion/base.md`, `recursion/topology.md` | Integrated proof-acceptance and topology material; split further only where distinct recursion relations require it |
| `soundness/accounting.md` | Integrated soundness ledger; complete its parameter relations and composition budget in place |
| `ETHPROOFS-W2.md` | External deliverable coverage; retain separately from normative component relations |

## Migration completion criteria

A component migration is complete only when:

- every relation has one canonical owner;
- profile-specific differences are explicit and common relations are not duplicated;
- all relative links and metadata dependencies resolve;
- the root and component indexes identify the new locations;
- no profile manifest silently selects an unresolved or unavailable component;
- gaps remain attached to the relation or compatibility decision they actually affect;
- the old path is removed only after all references have migrated.

Until then, [INDEX.md](INDEX.md) remains the authoritative map of current files and
this document remains the authoritative map of the agreed destination.
