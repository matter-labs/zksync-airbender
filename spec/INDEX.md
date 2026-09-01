# Airbender proof-system specification

- spec revision: `2026-09-01.1`
- implementation: `matter-labs/zksync-airbender@dfb1b2a8a+dirty`
- scope: unrolled and reduced-unified ISA implementations, shared machine state, and
  the current proof hierarchy

## Layout

- `isa/unrolled/` specifies the per-family unrolled ISA implementation.
- `isa/unified/` specifies the reduced unified ISA implementation.
- `isa/precompiles/` specifies delegated operations and their profile availability.
- `machine/` specifies state and interfaces shared by the ISA implementations:
  decoding, lookups and range checks, registers, ROM/RAM, and cycle continuity.
- `proofs/` specifies proof invocations, composition, acceptance, and soundness
  obligations.

`machine/execution.md` is the thin composition rule that selects one ISA profile and
connects its transitions to the shared machine components. The former
`statement/base.md` has moved to `proofs/base.md`; it specifies acceptance of a base
proof artifact, not an ISA transition.

## Statement notation

| Prefix | Meaning |
|---|---|
| `IN` | admitted input domain |
| `ASM` | guarantee imported from another component |
| `REQ` | relation enforced or checked by this component |
| `INV` | derived or preserved invariant |
| `REJ` | explicitly forbidden accepting case |
| `OUT` | value or proposition exported across a real component boundary |
| `GAP` | one unresolved decision or missing fact |

An asterisk after a main-body ID marks a genuinely provisional relation: its support
is implementation-only, incomplete or conflicting, or its intendedness remains open.
It is not part of the stable ID. See
[METADATA.md](METADATA.md) for authority, activation, dependencies, bindings, and
source locators.

## Modules

### ISA profiles

| ID | Path | Scope |
|---|---|---|
| `UPROF` | [isa/unrolled/profile.md](isa/unrolled/profile.md) | full-unsigned unrolled profile and family inventory |
| `UNIFIED` | [isa/unified/profile.md](isa/unified/profile.md) | reduced unified profile and embedded-family inventory |
| `PRECOMP` | [isa/precompiles/profile.md](isa/precompiles/profile.md) | delegated Blake2s, bigint, and Keccak variants by profile |

### Unrolled ISA families

| ID | Path | Scope |
|---|---|---|
| `ADD` | [isa/unrolled/add-sub.md](isa/unrolled/add-sub.md) | `ADD`, `ADDI`, `LUI`, `SUB`, `AUIPC`, canonical `NOP` |
| `BSHIFT` | [isa/unrolled/binary-shifts.md](isa/unrolled/binary-shifts.md) | bitwise and shift operations |
| `JUMP` | [isa/unrolled/jump-branch-slt.md](isa/unrolled/jump-branch-slt.md) | jumps, branches, and comparisons |
| `MULDIV` | [isa/unrolled/mul-div.md](isa/unrolled/mul-div.md) | unsigned `MUL`, `MULHU`, `DIVU`, `REMU` |
| `MWORD` | [isa/unrolled/memory-word.md](isa/unrolled/memory-word.md) | word loads and stores |
| `MEMSUB` | [isa/unrolled/memory-subword.md](isa/unrolled/memory-subword.md) | byte and halfword loads and stores |

### Shared machine

| ID | Path | Scope |
|---|---|---|
| `MACH` | [machine/execution.md](machine/execution.md) | profile-selected execution composition |
| `DEC` | [machine/decoder.md](machine/decoder.md) | program-derived decoder authentication |
| `LOOKUP` | [machine/lookup.md](machine/lookup.md) | fixed tables, decoder membership, range checks, local LogUp output |
| `REG` | [machine/registers.md](machine/registers.md) | architectural registers, `x0`, and register-history tuples |
| `MEM` | [machine/memory.md](machine/memory.md) | ROM, RAM, alignment, and global memory consistency |
| `CONT` | [machine/continuity.md](machine/continuity.md) | PC, timestamp, activation, padding, and cycle continuity |

### Proof hierarchy

| ID | Path | Scope |
|---|---|---|
| `TOPO` | [proofs/topology.md](proofs/topology.md) | base, GKR/Sumcheck, WHIR, recursion, continuation, and final-verifier edges |
| `BASE` | [proofs/base.md](proofs/base.md) | unrolled base-proof acceptance and program/output binding |
| `SOUND` | [proofs/soundness.md](proofs/soundness.md) | W2 soundness accounting and W3 obligation stub |
| `W2` | [ETHPROOFS-W2.md](ETHPROOFS-W2.md) | official W2 requirements and current coverage |

## Composition map

`A -> B` means `A` uses the relation or inventory defined by `B`. Proof modules may
discharge assumptions exported by machine modules; this map is architectural rather
than a build-order DAG.

```text
TOPO -> BASE, SOUND
BASE -> MACH, UPROF, PRECOMP, REG, MEM, CONT, LOOKUP
MACH -> UPROF | UNIFIED, PRECOMP, DEC, LOOKUP, REG, MEM, CONT

UPROF -> ADD, BSHIFT, JUMP, MULDIV, MWORD, MEMSUB, PRECOMP
UNIFIED -> PRECOMP, MEM, DEC, LOOKUP, REG, CONT

DEC -> LOOKUP, CONT
ADD, BSHIFT, JUMP, MULDIV -> DEC, LOOKUP, REG, CONT
MWORD, MEMSUB -> DEC, LOOKUP, REG, MEM, CONT
```

## Largest remaining specification gaps

- `GAP-UPROF-001`: project MOP, nondeterminism, and delegation-call branches sharing
  the unrolled add-family circuit still need their own relations.
- `GAP-PRECOMP-001..002`: delegated precompile computations and their exact register/
  memory ABIs still need dedicated relation modules.
- `GAP-UNIFIED-001`: no adopted equivalence result yet supports one common ISA
  relation for operations shared by unrolled and unified implementations.
- `GAP-DEC-001`: the accepted program image and the separately supplied decoder text
  section still need a fully specified identity edge.
- `GAP-TOPO-001..005`: production path selection, exact invocation counts, complete
  invocation interfaces, auxiliary edges, and the terminal artifact remain incomplete.
- `GAP-SOUND-001..005`: concrete error budgets, lemma classification, production
  deviations, and the final W3 composition theorem remain future work.

The jump/branch/comparison witness generator also has a known implementation
conformance defect at the pinned revision: some not-taken branches around a 16-bit PC
boundary swap the low-limb carry and final-overflow witnesses. This can reject a valid
transition described by `REQ-JUMP-002`; it is an implementation defect, not an open
specification decision.
