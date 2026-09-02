# Airbender proof-system specification

- spec revision: `2026-09-02.1`
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
| `REL` | mathematical relation enforced by this component |
| `REQ` | non-relational profile, composition, or acceptance requirement |
| `INV` | derived or preserved invariant |
| `REJ` | explicitly forbidden accepting case |
| `OUT` | state or argument effect exported across a real component boundary |
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
| `MULDIVU` | [isa/unrolled/mul-div-unsigned.md](isa/unrolled/mul-div-unsigned.md) | unsigned `MUL`, `MULHU`, `DIVU`, `REMU` |
| `MWORD` | [isa/unrolled/memory-word.md](isa/unrolled/memory-word.md) | word loads and stores |
| `MEMSUB` | [isa/unrolled/memory-subword.md](isa/unrolled/memory-subword.md) | byte and halfword loads and stores |

### Unified ISA bodies

| ID | Path | Scope |
|---|---|---|
| `UADD` | [isa/unified/add-sub-mop.md](isa/unified/add-sub-mop.md) | standard add/subtract, project MOPs, nondeterminism, and delegation invocation |
| `UJUMP` | [isa/unified/jump-branch-slt.md](isa/unified/jump-branch-slt.md) | jumps, branches, and comparisons |
| `UBSHIFT` | [isa/unified/binary-shifts.md](isa/unified/binary-shifts.md) | bitwise, shift, and project xor-rotate operations |
| `UMWORD` | [isa/unified/memory-word.md](isa/unified/memory-word.md) | aligned word loads/stores and ROM/RAM dispatch |

### Delegated precompiles

| ID | Path | Scope |
|---|---|---|
| `B2ROUND` | [isa/precompiles/blake2s-round.md](isa/precompiles/blake2s-round.md) | BLAKE2s round and compression fulfillment |
| `B2G` | [isa/precompiles/blake2s-g.md](isa/precompiles/blake2s-g.md) | BLAKE2s G-function fulfillment |
| `BIGINT` | [isa/precompiles/bigint.md](isa/precompiles/bigint.md) | 256-bit arithmetic fulfillment |
| `KECCAK` | [isa/precompiles/keccak.md](isa/precompiles/keccak.md) | Keccak-f[1600] special-5 fulfillment |

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

UPROF -> ADD, BSHIFT, JUMP, MULDIVU, MWORD, MEMSUB, PRECOMP
UNIFIED -> UADD, UJUMP, UBSHIFT, UMWORD, PRECOMP, DEC, LOOKUP, REG, MEM, CONT
PRECOMP -> B2ROUND, B2G, BIGINT, KECCAK, DEC, REG, MEM, CONT

DEC -> LOOKUP, CONT
ADD, BSHIFT, JUMP, MULDIVU -> DEC, LOOKUP, REG, CONT
MWORD, MEMSUB -> DEC, LOOKUP, REG, MEM, CONT
UADD, UJUMP, UBSHIFT -> DEC, LOOKUP, REG, CONT
UMWORD -> DEC, LOOKUP, REG, MEM, CONT
```

## Largest remaining specification gaps

- `GAP-UPROF-001`: project MOP, nondeterminism, and delegation-call branches sharing
  the unrolled add-family circuit still need their own relations.
- `GAP-PRECOMP-001`: reduced-unified delegation admission is
  conflicting; direct setup/proving installs four fulfillment types while the named
  machine configuration declares only the two Blake types.
- `GAP-UADD-001..003`, `GAP-UBSHIFT-001`, `GAP-B2ROUND-001..003`,
  `GAP-B2G-001..003`, `GAP-BIGINT-001..002`, and `GAP-KECCAK-001`:
  implementation-specific custom arithmetic, control, ABI, counter, and
  pointer-domain relations remain provisional pending the decisions named in their
  modules.
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
transition described by `REL-JUMP-002`; it is an implementation defect, not an open
specification decision.
