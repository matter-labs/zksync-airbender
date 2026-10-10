# Airbender V3 GKR Circuit Architecture

Use this architecture snapshot only after [the Airbender V3 machine profile](airbender-v3-machine-profile.md) passes its applicability check. It describes the GKR architecture at commit `0b8febeb44c2794c028372561bb0ed41bcb5fc56`; it is not a generic Airbender or ZKP-circuit reference.

## Execution statement

The architecture proves the restricted RV32I-derived profiles, custom CSRRW/Zimop carriers, fixed/preprocessed ROM, and delegation operations specified in the versioned machine profile. Read the [normative RV32 baseline](riscv32-machine-baseline.md) for ordinary ISA semantics, then the versioned machine profile for this repository's deliberate delta.

Do not derive the intended ISA solely from whichever operations happen to appear in circuit code. If the checkout differs from this profile, create a version delta. An undocumented semantic mismatch is a specification question or candidate bug, not an automatic new specification.

## Circuit organization

Execution cycles may be split by opcode family into unrolled circuits, combined into a unified circuit for recursion, or handled by delegation/precompile circuits. A named circuit ordinarily proves only its family/profile semantics, not the entire ISA.

Common unrolled families cover add/subtract and custom operations, binary shifts, jumps/branches/comparisons, word memory, subword memory, multiplication/division, and individual delegation precompiles. A unified circuit may select among several families. Resolve the exact family and profile rather than checking a named family against the full ISA.

Witnesses are arranged as row-shaped execution data at the base layer and then encoded into a layered GKR circuit. Later layers compress row constraints and contributions to memory or lookup arguments.

## Algebraic model

Typical properties include:

- base witnesses over a roughly 31-bit prime field;
- extension-field values where random challenges are required;
- batched Sumchecks with maximum gate degree commonly 2;
- terminal outputs routed to zerocheck constraints, local lookup/LogUp claims, or global memory/state/delegation claims;
- non-interactive challenges derived through Fiat-Shamir at the proof-system interface.

Verify actual constants and interfaces in the branch under review.

Historical public reports may describe a different proof backend, field, lookup split, or security parameter set from the checked-out branch. Use such reports only when their version matches the target; proof-system parameters do not redefine the RV32I-derived machine semantics.

## Local lookups

The lookup baseline is Haböck's [*Multivariate lookups based on logarithmic derivatives*](https://eprint.iacr.org/2022/1530), with the GKR-specific refinement in Papini and Haböck's [*Improving logarithmic derivative lookups using GKR*](https://eprint.iacr.org/2023/1284) relevant to the layered implementation. Separate local lookup arguments may cover generic table membership, word/limb range checks, and timestamp ranges. Although a verifier may complete these arguments at chunk level, the circuit must locally constrain query/table encodings, selectors, multiplicities, inverse witnesses, padding behavior, and exposed accumulator claims.

The architecture summary identifies generic/decoder lookups, 16-bit range-check lookups for word limbs, and timestamp range checks commonly split into 19-bit limbs. Verify widths and argument selection in code.

## Global interactions

The memory baseline is Yang and Heath's [*Two Shuffles Make a RAM: Improved Constant Overhead Zero Knowledge RAM*](https://eprint.iacr.org/2023/1115). Airbender adapts memory-like shuffled sets to connect registers, mutable RAM, ROM-shaped traffic, program-counter/timestamp state, and delegation traffic across circuits and chunks. During a per-circuit review, assume the global permutation mechanism is consistent, then verify that every local tuple field and activation rule correctly represents the selected operation.

The summarized memory tuple has the semantic shape:

```text
(type, address, timestamp, value)
```

where the current type tags are `Register = 0`, `RAM = 1`, and `PC = 2`; the architecture currently describes a 32-bit address, 38-bit timestamp, and 32-bit value. Verify the exact layout, limb decomposition, type tags, timestamp offsets, and compression order in the checked-out implementation.

This shared mechanism has distinct uses that must not be conflated:

- **Register access:** base registers use type `Register` and addresses `0..31`, with initialization and final public teardown values.
- **RAM access:** mutable memory uses type `RAM`, including timestamp-ordered reads, writes, word/subword reconstruction, and address semantics.
- **ROM-shaped access:** the low ROM region emits memory traffic, but actual ROM contents are authenticated by a preprocessed bytecode/ROM lookup. The memory values are concrete but semantically ignored for ROM reads; stores to ROM must be rejected.
- **PC/timestamp state:** type `PC` links cycle-start `(PC, timestamp)` to locally constrained cycle-end `(next PC, timestamp + stride)` state, normally using an empty address.
- **Delegation/precompile access:** virtual register addresses beyond the base-register set carry zero-valued, timestamped invocation/fulfillment tuples. They have no ordinary initialization or teardown and form a permutation bus, not RAM.

Current implementations also omit some direct read-tuple range checks by induction. Read values inherit their range from range-valid initialization plus range-checked writes; some addresses inherit it from valid inits/teardowns plus timestamp ordering and permutation closure. This is a proof obligation, not a blanket assumption: audit every base case, every possible write path, strict ordering, final closure, and separation between ordinary memory, ROM, PC state, and the delegation bus. See [memory-and-ram.md](memory-and-ram.md) for the complete checklist.

Global consistency cannot repair a locally wrong address, type tag, timestamp, value, or omitted contribution when that wrong contribution is itself globally consistent.

The cited constructions and the concrete adaptations above are subject to change. Preserve the semantic goals when reviewing a newer branch: lookup arguments still prove membership in precisely defined tables/multisets, RAM still models ordered read/write state, and pure permutation buses still require exact producer/consumer matching. Reconstruct the current mechanism before deciding whether a paper detail is required.

## Padding and chunking

Fixed-size chunks may inject inactive cycles controlled by an execution flag. Verify that the flag is constrained and that inactive rows consistently disable state, memory, lookup, and delegation effects. Treat cross-chunk continuity as an explicit assumption unless the named circuit completes it locally.

## Review implication

For an opcode-family circuit, trace:

```text
authenticated decode/profile
  -> operation selector and operands
  -> arithmetic and range relations
  -> next state and local outputs
  -> local lookup claims
  -> global memory/state/delegation contributions
  -> GKR aggregation and verifier-visible claims
```
