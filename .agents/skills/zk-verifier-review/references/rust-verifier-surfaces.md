# Rust Verifier Implementation Surfaces

## Contents

1. Parsing adversarial proof data
2. Field and integer decoding
3. Unsafe and release behavior
4. Generated verifiers
5. Merkle and transcript buffers
6. Tests and differential validation
7. Trusted constants and artifact provenance

## 1. Parsing adversarial proof data

Treat `NonDeterminismSource`, iterators, readers, deserializers, and proof structs as attacker-controlled streams. Inventory every read in actual order.

Check:

- underflow/EOF behavior and whether missing words become zero/default;
- trailing unread words and ambiguous proof framing;
- length/count conversions between `u32`, `usize`, and shifts;
- multiplication/addition overflow when computing offsets or capacities;
- attacker-controlled allocation and loops when robustness is in scope;
- enum/tag dispatch and invalid variants;
- optional/empty vectors and implicit defaults;
- duplicate fields that should equal derived values;
- data parsed before the context that determines its expected length;
- parser branches that alter transcript absorption.

An outer proof containing concatenated inner proofs needs unambiguous boundaries. If inner verifiers consume a shared stream, verify every branch consumes exactly its specified length.

## 2. Field and integer decoding

Distinguish:

- canonical decoding that rejects values `>= p`;
- raw representation known to be reduced;
- conversion with reduction modulo `p`;
- unchecked constructors;
- range-checked integer limbs represented as field elements.

Reduction can be correct for transcript challenges but dangerous for proof encodings when the same algebraic value has several serialized forms or when transcript and semantic parser see different representatives. Check whether raw words are absorbed before or after reduction and whether prover/verifier serialize identically.

For extension fields, verify coefficient count/order, each base coefficient's decoding, memory layout assumptions, and the exact hash encoding. For `u64` nonces/timestamps, verify low/high order. For packed limbs, validate unused high bits before recombination.

## 3. Unsafe and release behavior

Cryptographic verifier code often uses `unsafe` for fixed-capacity buffers. Audit the proof of every invariant supporting:

- `get_unchecked` and unchecked slice conversion;
- `MaybeUninit` length initialization;
- pointer casts between words, fields, arrays, and aligned blocks;
- `repr(C)`/alignment/offset assumptions;
- const-generic capacities versus runtime lengths;
- unchecked enum or index conversion.

Differentiate memory safety from soundness, but recognize overlap: reading uninitialized/stale data, truncating a buffer, or indexing the wrong claim can change the accepted relation.

List all `debug_assert!` and debug-only checks that support cryptographic correctness. Production soundness must use unconditional checks, type-level invariants proven at construction, or unreachable states enforced by authenticated constants. Compiler optimization hints and comments are not enforcement.

Also inspect the optimized artifact for checks the compiler could prove
redundant and delete. `core::hint::black_box` or an equivalent barrier may be
deliberately preserving a guest range/assertion check; the barrier is evidence
of intent, not the enforcement itself. Confirm the assertion remains in the
feature-selected optimized binary and add a regression that detects its loss.

Treat unsafe logical length separately from allocated capacity. Patterns such
as pushing `n` initialized elements, calling `set_len(MAX)` to expose a fixed
array, and carrying `n` in another field leave a tail that must never be read,
hashed, copied, or compared. Trace every consumer using both the physical and
logical lengths; a capacity proof does not prove tail initialization.

Check panic configuration. A verifier that aborts on malformed untrusted proof data may be an availability issue even if it cannot accept a false proof.

## 4. Generated verifiers

Build a generator-to-binary map:

```text
circuit definition/config
  -> compiled artifact/layout
  -> generator branches/constants
  -> generated Rust
  -> feature-selected crate/binary
  -> full-statement function pointer/dispatch
```

Audit generator loops and emitted code for:

- deterministic/stable address ordering;
- all gate and lookup variants;
- layer-zero and final-layer special cases;
- zero/one/many columns, claims, and rounds;
- cached/virtual relations;
- LSB/MSB order and dimension-reducing layers;
- security-level-specific schedules;
- buffer-capacity calculations;
- stale committed outputs or binaries;
- regenerated source differing from the deployed artifact;
- test-only/proof-utils code accidentally defining serialization differently.

Audit Cargo feature unification and each concrete binary independently. A function or binary named `sec_100` does not establish 100-bit end-to-end security if a direct dependency enables `security_80`, if an outer aggregation/PoW constant is selected through a different feature path, or if Cargo unifies an unintended feature combination. Trace the resolved feature set from the build target through every verifier layer, and require compile-time rejection of mixed/incoherent security modes.

A generator test that produces an accepting honest proof checks completeness, not malicious soundness. Add structural tests for transcript schedules and mutated proof data.

Generated verifier constants are trusted inputs, not self-authenticating facts.
Trace setup caps, verifier keys, circuit layouts, delegation parameters, final
PCs, security constants, and imported generated modules to the exact circuit or
program artifact that produced them. Require deterministic regeneration and a
checked diff where supported. A verifier can consistently and soundly verify
the wrong program when its expected constant is stale or came from the wrong
build.

## 5. Merkle and transcript buffers

For aligned transcript buffers verify:

- current seed is included exactly once;
- meaningful data length excludes uninitialized padding and includes all real data;
- zero padding is deterministic;
- hash final-block active length matches on all implementations;
- hasher reset preserves the intended seed chain;
- buffer capacities cover the rounded size in release builds.

For Merkle buffers verify:

- exact leaf value count and order;
- hashing of empty leaves/oracles;
- state reset between leaves/paths;
- sibling placement and cap lookup;
- depth arithmetic cannot underflow;
- cap slice length is checked before unchecked access;
- distinct oracle types cannot share caps without explicit binding.

## 6. Tests and differential validation

Use safe, defensive tests where authorized:

- compare prover flattener output length/order with verifier read instrumentation;
- compare native and recursive verifier transcript challenge traces;
- regenerate verifiers and compare expected diffs;
- mutate or delete each proof item and expect rejection;
- vary optional/empty/singleton/max-count cases;
- test noncanonical field/length/tag encodings;
- pin transcript vectors across architectures and feature modes;
- pin security parameters and PoW threshold edge cases;
- compare LSB/MSB or final-round formulas against a small reference evaluator;
- ensure no trailing data is accepted when canonical proof encoding requires exhaustion.

Do not treat fuzzing that finds no crash as soundness evidence. Property tests should assert rejection or equivalence to a simple specification.

## 7. Trusted constants and artifact provenance

Build a provenance table:

| Trusted value | Source artifact/program | Generation command/config | Imported at | Compared by | Reproducible? | Deployed value |
|---|---|---|---|---|---|---|

Include every setup cap/key, fixed-table commitment, circuit-family dispatch
constant, program/binary digest, recursion verifier identity, expected final PC,
field/hash/security parameter, trace-size constant, and delegation setup.

Check that:

- generation consumes the intended source revision and feature/security mode;
- generated/imported files cannot be silently mixed across circuits or levels;
- regeneration is deterministic or differences are explained;
- CI/tests regenerate and compare security-critical constants;
- the wrapper selects the exact constant set matching the verifier binary;
- recursive and L1 layers ultimately compare the propagated identity with a
  trusted expected value;
- deployed bytecode contains the reviewed constants.
