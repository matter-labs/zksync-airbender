# Unified memory initialization and teardown

> Integration stub for initialization and teardown data folded into unified
> execution chunks.

- spec revision: TBD
- implementation: TBD
- status: stub

This module will define placement in trailing unified chunks, boundary contributions,
and closure against the common memory relation. Current material remains in
[machine-old/memory.md](../machine-old/memory.md) and
[recursion/topology.md](../recursion/topology.md).

## info-meta

> Unorganised data dump collected from the implementation at `303ea6fa1`. Not
> normative, not ID'd, not reconciled with `memory/common.md`. Raw material for
> writing the real relations later.

**Shape.** No separate circuit exists. Initialization and teardown are compiled
*inline* into the reduced-machine family itself, via
`compile_family_circuit_with_inline_inits_and_teardowns`
(`cs/src/gkr_compiler/family_circuit.rs:969`, called from
`cs/src/gkr_circuits/unified_reduced_machine/circuit.rs:679-682`; inline lowering in
`cs/src/gkr_compiler/inits_and_teardowns_inline.rs`).

- `circuit_defs/unrolled_circuits/unified_reduced_machine/src/lib.rs:31` —
  `NUM_INIT_AND_TEARDOWN_PAIRS = 1`
- the compiled artifact gains a second global output channel,
  `OutputType::InitsAndTeardownsProduct`, alongside the ordinary
  `OutputType::PermutationProduct`
  (`cs/src/gkr_circuits/unified_reduced_machine/circuit.rs:785-794`)
- so one unified proof exposes **two** read/write product pairs, where an unrolled
  execution proof exposes one. This is the "second initialization/teardown pair where
  present" in the ye-branch TODO.

**Only trailing instances carry it.** The FSV reads `num_unified_circuits`, then a
second word `num_it_circuits`, and treats the *last* `num_it_circuits` instances as
the i/t carriers (`full_statement_verifier/src/unified_circuit_statement.rs:94-103`):

- `first_it_circuit = num_unified_circuits − num_it_circuits`
- `1 ≤ num_it_circuits ≤ num_unified_circuits`
- carriers must supply `proof_output.inits_and_teardowns` (an `Option`) and their
  products are multiplied into the global accumulators (`:152-161`)
- leading instances must report **all-zero** `top_bits`, so the prover has no free
  choice over values that are FS-committed but unused (`:170-180`)
- `assert_eq!(it_circuits_seen, num_it_circuits)` at the end

**Window discipline.** Unlike the unrolled mode's fixed `top_bits[i] == i`, the
unified windows are runtime-chosen and must be proven disjoint
(`full_statement_verifier/src/unified_circuit_statement.rs:104-106`, `:163-167`):

```text
ADDRESS_HIGH_BITS_SHIFT = 10
MAX_TOP_BIT = 1 << (32 − 16 − 10) = 64
per set: assert top_bit < MAX_TOP_BIT
across the concatenated top_bits of all i/t-carrying instances, in order:
  assert top_bit > prev_top_bit        (strictly increasing, starts from −1)
```

Strictly increasing + ceiling ⇒ disjoint per-instance memory super-blocks, so no two
instances can initialize or tear down the same range. The GKR-verified window is bound
to these same runtime values through `set_bits = top_bits[set_idx] << shift` in the
generated verifier.

**Transcript position.** `top_bits` are absorbed *before* the memory caps, in one
block together with the family index
(`full_statement_verifier/src/unified_circuit_statement.rs:124-142`):

```text
buffer[0]                    = REDUCED_MACHINE_CIRCUIT_FAMILY_IDX
buffer[1 .. 1+top_bits.len()] = inits_and_teardowns_top_bits
transcript.absorb(buffer)
transcript.absorb(memory_caps_flattened())
```

The comment states the reason explicitly: binding `top_bits` into the Fiat-Shamir
challenge, not just into the memory columns, closes the gap where a prover could pick
the GKR i/t window adaptively after seeing the challenges. Relies on
`INIT_AND_TEARDOWN_SETS < BLAKE2S_BLOCK_SIZE_U32_WORDS` so index + all top bits fit in
one transcript block. Prover-side mirror:
`circuit_defs/trace_and_split/src/lib.rs:576`
`fs_transform_unified_for_permutation_argument`.

**Shared setup.** Every unified instance is checked against the same setup cap
(`full_statement_verifier/src/unified_circuit_statement.rs:145-148`), where the
unrolled i/t circuit has no setup at all.

**Tuple lowering.** Identical to the unrolled mode — see the info-meta section of
[init-teardown-unrolled.md](init-teardown-unrolled.md); `gkr_eval_ir/src/lower/memory.rs:312-324`
is shared, with `high_bits_offset = log2(trace_len) + WORD_BITS − 16`.

**Open questions for the real relation.**

- what fixes `num_it_circuits`, and what stops a prover from declaring fewer carriers
  than the address space needs — the count split alone is not a coverage argument
- whether total coverage across instances is checked anywhere, or only disjointness
- `total_cycles += 1 << 24` per instance is hardcoded in the FSV with a `TODO` saying
  it should be derived from the circuit (`unified_circuit_statement.rs:115-118`); this
  is the same `2^23` vs `2^24` question as `GAP-EXEC-005`
- folded i/t rows issue no lookup queries (ye-branch TODO) — confirm against the
  inline compiler
