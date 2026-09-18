# Unrolled memory initialization and teardown

> Integration stub for the separate initialization/teardown proof used by unrolled
> execution.

- spec revision: TBD
- implementation: TBD
- status: stub

This module will define the initialization and finalization contributions, their
public bindings, and their composition with unrolled execution chunks. Current
material remains in [machine-old/memory.md](../machine-old/memory.md) and
[recursion/base.md](../recursion/base.md).

## info-meta

> Unorganised data dump collected from the implementation at `303ea6fa1`. Not
> normative, not ID'd, not reconciled with `memory/common.md`. Raw material for
> writing the real relations later.

**Shape.** A dedicated circuit family, proved separately from every execution family.
Family index `INITS_AND_TEARDOWNS_FORMAL_CIRCUIT_FAMILY_IDX`.

- `circuit_defs/unrolled_circuits/inits_and_teardowns/src/lib.rs:12-15` —
  `TRACE_LEN_LOG2 = 24`, `NUM_INIT_AND_TEARDOWN_SETS = 16`, `WORD_BITS = 2`
- coverage: `16 · 2^24 · 4 bytes = 2^30 bytes`, i.e. word addresses
  `{4i | 0 ≤ i < 2^28}` — same set as `REQ-MEM-003` in
  [machine-old/memory.md](../machine-old/memory.md)
- `num_bytes_per_set = (1 << trace_len_log2) << WORD_BITS`, asserted
  `num_bytes_per_set · num_sets ≤ 2^32`
  (`cs/src/gkr_compiler/inits_and_teardowns.rs:16-18`)

**No lookups, no setup.** The circuit has no range checks and no generic lookups at
all (`cs/src/gkr_compiler/inits_and_teardowns.rs:16`). It has no committed setup
either: the FSV asserts `setup_caps.len() == 0`
(`full_statement_verifier/src/unrolled_proof_statement.rs:155`). This is why the
lookup inventory in the ye-branch TODO lists initialization/teardown as `0` generic
queries, `0` 16-bit queries, `0` timestamp queries.

**What is committed vs derived.** Only the *teardown* timestamp and value are
committed base-layer variables, two limbs each, per set
(`cs/src/gkr_compiler/inits_and_teardowns.rs:29-66`). Addresses are never committed —
they come from virtual setup polynomials `VirtualSetupPoly::InitsAndTeardownsLow` and
`InitsAndTeardownsHigh` (`cs/src/gkr_compiler/inits_and_teardowns.rs:187-190`), i.e.
verifier-evaluated closed forms. Init tuples carry zero timestamp and zero value and
so need no columns at all.

**Tuple lowering** (`gkr_eval_ir/src/lower/memory.rs:312-324`), shared with the
unified mode:

```text
address space = RAM constant
low address   = ch(AddressLow)  · VirtualSetup(InitsAndTeardownsLow)
high address  = ch(AddressHigh) · (VirtualSetup(InitsAndTeardownsHigh) + top_bits)
Init arm     : no timestamp/value terms  (zero ts, zero value)
Teardown arm : + ch(TsLow/High)·mem[ts] + ch(ValLow/High)·mem[val]
top_bits bound as inits_and_teardowns_top_bits[set_idx] << high_bits_offset
high_bits_offset = log2(trace_len) + WORD_BITS − 16     (= 10 here)
```

**Aggregation.** Sets are consumed two at a time by `create_inits_and_teardowns_set`
(`cs/src/gkr_compiler/inits_and_teardowns.rs:176`), then the read and write sets are
reduced pairwise by `GrandProductAccumulationStep::AggregationPair` up a binary tree
to exactly one read product and one write product
(`cs/src/gkr_compiler/inits_and_teardowns.rs:80-110`).

**FSV consumption** (`full_statement_verifier/src/unrolled_proof_statement.rs:131-162`):

- `assert_eq!(num_circuits, 1)` — exactly one i/t proof per statement
- absorbs the family index into the transcript, then the memory caps
- windows are pinned, not chosen: `top_bits[i] == i` for every set, so the 16 windows
  are a fixed contiguous cover of the low `2^30` bytes
- its read/write products are multiplied into the same two global accumulators as the
  execution families

**Drift vs `main`.** This branch predates `37747dbae` "allow >1 inits/teardowns
circuit (#433)" and `bc55aad87` "halve sets per proof (#434)"; neither is an ancestor
of this HEAD. So both `assert_eq!(num_circuits, 1)` and
`NUM_INIT_AND_TEARDOWN_SETS = 16` are already stale upstream. Recheck before writing
normative relations.
