# REG: Register state

> Defines architectural register reads and assignments, then the register tuples used
> to connect those effects globally. Instruction semantics and final public outputs are
> outside this module.

## Guarantee

The machine has 32 32-bit registers. `x0` reads as zero and discards assignments.
Every enabled implementation access is represented as one timestamped read/write pair;
the global argument connects those pairs into one history per register.

`*` marks the one provisional boundary claim whose intended initial/final authority
is unresolved by the gaps below. The marker is not part of the stable ID.

## Symbols

- `u32 = [0, 2^32)`.
- `Reg : [0, 32) -> u32` — architectural register values.
- `rts : [0, 32) -> [0, 2^38)` — last implementation access timestamp per register.
- `r : [0, 32)` — register index.
- `v, w : u32` — value read and value written by one access.
- `ts : [0, 2^38)` — cycle-base timestamp.
- `k : {0, 1, 2}` — local access position within an ordinary machine cycle.
- `q(space, address, timestamp, value)` — one global memory-like tuple.
- `Register = 0` — register address-space tag.

`x_r <- w` denotes an architectural assignment. Its right-hand side is evaluated from
the pre-transition state. Architectural locations not assigned by the transition remain
unchanged.

## Assumptions

- **`ASM-REG-001` — Global multiset closure.** After boundary contributions are
  included, acceptance of the global memory-like argument implies equality of its
  register read-tuple and write-tuple multisets.
- **`ASM-REG-002` — Local access authorization.** Each participating ISA or
  precompile relation enables exactly its selected register accesses and binds every
  access index, mode, and assigned value to its local computation.

## Canonical relation tree

> Interpret enabled accesses under `ASM-REG-001` and `ASM-REG-002`. The
> architectural requirement and implementation requirements are different views of the
> same access; implementation-only timestamp changes are not architectural assignments.

- **`enabled = 0`.** No architectural register effect and no register tuple contribution.
- **`enabled = 1`.** Let the access have register index `r` and local position `k`.
  - **Read.** Return `Reg[r]`; apply `REQ-REG-002` and `REQ-REG-003` with
    `w = Reg[r]`. No architectural register is assigned.
  - **Assignment.** Apply `REQ-REG-001`, `REQ-REG-002`, and `REQ-REG-003`.
    - **`r = 0`.** Discard the assigned value and preserve `x0` by `INV-REG-001`;
      the implementation pair carries `w = 0`.
    - **`r != 0`.** Assign `x_r <- w`; every other architectural register remains
      unchanged.

## Requirements

### REQ-REG-001 — Architectural register semantics

`Reg` contains exactly 32 values in `u32`. Reading `x0` returns zero. For `r != 0`,
`x_r <- w` replaces only `Reg[r]` by `w`; for `r = 0`, the assignment is discarded.

This is the register model of the official
[RV32I programmer's model](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html).

### `REQ-REG-002` — Register tuple encoding

An enabled access contributes exactly this pair:

```text
read  = q(Register, r, rts[r], Reg[r])
write = q(Register, r, ts + k, w)
```

For a read, `w = Reg[r]`. For an assignment to `x0`, `w = 0`.

### `REQ-REG-003` — Ordered implementation access

Every enabled access satisfies `rts[r] < ts + k`. After its tuple pair is formed, its
implementation record changes as follows:

```text
rts[r] <- ts + k;
Reg[r] <- w.
```

The second line records the tuple history. It is an architectural assignment only in
the assignment branch of the canonical tree. Other implementation records remain
unchanged.

### REQ-REG-004* — Proof-boundary closure

For every `r in [0, 32)`, the current base-proof construction adds:

```text
initial write = q(Register, r, 0, 0)
final read    = q(Register, r, rts_final[r], Reg_final[r]).
```

These contributions close each register history under `ASM-REG-001`.

## Preserved invariants

- **INV-REG-001 — Zero register.** `Reg[0] = 0` before a transition implies
  `Reg[0] = 0` afterward.

## Derived facts

- **Read effects**
  `Reg` unchanged
  `rts[r] <- ts + k`
- **Assignment effects**
  `r != 0 => only Reg[r] may change`
  `r = 0 => Reg[0] = 0`
- **Boundary history**
  `initial write = q(Register, r, 0, 0)`
  `final read = q(Register, r, rts_final[r], Reg_final[r])`

## Open boundary

- **GAP-REG-001 — Initial register authority.** Decide whether all 32 initial values
  and last-access timestamps being zero is normative, configurable statement data, or
  only the current base-proof construction.
- **GAP-REG-002 — Final register boundary.** Specify which final register values and
  last-access timestamps cross the public acceptance boundary. The current packed GKR
  path absorbs the complete final vector into its transcript and uses it for teardown,
  but that does not by itself define the end-to-end public statement.

## Metadata

- spec revision: TBD
- implementation: TBD
- profile: shared register relation for unrolled and unified machine circuits

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `ASM-REG-001` | normative | accepted global argument | `external:BASE` | located | `repo:cs/src/gkr_compiler/memory_like_grand_product.rs#layout_initial_grand_product_accumulation@dfb1b2a8a`; `repo:prover/src/definitions/mod.rs#produce_initial_permutation_product_separate_contributions@dfb1b2a8a` | `symbol:cs/src/gkr_compiler/memory_like_grand_product.rs#layout_initial_grand_product_accumulation`; `symbol:prover/src/definitions/mod.rs#produce_initial_permutation_product_separate_contributions` |
| `ASM-REG-002` | normative | enabled access | `external:UPROF`; `external:UNIFIED`; `external:PRECOMP` | located | `repo:cs/src/cs/circuit_impl.rs#BasicAssembly::request_mem_access@dfb1b2a8a`; `repo:cs/src/gkr_compiler/delegation_mem_accesses.rs#compile_register_and_indirect_mem_accesses@dfb1b2a8a`; circuit-local requests | `symbol:cs/src/cs/circuit_impl.rs#BasicAssembly::request_mem_access`; `symbol:cs/src/gkr_compiler/delegation_mem_accesses.rs#compile_register_and_indirect_mem_accesses` |
| `REQ-REG-001` | normative | architectural read or assignment | — | prose | `standard:RISC-V-Unprivileged-ISA@20260120#RV32I-programmers-model` | — |
| `REQ-REG-002` | normative | enabled access | `ASM-REG-002`, `REQ-REG-001` | located | `repo:cs/src/gkr_compiler/memory_like_grand_product.rs#layout_initial_grand_product_accumulation@dfb1b2a8a`; `repo:cs/src/definitions/gkr/mod.rs#AddressSpaceType@dfb1b2a8a` | `symbol:cs/src/gkr_compiler/memory_like_grand_product.rs#layout_initial_grand_product_accumulation`; `symbol:cs/src/definitions/gkr/mod.rs#AddressSpaceType` |
| `REQ-REG-003` | normative | enabled access | `ASM-REG-001`, `REQ-REG-002` | located | `repo:cs/src/gkr_compiler/range_check_exprs.rs#compile_timestamp_comparison_range_checks@dfb1b2a8a`; `repo:cs/src/gkr_compiler/memory_like_grand_product.rs#layout_initial_grand_product_accumulation@dfb1b2a8a` | `symbol:cs/src/gkr_compiler/range_check_exprs.rs#compile_timestamp_comparison_range_checks`; `symbol:cs/src/gkr_compiler/memory_like_grand_product.rs#layout_initial_grand_product_accumulation` |
| `REQ-REG-004` | provisional | once per base-proof boundary | `ASM-REG-001`, `REQ-REG-002`; `GAP-REG-001..002` | located | `repo:prover/src/definitions/mod.rs#produce_initial_permutation_product_separate_contributions@dfb1b2a8a` | `symbol:prover/src/definitions/mod.rs#produce_initial_permutation_product_separate_contributions` |
| `INV-REG-001` | normative | every architectural transition | `REQ-REG-001` | prose | `standard:RISC-V-Unprivileged-ISA@20260120#RV32I-programmers-model` | — |
| `GAP-REG-001` | open | — | affects `REQ-REG-004`; owner `human` | — | implementation fixes every initial register tuple to `(Register, r, 0, 0)`; no project decision identified | — |
| `GAP-REG-002` | open | — | affects final system/public statement; owner `human` | — | `repo:prover/src/gkr/prover/mod.rs#CommitmentMode@dfb1b2a8a`; `repo:prover/src/gkr/prover/mod.rs#prove_configured_with_gkr_impl@dfb1b2a8a` | `symbol:prover/src/gkr/prover/mod.rs#CommitmentMode`; `symbol:prover/src/gkr/prover/mod.rs#prove_configured_with_gkr_impl`; `pattern:prover/src/gkr/prover/mod.rs#registers_buffer(count=2)` |
