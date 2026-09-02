# PRECOMP: Delegated-precompile profile

> Profile admission and dispatch between executor carrier rows and fulfillment
> circuits; each linked module owns its computation and ABI

`*` marks the reduced-unified admission rule whose intended profile is unresolved by
`GAP-PRECOMP-001`

## Guarantee

An admitted sequence of custom `CSRRW` carriers selects exactly one precompile type
per carrier row. The executor and the selected fulfillment circuit contribute mirrored
synthetic-register tuples, so global permutation closure matches every invocation to a
fulfillment of the same type and timestamp

## Symbols

- `u16 = [0, 2¹⁶)`
- `u38 = [0, 2³⁸)`
- `P ∈ {full-unrolled, reduced-unrolled, reduced-unified}` — selected executor
  profile
- `δ ∈ u16` — delegation type, equal to the carrier CSR number
- `τ ∈ u38` — invocation timestamp
- `V(δ, τ) = (Register, δ, τ, 0)` — synthetic-register permutation tuple;
  the value and absent high address limb are zero
- `Inv_P` — multiset of `(δ, τ)` pairs emitted by active executor carrier rows
- `Ful_P` — multiset of `(δ, τ)` pairs emitted by active fulfillment rows

## Assumptions

- **ASM-PRECOMP-001 — Authenticated preprocessing**
  Program preprocessing binds each carrier word, complete-run shape, delegation type,
  and executor profile to the decoder table used by the proof
- **ASM-PRECOMP-002 — Global permutation closure**
  The shared memory-like argument uses common challenges for every executor,
  fulfillment, initialization, and teardown contribution and accepts only when its
  read and write products agree

## Supported operations

| Operation | `δ` and carrier | Complete run | Fulfillment circuit | Owned relation |
|---|---|---:|---|---|
| Blake2s round/compression | `0x7c7`; `CSRRW x0, 0x7c7, x0` | 7 or 10 words | `Blake2sWithCompressionDelegationCircuit` | [Blake2s round](blake2s-round.md) |
| Blake2s G function | `0x7c8`; `CSRRW x0, 0x7c8, x0` | 56 or 80 words | `Blake2sGFunctionDelegationCircuit` | [Blake2s G](blake2s-g.md) |
| Bigint with control | `0x7ca`; `CSRRW x0, 0x7ca, x0` | 1 word | `BigIntDelegationCircuit` | [Bigint](bigint.md) |
| Keccak-f1600 `special5` | `0x7cb`; `CSRRW x0, 0x7cb, x0` | 649 words | `KeccakSpecial5DelegationCircuit` | [Keccak](keccak.md) |

The Blake2s G lengths are `7 × 8` and `10 × 8`. Round-count, control,
register, and indirect-memory semantics belong to the linked relation modules

## Canonical dispatch tree

> Interpret the tree under `ASM-PRECOMP-001..002`

- **`P = full-unrolled`**
  - **`δ ∈ {0x7c7, 0x7c8, 0x7ca, 0x7cb}`** `REL-PRECOMP-001`,
    `REQ-PRECOMP-002`, `REQ-PRECOMP-004`, and `REL-PRECOMP-005`
  - **otherwise** not admitted by `REQ-PRECOMP-002`
- **`P = reduced-unrolled`**
  - **`δ ∈ {0x7c7, 0x7c8}`** `REL-PRECOMP-001`, `REQ-PRECOMP-002`,
    `REQ-PRECOMP-004`, and `REL-PRECOMP-005`
  - **otherwise** not admitted by `REQ-PRECOMP-002`
- **`P = reduced-unified`**
  - **`δ ∈ {0x7c7, 0x7c8, 0x7ca, 0x7cb}`** `REL-PRECOMP-001`,
    `REQ-PRECOMP-003*`, `REQ-PRECOMP-004`, and `REL-PRECOMP-005`
  - **otherwise** not admitted by `REQ-PRECOMP-003*`
- **Admitted carrier sequence**
  - **run length equals the selected row in Supported operations** one executor
    invocation and one fulfillment row per carrier word under `REL-PRECOMP-001` and
    the selected profile-admission requirement
  - **otherwise** preprocessing does not admit the sequence under `REL-PRECOMP-001`

## Relations and profile requirements

### REL-PRECOMP-001 — Carrier sequence

Every carrier word in a complete run has the selected table encoding

`carrier(δ) = CSRRW x0, δ, x0`

The run length is exactly the corresponding value in Supported operations. A complete
run of length `L` produces `L` executor invocation rows and `L` fulfillment rows. The
execution preprocessor may dispatch the complete run through one specialized handler;
the proof relation still contains one matched row per constituent carrier word

### REQ-PRECOMP-002 — Unrolled profile admission

`Admit(full-unrolled) = {0x7c7, 0x7c8, 0x7ca, 0x7cb}`

`Admit(reduced-unrolled) = {0x7c7, 0x7c8}`

The current unrolled setup rejects a delegation row whose `δ` is outside the
selected set

### REQ-PRECOMP-003* — Reduced-unified profile admission

The current reduced-unified decoder setup admits

`Admit(reduced-unified) = {0x7c7, 0x7c8, 0x7ca, 0x7cb}`

This implemented set is provisional because the execution path names
`ReducedMachineWithDelegation`, whose declared set is `{0x7c7, 0x7c8}`

### REQ-PRECOMP-004 — Fulfillment dispatch

| `δ` | Fulfillment relation |
|---:|---|
| `0x7c7` | [Blake2s round](blake2s-round.md) |
| `0x7c8` | [Blake2s G](blake2s-g.md) |
| `0x7ca` | [Bigint](bigint.md) |
| `0x7cb` | [Keccak](keccak.md) |

Each fulfillment setup fixes its own `δ`. An active fulfillment row satisfies the
linked relation and uses the invocation timestamp supplied by its witness

### REL-PRECOMP-005 — Invocation and fulfillment tuples

For an active executor carrier row of type `δ` at cycle timestamp `ts`

`τ = ts + 1`

`executor_read  = V(δ, 0)`

`executor_write = V(δ, τ)`

For its active fulfillment row

`fulfillment_read  = V(δ, τ)`

`fulfillment_write = V(δ, 0)`

Read/write product orientation supplies the sign; the tuple has no separate direction
field. Inactive executor and fulfillment rows contribute the multiplicative identity

## Derived facts

- **Matched dispatch**
  `Inv_P = Ful_P` as multisets
- **Type separation**
  `(δ₁, τ₁) = (δ₂, τ₂) ⇒ δ₁ = δ₂ ∧ τ₁ = τ₂`
- **Dispatch neutrality**
  `value(V(δ, τ)) = 0`
- **Per-run cardinality**
  `|Inv_P| = |Ful_P| = L` for one admitted run of length `L`

## Open boundary

- **GAP-PRECOMP-001 — Reduced-unified admission policy**
  Decide whether reduced-unified admits all four types implemented by its decoder
  setup and prover, or only the two Blake types declared by
  `ReducedMachineWithDelegation`. This decision promotes or replaces
  `REQ-PRECOMP-003`

## Metadata

The carrier shapes, unrolled admission sets, circuit dispatch, and mirrored tuple
relation are normative for the selected implementation profiles. They converge across
constants, preprocessing, circuit constraints, setup construction, replay, and the
full-statement verifier. Only the conflicting reduced-unified admission policy remains
provisional

- spec revision: `2026-09-02.1`
- implementation: `matter-labs/zksync-airbender@dfb1b2a8ab3c29cd1024ae98dbc2bd4a7d164365+dirty`
- profile: `full-unrolled; reduced-unrolled-with-delegation; reduced-unified`

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `ASM-PRECOMP-001` | normative | carrier preprocessing | `external:DEC` | located | profile preprocessing and decoder-table construction at `dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:cs/src/gkr_circuits/decoder_trait.rs#preprocess_bytecode` |
| `ASM-PRECOMP-002` | normative | proof acceptance | `REQ-MACH-004`; `external:memory-permutation soundness` | located | shared memory/delegation product closure at `dfb1b2a8a` | `symbol:cs/src/gkr_compiler/memory_like_grand_product.rs#layout_initial_grand_product_accumulation`; `symbol:full_statement_verifier/src/unrolled_proof_statement.rs#verify_full_statement_for_unrolled_circuits`; `symbol:full_statement_verifier/src/unified_circuit_statement.rs#verify_full_statement_for_unified_circuit` |
| `REL-PRECOMP-001` | normative | selected carrier CSR | `ASM-PRECOMP-001` | located | delegation constants and preprocessing at `dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#DelegationType`; `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:common_constants/src/delegation_types/keccak_special5.rs#NUM_DELEGATION_CALLS_FOR_KECCAK_F1600` |
| `REQ-PRECOMP-002` | normative | full or reduced unrolled setup | `ASM-PRECOMP-001`, `REL-PRECOMP-001` | located | machine configuration and unrolled decoder setup at `dfb1b2a8a` | `symbol:riscv_transpiler/src/cycle/mod.rs#MachineConfig`; `symbol:circuit_defs/setups/src/unrolled_circuits/mod.rs#get_unrolled_circuits_setups_for_machine_type` |
| `REQ-PRECOMP-003` | provisional | reduced-unified setup | `ASM-PRECOMP-001`, `REL-PRECOMP-001`; `GAP-PRECOMP-001` | located | unified decoder setup and prover at `dfb1b2a8a` | `symbol:circuit_defs/setups/src/unrolled_circuits/unifier_reduced_machine_circuit/mod.rs#unified_reduced_machine_circuit_setup`; `symbol:program_prover/src/unified.rs#prove_unified_execution_with_replayer_with_unified_config` |
| `REQ-PRECOMP-004` | normative | admitted `δ` | `REQ-PRECOMP-002` or `REQ-PRECOMP-003`; linked relation module | located | runtime dispatch and fixed-type setup construction at `dfb1b2a8a` | `symbol:riscv_transpiler/src/replayer/instructions/add_sub_family/delegation.rs#call_delegation`; `symbol:circuit_defs/setups/src/circuits/mod.rs#produce_verifier_setup_for_all_delegations` |
| `REL-PRECOMP-005` | normative | active executor or fulfillment row | `ASM-PRECOMP-002`, `REQ-PRECOMP-004` | located | executor constraints and mirrored fulfillment compilation at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/add_sub_family/circuit.rs#apply_add_sub_lui_auipc_mop_inner`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/add_sub_lui_auipc_mop.rs#apply_unified_add_sub_lui_auipc_mop_inner`; `symbol:cs/src/gkr_compiler/delegation_circuit.rs#compile_delegation_circuit`; `symbol:cs/src/gkr_compiler/memory_like_grand_product.rs#layout_initial_grand_product_accumulation` |
| `GAP-PRECOMP-001` | open | — | affects `REQ-PRECOMP-003`; owner: human | — | unified setup/prover admit four types while the named reduced machine configuration declares two | — |
