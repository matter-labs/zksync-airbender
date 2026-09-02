# BIGINT: 256-bit arithmetic with control

> Specifies one `BigIntDelegationCircuit` fulfillment; carrier-cycle PC behavior and
> the global delegation/RAM permutation checks are imported

`*` marks a provisional relation whose intended accepted domain conflicts with the honest
VM boundary

## Supported operations

- `ADD`: `a + b + κ`
- `SUB`: `a - b - κ`
- `SUB_NEGATE`: `b - a - κ`
- `MUL_LOW`: low half of `a · b`
- `MUL_HIGH`: high half of `a · b`
- `EQ`: equality test, preserving `a`
- `MEMCOPY`: copy the 32-byte value `b`, optionally incrementing it by `κ`

One `CSRRW x0, 0x7ca, x0` carrier invokes one fulfillment. Admission is confirmed for
the full unrolled profile; reduced-unified admission is conditional on
`GAP-PRECOMP-001` in [the precompile profile](profile.md)

## Inputs

- `u1 = {0, 1}`, `u8 = [0, 2⁸)`, `u16 = [0, 2¹⁶)`, `u32 = [0, 2³²)`,
  `u256 = [0, 2²⁵⁶)`, and `u512 = [0, 2⁵¹²)`
- `execute ∈ u1` activates one fulfillment row
- `δ = 0x7ca` is the bigint delegation type
- `t` is the carrier-cycle base timestamp
- `τ` is the invocation timestamp received from the delegation argument
- `p = x10 ∈ u32` is the destination pointer and `q = x11 ∈ u32` is the source
  pointer
- `control = x12 ∈ u32` is the pre-fulfillment control word
- `Aᵢ, Bᵢ, Rᵢ ∈ u32` for `i ∈ [0, 8)` are little-endian memory words
- `aⱼ, bⱼ, rⱼ ∈ u16` for `j ∈ [0, 16)` are little-endian arithmetic limbs
- `a, b, R ∈ u256` are the decoded operands and result
- `f ∈ u1` is the returned carry, borrow, overflow, or equality flag
- `κ ∈ u1` is the input carry or borrow bit
- `RAM[z]` denotes the 32-bit word at byte address `z`
- `x ← expression` assigns the expression to `x`; unassigned values remain unchanged
- `⟦P⟧ = 1` when predicate `P` holds and `0` otherwise

## Assumptions

- **ASM-BIGINT-001 — Delegation closure** The global delegation argument matches the
  carrier invocation and fulfillment by delegation type `δ` and timestamp `τ`
- **ASM-BIGINT-002 — Register and RAM consistency** Register and indirect-memory
  accesses satisfy the shared ordered-memory argument
- **ASM-BIGINT-003 — Word domains** Values supplied by the register and RAM arguments
  are 32-bit words represented by two 16-bit limbs

## Canonical relation tree

> Interpret the tree under `ASM-BIGINT-001..003`. Within `execute = 1`,
> `REL-BIGINT-001..005` are conjoined

- **`execute = 0`**
  - No register, RAM, or delegation contribution
- **`execute = 1`**
  - **[`REL-BIGINT-001*`] Control decoding**
    `c₀, ..., c₇ ∈ u1`
    `h ∈ u16`
    `control = Σᵢ₌₀⁷ cᵢ · 2ⁱ + h · 2¹⁶`
    `s = c₀ + c₁ + c₂ + c₃ + c₄ + c₅ + c₇`
    `s ∈ u1`
    `κ = c₆`
  - **[`REL-BIGINT-002`] Pointer and operand binding**
    `p mod 32 = 0`
    `q mod 32 = 0`
    `Aᵢ = RAM[p + 4i]`
    `Bᵢ = RAM[q + 4i]`
    `Aᵢ = a₂ᵢ + 2¹⁶ · a₂ᵢ₊₁`
    `Bᵢ = b₂ᵢ + 2¹⁶ · b₂ᵢ₊₁`
    `a = Σᵢ₌₀⁷ Aᵢ · 2³²ⁱ = Σⱼ₌₀¹⁵ aⱼ · 2¹⁶ʲ`
    `b = Σᵢ₌₀⁷ Bᵢ · 2³²ⁱ = Σⱼ₌₀¹⁵ bⱼ · 2¹⁶ʲ`
  - **[`REL-BIGINT-003`] Selected result**
    - **`s = 0`**
      `R = 0`
      `f = 0`
    - **`c₀ = 1`** `ADD`
      `T = a + b + κ`
      `R = T mod 2²⁵⁶`
      `f = ⌊T / 2²⁵⁶⌋`
    - **`c₁ = 1`** `SUB`
      `a + 2²⁵⁶ · f = R + b + κ`
      `f = ⟦a < b + κ⟧`
    - **`c₂ = 1`** `SUB_NEGATE`
      `b + 2²⁵⁶ · f = R + a + κ`
      `f = ⟦b < a + κ⟧`
    - **`c₃ = 1`** `MUL_LOW`
      `P = a · b`
      `R = P mod 2²⁵⁶`
      `f = ⟦P ≥ 2²⁵⁶⟧`
    - **`c₄ = 1`** `MUL_HIGH`
      `P = a · b`
      `R = ⌊P / 2²⁵⁶⌋`
      `f = 0`
    - **`c₅ = 1`** `EQ`
      `R = a`
      `f = ⟦a = b⟧`
    - **`c₇ = 1`** `MEMCOPY`
      `T = b + κ`
      `R = T mod 2²⁵⁶`
      `f = ⌊T / 2²⁵⁶⌋`
  - **[`REL-BIGINT-004`] State assignment**
    `Rᵢ = r₂ᵢ + 2¹⁶ · r₂ᵢ₊₁`
    `R = Σᵢ₌₀⁷ Rᵢ · 2³²ⁱ = Σⱼ₌₀¹⁵ rⱼ · 2¹⁶ʲ`
    `RAM[p + 4i] ← Rᵢ` for every `i ∈ [0, 8)`
    `x12 ← f`
  - **[`REL-BIGINT-005`] Timestamped fulfillment**
    `τ = t + 1`

    The accesses to `x10`, `x11`, `x12`, `RAM[p + 4i]`, and `RAM[q + 4i]` emit
    their read records at the supplied predecessor timestamps and their write records
    at `τ + 2`

    The fulfillment contributes the complementary delegation records

    `read = (Register, δ, τ, 0)`

    `write = (Register, δ, 0, 0)`

    The carrier contributes the opposite records under `ASM-BIGINT-001`

`κ` is ignored by `MUL_LOW`, `MUL_HIGH`, and `EQ`

## Derived facts

- **Operand and result domains**
  `a, b, R ∈ u256`
  `a · b ∈ u512`
- **Pointer-span bounds**
  `p + 28 ∈ u32`
  `q + 28 ∈ u32`
- **Result-word domains**
  `Rᵢ ∈ u32` for every `i ∈ [0, 8)`
- **Returned-flag domain**
  `x12 ∈ u1` after assignment

## Open boundary

- **GAP-BIGINT-001 — Control-word admissibility** The fulfillment circuit constrains
  `s ∈ u1`, so it admits `s = 0`, and it permits arbitrary `h ∈ u16`. The VM and
  public trigger require `control ∈ u8` with exactly one non-carry operation bit.
  Decide whether the circuit relation or the honest VM subset is normative, then enforce
  that decision consistently. This affects `REL-BIGINT-001`
- **GAP-BIGINT-002 — Pointer-domain admissibility** The VM and JIT require
  `p, q ≥ 2²²` and `p ≠ q`. The fulfillment circuit locally enforces only
  32-byte alignment; the global memory policy excludes destination writes to ROM but
  does not replace an explicit review of the source-region and aliasing boundaries.
  Decide and bind the accepted pointer domain

## Metadata

The arithmetic, limb encoding, register roles, memory offsets, and fulfillment records
are normative for the full unrolled bigint profile because the circuit constraints,
constants, VM, replayer, JIT, setup, and public trigger converge on them. Control-domain
behavior remains provisional only where the fulfillment constraints and honest runtime
checks conflict

- spec revision: `2026-09-02.1`
- implementation: `matter-labs/zksync-airbender@dfb1b2a8a`
- profile: full unrolled; reduced unified conditional on `GAP-PRECOMP-001`;
  `BigIntDelegationCircuit`, delegation type `0x7ca`

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `ASM-BIGINT-001` | normative | active fulfillment | `external:PRECOMP/delegation-argument-closure` | located | delegation compiler and full-profile carrier at `dfb1b2a8a` | `symbol:cs/src/gkr_compiler/delegation_circuit.rs#GKRCompiler::compile_delegation_circuit`; `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode` |
| `ASM-BIGINT-002` | normative | active fulfillment | `external:REG`; `external:MEM` | located | shared memory-like argument at `dfb1b2a8a` | `symbol:cs/src/gkr_compiler/delegation_mem_accesses.rs#compile_register_and_indirect_mem_accesses`; `symbol:cs/src/gkr_compiler/memory_like_grand_product.rs#layout_initial_grand_product_accumulation` |
| `ASM-BIGINT-003` | normative | active fulfillment | `external:REG`; `external:MEM`; `external:LOOKUP` | located | register/RAM representations and range checks at `dfb1b2a8a` | `symbol:cs/src/gkr_compiler/delegation_mem_accesses.rs#compile_register_and_indirect_mem_accesses`; `symbol:cs/src/gkr_circuits/delegation/bigint_with_control/mod.rs#define_bigint_with_extended_control_delegation_circuit` |
| `REL-BIGINT-001` | provisional | active fulfillment | `ASM-BIGINT-003`; `GAP-BIGINT-001` | located | conflicting fulfillment and VM control domains at `dfb1b2a8a` | `symbol:common_constants/src/delegation_types/bigint_with_control.rs#BIGINT_NUM_CONTROL_BITS`; `symbol:cs/src/gkr_circuits/delegation/bigint_with_control/mod.rs#define_bigint_with_extended_control_delegation_circuit`; `symbol:riscv_transpiler/src/vm/delegations/bigint.rs#bigint_impl` |
| `REL-BIGINT-002` | normative | active fulfillment | `ASM-BIGINT-002..003` | located | convergent ABI constants, fulfillment requests, VM, replayer, JIT, and example at `dfb1b2a8a`; `GAP-BIGINT-002` bounds the unresolved extra pointer restrictions | `symbol:common_constants/src/delegation_types/bigint_with_control.rs#BIGINT_BASE_ABI_REGISTER`; `symbol:cs/src/gkr_circuits/delegation/bigint_with_control/mod.rs#define_bigint_with_extended_control_delegation_circuit`; `symbol:riscv_transpiler/src/witness/delegation/bigint.rs#BigintAbiDescription`; `symbol:riscv_transpiler/src/replayer/delegations/bigint.rs#bigint_call`; `symbol:riscv_transpiler/src/jit/delegations/bigint.rs#bigint_implementation` |
| `REL-BIGINT-003` | normative | active fulfillment | `REL-BIGINT-001..002` | located | convergent fulfillment constraints and VM arithmetic at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/delegation/bigint_with_control/mod.rs#define_bigint_with_extended_control_delegation_circuit`; `symbol:riscv_transpiler/src/vm/delegations/bigint.rs#bigint_impl`; `symbol:common_constants/src/delegation_types/bigint_with_control.rs#bigint_csr_trigger_delegation` |
| `REL-BIGINT-004` | normative | active fulfillment | `ASM-BIGINT-002..003`; `REL-BIGINT-002..003` | located | convergent fulfillment, witness ABI, VM, and replayer effects at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/delegation/bigint_with_control/mod.rs#define_bigint_with_extended_control_delegation_circuit`; `symbol:riscv_transpiler/src/witness/delegation/bigint.rs#BigintAbiDescription`; `symbol:riscv_transpiler/src/vm/delegations/bigint.rs#bigint_call`; `symbol:riscv_transpiler/src/replayer/delegations/bigint.rs#bigint_call` |
| `REL-BIGINT-005` | normative | active fulfillment | `ASM-BIGINT-001..003`; `REL-BIGINT-004` | located | delegation access compiler and fulfillment grand product at `dfb1b2a8a` | `symbol:cs/src/gkr_compiler/delegation_mem_accesses.rs#compile_register_and_indirect_mem_accesses`; `symbol:cs/src/gkr_compiler/memory_like_grand_product.rs#layout_initial_grand_product_accumulation`; `symbol:prover/src/gkr/witness_gen/delegation_circuits/memory.rs#gkr_evaluate_indirect_memory_accesses` |
| `GAP-BIGINT-001` | open | — | affects `REL-BIGINT-001`; owner: human | — | fulfillment admits an empty selector and ignores the high control half while VM paths reject both | — |
| `GAP-BIGINT-002` | open | — | affects accepted input boundary; owner: human | — | VM/JIT pointer checks are not all visibly enforced by the fulfillment circuit | — |
