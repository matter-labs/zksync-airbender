# B2ROUND: BLAKE2s round and compression delegation

> Relation for `Blake2sWithCompressionDelegationCircuit`; the standalone G-function
> delegation, transcript use of BLAKE2s, and the global delegation argument are out of
> scope.

`*` marks an Airbender-specific relation whose intended ABI is currently supported
primarily by implementation evidence.

## Supported operations

- one BLAKE2s round in a 10-round BLAKE2s compression
- one BLAKE2s round in a reduced 7-round compression
- direct block mode over a caller-supplied chaining value and message block
- two-to-one compression mode over two eight-word nodes

The 10-round permutation is the BLAKE2s compression permutation standardized by
[RFC 7693](https://www.rfc-editor.org/rfc/rfc7693.html#section-3.2). Seven-round mode
uses the first seven standard BLAKE2s rounds and is an Airbender-specific variant.

## Inputs

- `u32 = [0, 2³²)` is the unsigned 32-bit word domain
- `execute ∈ {0, 1}` activates one fulfillment row
- `p_state, p_input ∈ u32` are the values read from `x10` and `x11`
- `control ∈ u32` is the value read from `x12`
- `H = (H₀, …, H₇) ∈ u32⁸` is the chaining state at
  `RAM[p_state + 4i]`
- `V = (V₀, …, V₁₅) ∈ u32¹⁶` is the extended state at
  `RAM[p_state + 4(8 + i)]`
- `M = (M₀, …, M₁₅) ∈ u32¹⁶` is the input at
  `RAM[p_input + 4i]`
- `red = control[16]`, `right = control[17]`, and `compress = control[18]`
- `sᵢ = control[19 + i]` for `i ∈ [0, 10)` is the round-selector bit
- every sum `Σᵢ` in this module ranges over `i ∈ [0, 10)`
- `ROTRₙ(x)` rotates the `u32` word `x` right by `n` bits
- `⊕` denotes bitwise XOR on `u32`
- `X || Y` concatenates word vectors; BLAKE2s serializes each word little-endian
- `x ← expression` assigns the expression to `x`; the right-hand side uses
  pre-transition values and unassigned locations remain unchanged

## Assumptions

- **ASM-B2ROUND-001* — Authenticated carrier.** Preprocessing authenticates
  `IN-B2ROUND-001` and dispatches each carrier position as delegation type `0x7c7`.
- **ASM-B2ROUND-002 — Delegation closure.** The global delegation argument matches
  each carrier invocation to one active fulfillment row with the same type and
  invocation timestamp.
- **ASM-B2ROUND-003 — Register and RAM consistency.** Register and indirect-memory
  accesses participate in the global memory argument, which supplies their preceding
  values and orders their writes.

## Canonical relation tree

> Interpret this tree under `IN-B2ROUND-001..002` and `ASM-B2ROUND-001..003`.
> Equations beneath the numbered statements are conjoined.

- **[`IN-B2ROUND-001*`] Complete carrier run**
  - the run contains `n` consecutive encodings of `CSRRW x0, 0x7c7, x0`
  - the first invocation has `s₀ = 1`
  - `red = 1 ⇒ n = 7`
  - `red = 0 ⇒ n = 10`
- **[`IN-B2ROUND-002*`] Caller ABI at run entry**
  - `p_state ≥ 2²²`
  - `p_input ≥ 2²²`
  - `p_state ≠ p_input`
  - `control[15:0] = 0`
  - `control[31:29] = 0`
  - `Σᵢ sᵢ = 1`
  - `r` is the unique index for which `sᵣ = 1`
- **`execute = 0`**
  - no synthetic-register, ordinary-register, or RAM contribution
- **`execute = 1`**
  - **[`REL-B2ROUND-001*`] Delegated-row ABI**
    - `p_state mod 128 = 0`
    - `p_input mod 64 = 0`
    - delegation type `= 0x7c7`
    - **[`REL-B2ROUND-002*`] Control transition**
      - `red, right, compress, s₀, …, s₉ ∈ {0, 1}`
      - `s₀′ = 0`
      - `sᵢ′ = sᵢ₋₁` for `i ∈ [1, 10)`
      - `control ← 2¹⁶(red + 2 · right + 4 · compress + 8Σᵢ 2ⁱ · sᵢ′)`
    - **[`REL-B2ROUND-003`] BLAKE2s G function**
      - `a ← (a + b + x) mod 2³²`
      - `d ← ROTR₁₆(d ⊕ a)`
      - `c ← (c + d) mod 2³²`
      - `b ← ROTR₁₂(b ⊕ c)`
      - `a ← (a + b + y) mod 2³²`
      - `d ← ROTR₈(d ⊕ a)`
      - `c ← (c + d) mod 2³²`
      - `b ← ROTR₇(b ⊕ c)`
    - **[`REL-B2ROUND-004`] BLAKE2s round `Roundᵣ`**
      - let `mᵢ = B[σ[r][i]]`
      - `G(W, 0, 4, 8, 12, m₀, m₁)`
      - `G(W, 1, 5, 9, 13, m₂, m₃)`
      - `G(W, 2, 6, 10, 14, m₄, m₅)`
      - `G(W, 3, 7, 11, 15, m₆, m₇)`
      - `G(W, 0, 5, 10, 15, m₈, m₉)`
      - `G(W, 1, 6, 11, 12, m₁₀, m₁₁)`
      - `G(W, 2, 7, 8, 13, m₁₂, m₁₃)`
      - `G(W, 3, 4, 9, 14, m₁₄, m₁₅)`
    - **[`REL-B2ROUND-005*`] Round input**
      - **`r ≠ 0`**
        - `W = V`
      - **`r = 0 ∧ compress = 0`**
        - `W = (H₀, …, H₇, IV₀, IV₁, IV₂, IV₃, V₁₂, IV₅, V₁₄, IV₇)`
      - **`r = 0 ∧ compress = 1`**
        - `W = (Hcfg₀, …, Hcfg₇, IV₀, IV₁, IV₂, IV₃, IV₄ ⊕ 64, IV₅, IV₆ ⊕ 0xffffffff, IV₇)`
      - **`compress = 0`**
        - `B = M`
      - **`compress = 1 ∧ right = 0`**
        - `B = H || (M₀, …, M₇)`
      - **`compress = 1 ∧ right = 1`**
        - `B = (M₀, …, M₇) || H`
      - `W ← Roundᵣ(W, B)`
    - **[`REL-B2ROUND-006*`] State assignment**
      - `V ← W`
      - **`r = 9 ∨ (red = 1 ∧ r = 6)`**
        - `Hᵢ ← Hbaseᵢ ⊕ Wᵢ ⊕ Wᵢ₊₈` for `i ∈ [0, 8)`
        - `Hbase = Hcfg` when `compress = 1`
        - `Hbase = H` when `compress = 0`
    - **[`REL-B2ROUND-007*`] RAM assignment**
      - `RAM[p_state + 4i] ← Hᵢ` for `i ∈ [0, 8)`
      - `RAM[p_state + 4(8 + i)] ← Vᵢ` for `i ∈ [0, 16)`
    - **[`REL-B2ROUND-008*`] Run expansion and timestamps**
      - for `j ∈ [0, n)`, carrier cycle timestamp `Tⱼ = T₀ + 4j`
      - invocation timestamp `τⱼ = Tⱼ + 1`
      - register and indirect-memory access timestamp `= τⱼ + 2`
      - one carrier and one fulfillment synthetic-register item share
        `(type, timestamp) = (0x7c7, τⱼ)`

Here `G(W, a, b, c, d, x, y)` applies `REL-B2ROUND-003` to the indexed words
of `W`. The assignments within one G call are ordered. The eight G calls within
`Roundᵣ` are ordered as written in two groups of four; calls within either group
operate on disjoint word positions.

The constants are:

`IV = (0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19)`

`Hcfg = (IV₀ ⊕ 0x01010020, IV₁, …, IV₇)`

The round schedules are the RFC 7693 BLAKE2s schedules:

```text
σ[0] =  0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15
σ[1] = 14 10  4  8  9 15 13  6  1 12  0  2 11  7  5  3
σ[2] = 11  8 12  0  5  2 15 13 10 14  3  6  7  1  9  4
σ[3] =  7  9  3  1 13 12 11 14  2  6  5 10  4  0 15  8
σ[4] =  9  0  5  7  2  4 10 15 14  1 11 12  6  8  3 13
σ[5] =  2 12  6 10  0 11  8  3  4 13  7  5 15 14  1  9
σ[6] = 12  5  1 15 14 13  4 10  0  7  6  3  9  2  8 11
σ[7] = 13 11  7 14 12  1  3  9  5  0 15  4  8  6  2 10
σ[8] =  6 15 14  9 11  3  0  8 12  2 13  7  1  4 10  5
σ[9] = 10  2  8  4  7  6  1  5 15 11  9 14  3 12 13  0
```

## Derived facts

- **Full direct mode**
  `red = 0 ∧ compress = 0 ∧ V₁₂ = IV₄ ⊕ t ∧ V₁₄ = IV₆ ⊕ f ⇒ H` is the
  RFC 7693 BLAKE2s compression result, where `t ∈ u32` and
  `f ∈ {0, 0xffffffff}`
- **Full two-to-one mode**
  `red = 0 ∧ compress = 1 ⇒ H = BLAKE2s-256(left || right)` for one
  64-byte block
- **Reduced mode**
  `red = 1 ⇒` only `σ[0]..σ[6]` are applied
- **Final control value**
  `red = 0 ⇒ control = 2¹⁶(red + 2 · right + 4 · compress)` after the run
  `red = 1 ⇒ control = 2¹⁶(red + 2 · right + 4 · compress + 2¹⁰)` after the run
- **Word domains**
  `H ∈ u32⁸`
  `V, M ∈ u32¹⁶`
- **Memory footprint**
  state window `= 96` bytes
  input window `= 64` bytes
- **Non-wrapping indirect addresses**
  `p_state + 92 ∈ u32`
  `p_input + 60 ∈ u32`

## Open boundary

- **GAP-B2ROUND-001 — Airbender ABI adoption.** Adopt or revise the carrier count,
  CSR/register roles, control-bit layout, pointer conditions, timestamp offsets,
  reduced-round variant, and partial-overlap policy described by
  `IN-B2ROUND-001..002` and the starred relations.
- **GAP-B2ROUND-002 — Round-selector enforcement.** The circuit boolean-constrains
  all ten selector bits but does not constrain their sum to one. Add that constraint
  or explicitly broaden the accepted relation beyond the complete-run ABI.
- **GAP-B2ROUND-003 — Carrier-only pointer checks.** ROM exclusion and
  `p_state ≠ p_input` are asserted by VM/replayer execution but are not locally
  constrained by the fulfillment circuit. Decide which proof component owns these
  conditions.

## Metadata

The standard G function, ten schedules, full-round count, IV, parameter-block twist,
and full compression relation adopt
[RFC 7693 §2.6–2.7, §3.2](https://www.rfc-editor.org/rfc/rfc7693.html).
Airbender's carrier and fulfillment ABI are inspected at the implementation revision
below.

- spec revision: `2026-09-02.1`
- implementation: `matter-labs/zksync-airbender@dfb1b2a8a`
- profile: `Blake2sWithCompressionDelegationCircuit`; full and reduced delegated runs

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `IN-B2ROUND-001` | provisional | carrier entry | `GAP-B2ROUND-001` | located | carrier preprocessing and RISC-V wrapper at `dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:common_constants/src/delegation_types/blake2s_with_control.rs#blake_csr_trigger_delegation_reduced_rounds`; `symbol:common_constants/src/delegation_types/blake2s_with_control.rs#blake_csr_trigger_delegation_full_rounds` |
| `IN-B2ROUND-002` | provisional | carrier entry | `GAP-B2ROUND-001..003` | located | caller and VM ABI at `dfb1b2a8a` | `symbol:blake2s_u32/src/state_with_extended_control/round_function_delegation_impl.rs#Blake2RoundFunctionEvaluator`; `symbol:riscv_transpiler/src/vm/delegations/blake2_round_function.rs#blake2_round_function_call` |
| `ASM-B2ROUND-001` | provisional | admitted carrier run | `external:PRECOMP`; `GAP-B2ROUND-001` | located | `repo:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode@dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode` |
| `ASM-B2ROUND-002` | normative | active fulfillment row | `REL-PRECOMP-005`; `external:delegation-global-argument` | located | delegation compiler at `dfb1b2a8a` | `symbol:cs/src/gkr_compiler/delegation_circuit.rs#GKRCompiler::compile_delegation_circuit` |
| `ASM-B2ROUND-003` | normative | active fulfillment row | `external:MEM`; `external:REG` | located | delegation memory compiler at `dfb1b2a8a` | `symbol:cs/src/gkr_compiler/delegation_mem_accesses.rs#compile_register_and_indirect_mem_accesses` |
| `REL-B2ROUND-001` | provisional | active fulfillment row | `IN-B2ROUND-002`, `ASM-B2ROUND-002..003`; `GAP-B2ROUND-001` | located | `repo:cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/mod.rs#define_blake2_with_extended_control_delegation_circuit@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/mod.rs#define_blake2_with_extended_control_delegation_circuit`; `symbol:riscv_transpiler/src/witness/delegation/blake2_round_function.rs#Blake2sRoundFunctionAbiDescription` |
| `REL-B2ROUND-002` | provisional | active fulfillment row | `IN-B2ROUND-001`, `REL-B2ROUND-001`; `GAP-B2ROUND-001..002` | located | control-bit constraints and honest progression at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/mod.rs#define_blake2_with_extended_control_delegation_circuit`; `symbol:riscv_transpiler/src/replayer/delegations/blake2_round_function.rs#blake2_round_function_call` |
| `REL-B2ROUND-003` | normative | active fulfillment row | word inputs | located | [RFC 7693 §3.1](https://www.rfc-editor.org/rfc/rfc7693.html#section-3.1); circuit G constraints at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/g_function.rs#g_function` |
| `REL-B2ROUND-004` | normative | active fulfillment row with `r ∈ [0, 10)` | `REL-B2ROUND-003` | located | [RFC 7693 §2.7, §3.2](https://www.rfc-editor.org/rfc/rfc7693.html#section-3.2); round circuit at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/mod.rs#define_blake2_with_extended_control_delegation_circuit` |
| `REL-B2ROUND-005` | provisional | active fulfillment row | `IN-B2ROUND-002`, `REL-B2ROUND-004`; `GAP-B2ROUND-001` | located | mode-selection circuit, VM, and caller wrapper at `dfb1b2a8a`; RFC 7693 full-compression initialization | `symbol:cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/mod.rs#define_blake2_with_extended_control_delegation_circuit`; `symbol:riscv_transpiler/src/vm/delegations/blake2_round_function.rs#blake2_round_function_call`; `symbol:blake2s_u32/src/state_with_extended_control/round_function_delegation_impl.rs#Blake2RoundFunctionEvaluator` |
| `REL-B2ROUND-006` | provisional | active fulfillment row | `REL-B2ROUND-002`, `REL-B2ROUND-005`; `GAP-B2ROUND-001` | located | final-XOR and state-write constraints at `dfb1b2a8a`; [RFC 7693 §3.2](https://www.rfc-editor.org/rfc/rfc7693.html#section-3.2) | `symbol:cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/mod.rs#define_blake2_with_extended_control_delegation_circuit` |
| `REL-B2ROUND-007` | provisional | active fulfillment row | `REL-B2ROUND-001`, `REL-B2ROUND-006`, `ASM-B2ROUND-003`; `GAP-B2ROUND-001` | located | circuit ABI and witness description at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/mod.rs#define_blake2_with_extended_control_delegation_circuit`; `symbol:riscv_transpiler/src/witness/delegation/blake2_round_function.rs#Blake2sRoundFunctionAbiDescription` |
| `REL-B2ROUND-008` | provisional | admitted carrier run | `IN-B2ROUND-001`, `ASM-B2ROUND-001..002`; `GAP-B2ROUND-001` | located | carrier expansion and delegation witness production at `dfb1b2a8a` | `symbol:riscv_transpiler/src/replayer/delegations/blake2_round_function.rs#blake2_round_function_call`; `symbol:common_constants/src/timestamps.rs#TIMESTAMP_STEP`; `symbol:common_constants/src/lib.rs#DELEGATION_INVOCATION_OFFSET` |
| `GAP-B2ROUND-001` | open | — | affects all starred statements; owner: human | — | Airbender-specific ABI has implementation and wrapper evidence but no adopted design decision | — |
| `GAP-B2ROUND-002` | open | — | affects `REL-B2ROUND-002`; owner: implementation | — | source TODO confirms missing one-hot selector constraint | `pattern:cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/mod.rs#TODO:for all cases that we care round bitmask is exclusive` |
| `GAP-B2ROUND-003` | open | — | affects `IN-B2ROUND-002`; owner: human | — | VM/replayer assert ROM exclusion and unequal bases; fulfillment constraints enforce only alignment | — |
