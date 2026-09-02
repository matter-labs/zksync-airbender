# B2G: Blake2s G-function delegation

> One fulfillment row proves one BLAKE2s G call; a carrier run sequences 56 or 80
> rows. Blake2s compression initialization and finalization are outside this module.

`*` marks a provisional relation whose intended boundary remains open.

## Supported operations

| Variant | `mode` | Initial `x12` | Rounds `R` | Carrier calls `N = 8R` |
|---|---:|---:|---:|---:|
| BLAKE2s full rounds | `0` | `0` | `10` | `80` |
| Airbender reduced rounds | `1` | `2⁷` | `7` | `56` |

The carrier is `CSRRW x0, 0x7c8, x0`. It is an Airbender delegation carrier,
not an architectural CSR operation. The full variant is the BLAKE2s round schedule;
the reduced variant applies its first seven rounds.

## Inputs

- `u7 = [0, 2⁷)`, `u8 = [0, 2⁸)`, and `u32 = [0, 2³²)` are unsigned
  integer domains
- `execute ∈ {0, 1}` activates a fulfillment row
- `L ∈ {56, 80}` is the authenticated carrier-run length
- `p_s = x10 ∈ u32` points to the 16-word extended state `V`
- `p_m = x11 ∈ u32` points to the 16-word message block `M`
- `x12 ∈ u8` contains `mode = x12[7]` and `q = x12[6:0]`
- `RAM[a] ∈ u32` is the word at byte address `a`
- `rotr_k(z)` rotates the 32-bit word `z` right by `k` bits
- `⊕` denotes bitwise XOR on `u32`
- `τ` is the invocation timestamp carried by the delegation argument
- `x ← expression` assigns the expression to `x`; unassigned state remains unchanged

For mixing-function number `j`, the state indexes are:

| `j` | `(a, b, c, d)` |
|---:|---|
| `0` | `(0, 4, 8, 12)` |
| `1` | `(1, 5, 9, 13)` |
| `2` | `(2, 6, 10, 14)` |
| `3` | `(3, 7, 11, 15)` |
| `4` | `(0, 5, 10, 15)` |
| `5` | `(1, 6, 11, 12)` |
| `6` | `(2, 7, 8, 13)` |
| `7` | `(3, 4, 9, 14)` |

The BLAKE2s message permutations are:

| `r` | `σ_r[0..15]` |
|---:|---|
| `0` | `0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15` |
| `1` | `14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3` |
| `2` | `11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4` |
| `3` | `7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8` |
| `4` | `9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13` |
| `5` | `2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9` |
| `6` | `12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11` |
| `7` | `13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10` |
| `8` | `6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5` |
| `9` | `10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0` |

## Assumptions

- **ASM-B2G-001 — Authenticated carrier.** Preprocessing authenticates a complete run
  of exactly `56` or `80` identical `CSRRW x0, 0x7c8, x0` words and admits the
  Blake2s G-function delegation in the selected machine profile
- **ASM-B2G-002 — Register and memory consistency.** Register and indirect-memory
  records satisfy the global register/RAM argument; state writes address mutable RAM
- **ASM-B2G-003 — Delegation closure.** Invocation and fulfillment multisets match on
  delegation type, invocation timestamp, and zero value
- **ASM-B2G-004 — Carrier continuity.** Consecutive carrier cycles have timestamps
  `t_k = t_0 + 4k`, and their PCs advance by four under the selected ISA relation

## Canonical relation tree

> Interpret this tree under `ASM-B2G-001..004`. Within `execute = 1`, the selected
> counter branch and `REL-B2G-003..005` are conjoined.

- **`execute = 0`**
  - No register, RAM, or delegation-argument effect
- **`execute = 1`**
  - `mode = x12[7]`
  - `R = 7` if `mode = 1`; otherwise `R = 10`
  - `N = 8R`
  - **`q < N` — [`REL-B2G-001`] Scheduled row and control**
    - `i = q`
    - `x12 ← 2⁷ · mode + ((q + 1) mod N)`
  - **`q ≥ N` — [`REL-B2G-002*`] Out-of-range fallback**
    - `i = 0`
    - `x12 ← 2⁷ · mode`
  - **[`REL-B2G-003`] BLAKE2s G relation**
    - `r = ⌊i / 8⌋`
    - `j = i mod 8`
    - `(a, b, c, d)` is row `j` of the state-index table
    - `X = M[σ_r[2j]]`
    - `Y = M[σ_r[2j + 1]]`
    - `A₀ = V[a]`, `B₀ = V[b]`, `C₀ = V[c]`, `D₀ = V[d]`
    - `A₁ = (A₀ + B₀ + X) mod 2³²`
    - `D₁ = rotr₁₆(D₀ ⊕ A₁)`
    - `C₁ = (C₀ + D₁) mod 2³²`
    - `B₁ = rotr₁₂(B₀ ⊕ C₁)`
    - `A₂ = (A₁ + B₁ + Y) mod 2³²`
    - `D₂ = rotr₈(D₁ ⊕ A₂)`
    - `C₂ = (C₁ + D₂) mod 2³²`
    - `B₂ = rotr₇(B₁ ⊕ C₂)`
  - **[`REL-B2G-004`] Carrier ABI and RAM assignment**
    - `p_s mod 64 = 0`
    - `p_m mod 64 = 0`
    - `V[h] = RAM[p_s + 4h]` for `h ∈ {a, b, c, d}`
    - `M[h] = RAM[p_m + 4h]` for
      `h ∈ {σ_r[2j], σ_r[2j + 1]}`
    - `RAM[p_s + 4a] ← A₂`
    - `RAM[p_s + 4b] ← B₂`
    - `RAM[p_s + 4c] ← C₂`
    - `RAM[p_s + 4d] ← D₂`
  - **[`REL-B2G-005`] Delegation type and timestamps**
    - Delegation type `= 0x7c8`
    - Invocation value `= 0`
    - For carrier row `k`, `τ_k = t_0 + 4k + 1`
    - The three register accesses and six indirect-memory accesses occur at
      `τ_k + 2 = t_0 + 4k + 3`
    - `x12` and the four selected state words are written

## Derived facts

- **Complete supported run**
  `q₀ = 0 ∧ L = N ⇒ q_k = k` for `k ∈ [0, N)`
  `q_N = 0`
- **Round sequence**
  `i = 8r + j` for `r ∈ [0, R)` and `j ∈ [0, 8)`
- **32-bit values**
  `A₂, B₂, C₂, D₂ ∈ u32`
- **Address range**
  `p_s + 4h ∈ u32` and `p_m + 4h ∈ u32` for `h ∈ [0, 16)`

## Open boundary

- **GAP-B2G-001 — Out-of-range counter.** Decide whether `q ≥ N` must reject or
  retain the current fallback to G-function row zero
- **GAP-B2G-002 — Variant/run-length coupling.** Confirm the proof edge that requires
  the authenticated carrier length `L` to equal the `N` selected by `x12[7]`
- **GAP-B2G-003 — Input-pointer restrictions.** Decide whether the VM/replayer checks
  `p_m ≥ ROM_LIMIT` and `p_s ≠ p_m` are part of the proved ABI; the fulfillment
  circuit explicitly constrains alignment but not these two predicates

## Metadata

The G equations adopt [RFC 7693 §3.1](https://www.rfc-editor.org/rfc/rfc7693.html#section-3.1),
and the full schedule and ten message permutations adopt
[RFC 7693 §3.2](https://www.rfc-editor.org/rfc/rfc7693.html#section-3.2).
The seven-round variant and carrier ABI are Airbender-specific. Their normal-path
relations are supported by convergent API, preprocessing, VM/replayer, lookup-table,
constraint, and setup evidence.

- spec revision: `2026-09-02.1`
- implementation: `matter-labs/zksync-airbender@dfb1b2a8a`
- profile: full unrolled; reduced unrolled with delegation; reduced unified

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `ASM-B2G-001` | normative | complete carrier run | `REL-PRECOMP-001`; `external:DEC` | located | Airbender carrier preprocessing and profile configuration | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:riscv_transpiler/src/cycle/mod.rs#MachineConfig` |
| `ASM-B2G-002` | normative | active fulfillment row | `external:REG`; `external:MEM` | located | delegation register/indirect-memory compiler | `symbol:cs/src/gkr_compiler/delegation_mem_accesses.rs#compile_register_and_indirect_mem_accesses` |
| `ASM-B2G-003` | normative | active fulfillment row | `REL-PRECOMP-005`; `external:delegation-global-argument` | located | delegation-circuit grand-product construction | `symbol:cs/src/gkr_compiler/delegation_circuit.rs#compile_delegation_circuit` |
| `ASM-B2G-004` | normative | complete carrier run | `external:CONT` | located | carrier replay and machine continuity | `symbol:riscv_transpiler/src/replayer/delegations/blake2_g_function.rs#blake2_g_function_call` |
| `REL-B2G-001` | normative | `execute = 1 ∧ q < N` | `ASM-B2G-001..004` | located | Airbender control lookup and replay sequence | `symbol:cs/src/tables/blake_g_function_precompile_related.rs#create_blake_g_function_control_and_offsets_table`; `symbol:riscv_transpiler/src/replayer/delegations/blake2_g_function.rs#blake2_g_function_call` |
| `REL-B2G-002` | provisional | `execute = 1 ∧ q ≥ N` | `ASM-B2G-002..003`; `GAP-B2G-001` | located | current totalization of the Airbender control lookup | `symbol:cs/src/tables/blake_g_function_precompile_related.rs#create_blake_g_function_control_and_offsets_table` |
| `REL-B2G-003` | normative | `execute = 1` | selected `i` from `REL-B2G-001` or `REL-B2G-002` | located | [RFC 7693 §3.1](https://www.rfc-editor.org/rfc/rfc7693.html#section-3.1); [RFC 7693 §3.2](https://www.rfc-editor.org/rfc/rfc7693.html#section-3.2); Airbender G constraints | `symbol:cs/src/gkr_circuits/delegation/blake2_g_function/mod.rs#define_blake2_g_function_delegation_circuit`; `symbol:cs/src/gkr_circuits/delegation/blake2_round_with_extended_control/g_function.rs#g_function` |
| `REL-B2G-004` | normative | `execute = 1` | `ASM-B2G-002`; `REL-B2G-003` | located | Airbender API, ABI description, circuit access requests, and replay | `symbol:common_constants/src/delegation_types/blake2s_g_function.rs#blake_g_function_csr_trigger_delegation_full_rounds`; `symbol:common_constants/src/delegation_types/blake2s_g_function.rs#blake_g_function_csr_trigger_delegation_reduced_rounds`; `symbol:riscv_transpiler/src/witness/delegation/blake2_g_function.rs#Blake2sGFunctionAbiDescription`; `symbol:cs/src/gkr_circuits/delegation/blake2_g_function/mod.rs#define_blake2_g_function_delegation_circuit` |
| `REL-B2G-005` | normative | `execute = 1` | `ASM-B2G-003..004` | located | delegation constants, replay timestamps, and fulfillment allocation | `symbol:common_constants/src/delegation_types/blake2s_g_function.rs#BLAKE2S_G_FUNCTION_DELEGATION_CSR_REGISTER`; `symbol:common_constants/src/lib.rs#DELEGATION_INVOCATION_OFFSET`; `symbol:common_constants/src/lib.rs#DELEGATION_EXECUTION_OFFSET`; `symbol:riscv_transpiler/src/replayer/delegations/blake2_g_function.rs#blake2_g_function_call`; `symbol:cs/src/gkr_circuits/delegation/blake2_g_function/mod.rs#define_blake2_g_function_delegation_circuit` |
| `GAP-B2G-001` | open | — | affects `REL-B2G-002`; owner: human | — | circuit lookup accepts the fallback while VM/replayer entry requires `q = 0` | — |
| `GAP-B2G-002` | open | — | affects complete-run composition; owner: human | — | preprocessing authenticates `L ∈ {56, 80}` while fulfillment selects `N` from `x12[7]` | — |
| `GAP-B2G-003` | open | — | affects the input domain of `REL-B2G-004`; owner: human | — | VM/replayer assertions have no matching explicit circuit predicate | — |
