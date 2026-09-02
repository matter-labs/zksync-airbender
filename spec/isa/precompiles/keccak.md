# KECCAK: Keccak-f[1600] `special5` delegation

> Exact relation of `KeccakSpecial5DelegationCircuit`; sponge padding, absorption,
> squeezing, and SHA-3 digest formatting are out of scope.

`*` marks an Airbender-specific relation whose intendedness is supported primarily by
implementation evidence and remains subject to `GAP-KECCAK-001`.

## Supported operations

- `649 × CSRRW x0, 0x7cb, x0` transforms the 25-lane state at the pointer in `x11`
  by Keccak-f[1600]

Admission is confirmed for the full unrolled profile; reduced-unified admission is
conditional on `GAP-PRECOMP-001` in [the precompile profile](profile.md). `x10`
carries the internal micro-operation control and is not a Keccak state lane.

## Inputs

- `u32 = [0, 2³²)` and `u64 = [0, 2⁶⁴)` are unsigned word domains
- `execute ∈ {0, 1}` activates one fulfillment row
- `p ∈ u32` is the value read from `x11`
- `S_j ∈ u64`, `j ∈ [0, 31)`, is the little-endian value stored at
  `p + 8j`, reconstructed from the `u32` words at `p + 8j` and `p + 8j + 4`
- `S_0..S_24` are the Keccak state lanes and `S_25..S_30` are scratch lanes
- `c ∈ u32` is the control value read from `x10`
- `c = m + 8i + 64r` defines mode `m`, iteration `i`, and round index `r`
- `c_next = m_next + 8i_next + 64r_next` is the control value written to `x10`
- `P₀(x, y) = x + 5y` and
  `Pᵣ₊₁(y, (2x + 3y) mod 5) = Pᵣ(x, y)` map a logical lane to its physical
  state index after `r` accumulated π steps
- `RC_r ∈ u64`, `r ∈ [0, 24)`, and `ρ[x, y] ∈ [0, 64)` are the Keccak-f[1600]
  round constants and rotation offsets
- `rotl₆₄(a, n)` rotates `a ∈ u64` left by `n` bits
- `⊕`, `∧`, and `¬` are bitwise XOR, AND, and complement on `u64`
- Assignments within one micro-operation are simultaneous and use pre-operation values

## Assumptions

- **ASM-KECCAK-001* — Authenticated carrier run.** Preprocessing authenticates one
  uninterrupted run of exactly 649 carriers as delegation type `0x7cb` in the full
  unrolled profile
- **ASM-KECCAK-002 — Register and RAM consistency.** The global memory argument binds
  the `x10` and `x11` accesses and every indirect `u32` read/write described below
- **ASM-KECCAK-003 — Delegation closure.** Every machine invocation is matched by one
  fulfillment row with the same delegation type and invocation timestamp
- **ASM-KECCAK-004* — Caller ABI.** Immediately before the carrier run, `x10 = 0` and
  `x11 = p`, where bytes `[p, p + 248)` are initialized mutable RAM

## Canonical relation tree

> Interpret the tree under `ASM-KECCAK-001..004`. The equations under an active row
> are conjoined. A complete carrier run follows the control path in
> `REL-KECCAK-001` from `c₀ = 0` through `c₆₄₉ = 1544`.

- **`execute = 0`** Inactive padding row with no register, RAM, or delegation effect
- **`execute = 1`**
  - **[`REL-KECCAK-001*`] Control transition**
    - **`m ∈ {0, 3, 4} ∧ i < 4`**
      `(m_next, i_next, r_next) = (m, i + 1, r)`
    - **`m ∈ {0, 3, 4} ∧ i = 4`**
      `(m_next, i_next, r_next) = (m + 1, 0, r)`
    - **`m ∈ {1, 2, 5}`**
      `(m_next, i_next, r_next) = (m + 1, i, r)`
    - **`m = 6 ∧ i < 4`**
      `(m_next, i_next, r_next) = (5, i + 1, r)`
    - **`m = 6 ∧ i = 4`**
      `(m_next, i_next, r_next) = (0, 0, r + 1)`
    - `c_next = m_next + 8i_next + 64r_next`
  - **[`REL-KECCAK-002*`] Selected six-lane transformation**
    - **`m = 0` — deferred ι and column parity**
      `q_y = Pᵣ(i, y)` for `y ∈ [0, 5)`
      `K = RC_{r−1}` when `i = 0 ∧ r > 0`, and `K = 0` otherwise
      `z = S_{q₀} ⊕ K`
      `S_{q₀} ← z`
      `S_{25+i} ← z ⊕ S_{q₁} ⊕ S_{q₂} ⊕ S_{q₃} ⊕ S_{q₄}`
    - **`m = 1` — first D-lane mix**
      `S₂₅ ← S₂₅ ⊕ rotl₆₄(S₂₇, 1)`
      `S₂₇ ← S₂₇ ⊕ rotl₆₄(S₂₉, 1)`
      `S₃₀ ← rotl₆₄(S₂₅, 1)`
    - **`m = 2` — second D-lane mix**
      `S₂₆ ← S₂₆ ⊕ rotl₆₄(S₂₈, 1)`
      `S₂₈ ← S₂₈ ⊕ S₃₀`
      `S₂₉ ← S₂₉ ⊕ rotl₆₄(S₂₆, 1)`
    - **`m = 3` — θ column update**
      `d = S_{[29, 25, 26, 27, 28]_i}`
      `S_{Pᵣ(i,y)} ← S_{Pᵣ(i,y)} ⊕ d` for `y ∈ [0, 5)`
    - **`m = 4` — ρ rotations**
      `S_{Pᵣ(i,y)} ← rotl₆₄(S_{Pᵣ(i,y)}, ρ[i,y])` for `y ∈ [0, 5)`
    - **`m = 5` — first χ half-row**
      `q_x = Pᵣ₊₁(x, i)` for `x ∈ [1, 5)`
      `S_{q₁} ← S_{q₁} ⊕ (¬S_{q₂} ∧ S_{q₃})`
      `S_{q₂} ← S_{q₂} ⊕ (¬S_{q₃} ∧ S_{q₄})`
      `S₂₅ ← ¬S_{q₁} ∧ S_{q₂}`
      `S₂₆ ← S_{q₁}`
    - **`m = 6` — second χ half-row**
      `q_x = Pᵣ₊₁(x, i)` for `x ∈ {0, 3, 4}`
      `S_{q₀} ← S_{q₀} ⊕ S₂₅`
      `S_{q₃} ← S_{q₃} ⊕ (¬S_{q₄} ∧ S_{q₀})`
      `S_{q₄} ← S_{q₄} ⊕ (¬S_{q₀} ∧ S₂₆)`
  - **[`REL-KECCAK-003*`] Register, RAM, and delegation effects**
    `p mod 256 = 0`
    `x10 ← c_next`
    Each selected `S_j` emits read/write accesses to `p + 8j` and `p + 8j + 4`
    If the carrier-cycle base timestamp is `t`, then the invocation timestamp is
    `τ = t + 1` and the `x10`, `x11`, and twelve RAM-word accesses occur at `τ + 2`
    `x10` and the selected RAM words are written
    Every corresponding read timestamp is strictly less than `τ + 2`
    The fulfillment item has delegation type `0x7cb` and invocation timestamp `τ`
- **649-row carrier run**
  - **[`REL-KECCAK-004`] Keccak-f[1600] state transformation**
    `c₀ = 0`
    `c₆₄₉ = 1544`
    `A₀[x,y] = S_{P₀(x,y)}`
    For `r ∈ [0, 24)`:
    `C[x] = ⊕_{y=0}⁴ Aᵣ[x,y]`
    `D[x] = C[(x − 1) mod 5] ⊕ rotl₆₄(C[(x + 1) mod 5], 1)`
    `T[x,y] = Aᵣ[x,y] ⊕ D[x]`
    `B[y,(2x + 3y) mod 5] = rotl₆₄(T[x,y], ρ[x,y])`
    `U[x,y] = B[x,y] ⊕ (¬B[(x + 1) mod 5,y] ∧ B[(x + 2) mod 5,y])`
    `Aᵣ₊₁[0,0] = U[0,0] ⊕ RC_r`
    `Aᵣ₊₁[x,y] = U[x,y]` for `(x,y) ≠ (0,0)`
    `S_{P₂₄(x,y)} ← A₂₄[x,y]`

## Derived facts

- **Micro-operations per round**
  `5 + 1 + 1 + 5 + 5 + 5 · 2 = 27`
- **Calls per permutation**
  `24 · 27 + 1 = 649`
- **Final physical lane order**
  `P₂₄ = P₀`
- **Architectural effects**
  `x10 ← 1544`
- **Scratch independence**
  `S₀..S₂₄` after the run are independent of the initial values of `S₂₅..S₃₀`
- **State domain**
  `S_j ∈ u64` for `j ∈ [0, 31)`

## Open boundary

- **GAP-KECCAK-001 — Adopt the `special5` ABI and decomposition.** Confirm the exact
  649-call control schedule, six scratch lanes, `x10`/`x11` roles, 256-byte alignment,
  indirect-access timestamps, and final scratch-state convention as intended project
  behavior rather than implementation-specific machinery

## Metadata

The final 25-lane relation adopts [NIST FIPS 202](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf),
§3.2, and is corroborated by the Keccak team's
[Keccak specifications summary](https://keccak.team/keccak_specs_summary.html). The
carrier ABI and micro-operation schedule are Airbender-specific.

- spec revision: `2026-09-02.1`
- implementation: `matter-labs/zksync-airbender@dfb1b2a8a`
- profile: full unrolled; reduced unified conditional on `GAP-PRECOMP-001`; domain
  size `2²²`

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `ASM-KECCAK-001` | provisional | complete carrier run | `GAP-KECCAK-001`; `external:PRECOMP` | located | carrier preprocessing and profile admission at `dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:riscv_transpiler/src/cycle/mod.rs#IMStandardIsaConfigUnsignedMulDivOnly` |
| `ASM-KECCAK-002` | normative | active fulfillment row | `external:REG`; `external:MEM` | located | delegation memory compiler at `dfb1b2a8a` | `symbol:cs/src/gkr_compiler/delegation_mem_accesses.rs#compile_register_and_indirect_mem_accesses` |
| `ASM-KECCAK-003` | normative | active fulfillment row | `REL-PRECOMP-005`; `external:delegation-global-argument` | located | delegation compilation and replay at `dfb1b2a8a` | `symbol:cs/src/gkr_compiler/delegation_circuit.rs#compile_delegation_circuit`; `symbol:riscv_transpiler/src/replayer/delegations/keccak_special5.rs#keccak_special5_call` |
| `ASM-KECCAK-004` | provisional | carrier-run entry | `GAP-KECCAK-001`; `external:caller` | located | guest ABI wrapper and VM assertions at `dfb1b2a8a` | `symbol:common_constants/src/delegation_types/keccak_special5.rs#keccak_f1600`; `symbol:riscv_transpiler/src/vm/delegations/keccak_special5.rs#keccak_special5_call` |
| `REL-KECCAK-001` | provisional | active fulfillment row | `ASM-KECCAK-001..004`; `GAP-KECCAK-001` | located | control constraints and witness transition at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/delegation/keccak_special5/mod.rs#define_keccak_special5_delegation_circuit`; `symbol:riscv_transpiler/src/vm/delegations/keccak_special5.rs#keccak_special5_impl_bump_control` |
| `REL-KECCAK-002` | provisional | active fulfillment row | `ASM-KECCAK-001..004`; `REL-KECCAK-001`; `GAP-KECCAK-001` | located | index, bitwise, rotation, and routing constraints at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/delegation/keccak_special5/mod.rs#define_keccak_special5_delegation_circuit`; `symbol:cs/src/tables/keccak_precompile_related.rs#create_keccak_permutation_indices_table`; `symbol:riscv_transpiler/src/vm/delegations/keccak_special5.rs#keccak_special5_impl_compute_outputs` |
| `REL-KECCAK-003` | provisional | active fulfillment row | `ASM-KECCAK-002..003`; `REL-KECCAK-001..002`; `GAP-KECCAK-001` | located | ABI description, compiler, and replay witness at `dfb1b2a8a` | `symbol:riscv_transpiler/src/witness/delegation/keccak_special5.rs#KeccakSpecial5AbiDescription`; `symbol:cs/src/gkr_compiler/delegation_mem_accesses.rs#compile_register_and_indirect_mem_accesses`; `symbol:riscv_transpiler/src/replayer/delegations/keccak_special5.rs#keccak_special5_call` |
| `REL-KECCAK-004` | normative | complete 649-row run | `REL-KECCAK-001..003` | located | [NIST FIPS 202 §3.2](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf); [Keccak specifications summary](https://keccak.team/keccak_specs_summary.html); host/circuit equivalence implementation at `dfb1b2a8a` | `symbol:riscv_transpiler/src/vm/delegations/keccak_special5.rs#keccak_f1600_impl_ext`; `symbol:cs/src/gkr_circuits/delegation/keccak_special5/mod.rs#define_keccak_special5_delegation_circuit` |
| `GAP-KECCAK-001` | open | — | affects `ASM-KECCAK-001`, `ASM-KECCAK-004`, and `REL-KECCAK-001..003`; owner: human | — | exact Airbender ABI and decomposition are supported primarily by implementation evidence | — |
