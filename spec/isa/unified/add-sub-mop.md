# UADD: Unified add, subtract, MOP, and machine-interface family

> Relation module for family 1 of the reduced unified executor. Precompile
> fulfillment and global delegation closure are specified by `PRECOMP`.

`*` marks a provisional custom relation supported primarily by implementation
evidence and the corresponding gap below.

## Supported operations

- `ADD rd, rs1, rs2`
- `ADDI rd, rs1, imm12`
- `LUI rd, imm20`
- `SUB rd, rs1, rs2`
- `AUIPC rd, imm20`
- `NOP`
- `MOP.RR.0 rd, rs1, rs2` (`ADDMOD`)
- `MOP.RR.1 rd, rs1, rs2` (`SUBMOD`)
- `MOP.RR.2 rd, rs1, rs2` (`MULMOD`)
- `MOP.RR.3 rd, rs1, rs2` (`FMAMOD`)
- `MOP.RR.4 rd, rs1, rs2` (`TRIADD`)
- `CSRRW rd, 0x7C0, x0` (`NONDETERMINISM_READ`)
- `CSRRW x0, 0x7C0, rs1` (`NONDETERMINISM_WRITE`)
- `CSRRW x0, 0x7C7, x0` (`BLAKE2S_WITH_CONTROL` delegation)
- `CSRRW x0, 0x7C8, x0` (`BLAKE2S_G_FUNCTION` delegation)
- `CSRRW x0, 0x7CA, x0` (`BIGINT_WITH_CONTROL` delegation)
- `CSRRW x0, 0x7CB, x0` (`KECCAK_SPECIAL5` delegation)

The preprocessor canonicalizes ordinary destination-writing instructions with
`rd = x0` to `NOP`. It also maps `NONDETERMINISM_WRITE` to the canonical NOP row
and maps delegation carriers to normalized delegation rows carrying their CSR
address `d`.

## Inputs

- `u12 = [0, 2¹²)`, `u16 = [0, 2¹⁶)`, `u20 = [0, 2²⁰)`, and
  `u32 = [0, 2³²)` are unsigned integer domains
- `pc ∈ u32` is the current program counter
- `execute ∈ {0, 1}` activates the cycle
- `rs1, rs2 ∈ u32` are pre-cycle register values
- `imm12 ∈ u12` and `imm20 ∈ u20` are encoded immediate fields
- `rd` is the destination register
- `η ∈ u32` is the value admitted by a nondeterminism-read row
- `p = 0x78000001 = 2³¹ − 2²⁷ + 1` is the BabyBear modulus
- `R = 2³²` is the Montgomery radix and `R⁻¹` is its inverse modulo `p`
- `d ∈ {0x7C7, 0x7C8, 0x7CA, 0x7CB}` is the authenticated delegation CSR address;
  the selected profile may admit a subset
- `τ₁` is the write timestamp of the executor's shared access slot 1
- `RegItem(a, t, v) = (Register, a, t, v)` is a register-argument item with
  address, timestamp, and value
- `sign_extend_12(x)` is the sign extension of `x ∈ u12` to `u32`
- `x ≪ n` shifts `x` left by `n` bits
- `x ← expression` assigns the expression to `x`; the right-hand side uses
  pre-cycle values and unassigned architectural locations remain unchanged

## Assumptions

- **ASM-UADD-001 — Decoder authentication.** For an active family-1 row, the
  unified decoder authenticates exactly one supported operation, its selected
  registers, immediate, delegation type, and one-hot family selector against the
  instruction at the current `pc`.
- **ASM-UADD-002 — Register consistency.** Register reads and writes, including
  the shared slot-1 access, satisfy the global register-memory argument.
- **ASM-UADD-003 — Zero register.** Reading `x0` returns `0`; assigning to `x0`
  preserves `0`.
- **ASM-UADD-004 — PC alignment.** The active decoder lookup binds `pc` to a
  table key of the form `4 · i`; therefore `pc mod 4 = 0` at cycle start.

## Canonical relation tree

> Interpret this tree under `ASM-UADD-001..004`. Within `execute = 1`, the
> selected operation relation and `REL-UADD-004` are conjoined.

- **`execute = 0`** Outside this module's active-row scope
- **`execute = 1`**
  - **[`REL-UADD-001`] Ordinary destination assignment**
    - **`op = ADD`**
      `rd ← (rs1 + rs2) mod 2³²`
    - **`op = ADDI`**
      `rd ← (rs1 + sign_extend_12(imm12)) mod 2³²`
    - **`op = LUI`**
      `rd ← imm20 ≪ 12`
    - **`op = SUB`**
      `rd ← (rs1 − rs2) mod 2³²`
    - **`op = AUIPC`**
      `rd ← (pc + (imm20 ≪ 12)) mod 2³²`
    - **`op = NOP`**
      `rd = x0`
      `rd ← 0`
  - **[`REL-UADD-002*`] Custom arithmetic assignment**
    - **`op = MOP.RR.0` (`ADDMOD`)**
      `rd ← (rs1 + rs2) mod p`
    - **`op = MOP.RR.1` (`SUBMOD`)**
      `rd ← (rs1 − rs2) mod p`
    - **`op = MOP.RR.2` (`MULMOD`)**
      `rd ← (rs1 · rs2 · R⁻¹) mod p`
    - **`op = MOP.RR.3` (`FMAMOD`)**
      `rd ← (rs1 · rs2 · R⁻¹ + rd) mod p`
    - **`op = MOP.RR.4` (`TRIADD`)**
      `rd ← (rs1 + rs2 + rd) mod 2³²`
    - `ADDMOD`, `SUBMOD`, `MULMOD`, and `FMAMOD` admit non-canonical `u32`
      operands and assign `rd ∈ [0, p)`
  - **[`REL-UADD-003*`] Nondeterminism interface**
    - **`op = CSRRW rd, 0x7C0, x0` (`NONDETERMINISM_READ`)**
      `rd ← η`
    - **`op = CSRRW x0, 0x7C0, rs1` (`NONDETERMINISM_WRITE`)**
      `rd = x0`
      `rd ← 0`
    - The executor imposes no predicate on `η` beyond `η ∈ u32`
  - **[`OUT-UADD-001*`] Delegation invocation**
    - **`op = CSRRW x0, d, x0` (`DELEGATION`)**
      `rd = x0`
      `rd ← 0`
      `T_exec^PRECOMP ← ({RegItem(d, 0, 0)}_read, {RegItem(d, τ₁, 0)}_write)`
    - PRECOMP owns the complementary pair
      `({RegItem(d, τ₁, 0)}_read, {RegItem(d, 0, 0)}_write)` and the delegated
      state computation
  - **[`REL-UADD-004`] Non-wrapping sequential PC assignment**
    `pc + 4 < 2³²`
    `pc ← pc + 4`

## Derived facts

- **Ordinary and three-input assignments**
  `rd ∈ u32`
- **Modular assignments**
  `rd ∈ [0, p)`
- **Sequential PC range**
  `pc ≤ 2³² − 8` before assignment
  `pc ≤ 2³² − 4` after assignment
- **PC alignment**
  `pc mod 4 = 0`
- **Register effects**
  Ordinary, custom-arithmetic, and nondeterminism-read rows change at most `rd`
  `NOP`, nondeterminism-write, and delegation rows change no architectural
  register value
  `x0 = 0`

## Open boundary

- **GAP-UADD-001 — Custom arithmetic adoption.** Adopt or replace the exact
  BabyBear Montgomery `ADDMOD`, `SUBMOD`, `MULMOD`, `FMAMOD`, and wrapping
  `TRIADD` redefinitions of `MOP.RR.0..4`, including acceptance of non-canonical
  `u32` operands.
- **GAP-UADD-002 — Nondeterminism contract.** Adopt the unconstrained `u32` read
  value and the circuit-level elision of nondeterminism-write values, and identify
  any external ordering or transcript relation intended to bind nondeterminism
  reads. Decide whether non-`CSRRW` Zicsr encodings currently accepted by
  preprocessing are admitted carriers or implementation aliases to reject.
- **GAP-UADD-003 — Delegation invocation adoption.** Adopt the executor-side
  virtual-register encoding and determine the exact delegation-type set admitted
  by the selected reduced unified profile, including whether non-`CSRRW` Zicsr
  encodings currently accepted by preprocessing are admitted carriers. PRECOMP
  separately owns fulfillment arithmetic and ABI relations.

## Metadata

Ordinary instruction semantics adopt the official
[RV32I specification](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html).
Carrier syntax follows the official
[Zimop](https://docs.riscv.org/reference/isa/unpriv/zimop.html) and
[Zicsr](https://docs.riscv.org/reference/isa/unpriv/zicsr.html) specifications;
delegation and nondeterminism addresses occupy the official
[custom machine CSR range](https://docs.riscv.org/reference/isa/priv/priv-csrs.html).
The [RVALP v0.18.4 RV32I reference cards](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf)
corroborate the ordinary destination assignments and sequential PC assignment.
Canonical NOP routing and non-wrapping PC enforcement are Airbender-specific
boundaries already adopted for the ISA-family specifications. Starred custom
relations remain implementation-derived.

- spec revision: TBD
- implementation: TBD
- profile: reduced unified machine, circuit family `128`, family-1 subrelation

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `ASM-UADD-001` | normative | active family-1 row | `external:DEC` | located | unified preprocessing and decoder at `dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/decoder.rs#UnifiedReducedMachineDecoder::define_decoder_subspace`; `symbol:cs/src/gkr_circuits/add_sub_family/decoder.rs#AddSubLuiAuipcMopDecoder::define_decoder_subspace` |
| `ASM-UADD-002` | normative | active family-1 row | `external:REG` | located | unified shared accesses and global memory-like argument at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/unified_reduced_machine/circuit.rs#apply_unified_reduced_machine_inner`; `symbol:cs/src/gkr_compiler/memory_like_grand_product.rs#layout_initial_grand_product_accumulation` |
| `ASM-UADD-003` | normative | a selected register is `x0` | `external:REG` | prose | RISC-V `x0` semantics; global register-memory argument | — |
| `ASM-UADD-004` | normative | active row | `external:DEC` | located | aligned decoder-table keys at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask`; `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit` |
| `REL-UADD-001` | normative | active ordinary or NOP row | `ASM-UADD-001..003` | located | [RV32I](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html); [RVALP v0.18.4](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf); unified family-1 constraints at `dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/add_sub_lui_auipc_mop.rs#apply_unified_add_sub_lui_auipc_mop_inner` |
| `REL-UADD-002` | provisional | active custom-arithmetic row | `ASM-UADD-001..003`; `GAP-UADD-001` | located | [Zimop carrier syntax](https://docs.riscv.org/reference/isa/unpriv/zimop.html); unified decoder, constraints, and MOP replayer at `dfb1b2a8a` | `symbol:common_constants/src/mops.rs#MOP_ADD_MOD`; `symbol:common_constants/src/mops.rs#MOP_SUB_MOD`; `symbol:common_constants/src/mops.rs#MOP_MUL_MOD`; `symbol:common_constants/src/mops.rs#MOP_FMA_MOD`; `symbol:common_constants/src/mops.rs#MOP_TRI_ADD`; `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/decoder.rs#UnifiedReducedMachineDecoder::define_decoder_subspace`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/add_sub_lui_auipc_mop.rs#apply_unified_add_sub_lui_auipc_mop_inner`; `symbol:riscv_transpiler/src/replayer/instructions/add_sub_family/mop.rs#mop_addmod` |
| `REL-UADD-003` | provisional | active nondeterminism row | `ASM-UADD-001..003`; `GAP-UADD-002` | located | [Zicsr carrier syntax](https://docs.riscv.org/reference/isa/unpriv/zicsr.html); preprocessing, family-1 constraints, and nondeterminism replayer at `dfb1b2a8a` | `symbol:common_constants/src/lib.rs#NON_DETERMINISM_CSR`; `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/add_sub_lui_auipc_mop.rs#apply_unified_add_sub_lui_auipc_mop_inner`; `symbol:riscv_transpiler/src/replayer/instructions/add_sub_family/non_determinism.rs#nd_read` |
| `REL-UADD-004` | normative | every active family-1 row | `ASM-UADD-001`, `ASM-UADD-004`; 32-bit `pc` domain | located | [RVALP v0.18.4](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf); unified PC-bump constraints at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/unified_reduced_machine/circuit.rs#apply_unified_pc_bump` |
| `OUT-UADD-001` | provisional | active delegation row | `ASM-UADD-001..003`; `GAP-UADD-003`; discharged by `external:PRECOMP` | located | [Zicsr carrier syntax](https://docs.riscv.org/reference/isa/unpriv/zicsr.html); [custom machine CSR range](https://docs.riscv.org/reference/isa/priv/priv-csrs.html); delegation preprocessing, family-1 constraints, and global memory-like argument at `dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#DelegationType`; `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:cs/src/gkr_circuits/add_sub_family/decoder.rs#AddSubLuiAuipcMopDecoder::define_decoder_subspace`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/add_sub_lui_auipc_mop.rs#apply_unified_add_sub_lui_auipc_mop_inner`; `symbol:cs/src/gkr_compiler/memory_like_grand_product.rs#layout_initial_grand_product_accumulation` |
| `GAP-UADD-001` | open | — | affects `REL-UADD-002`; owner: human | — | custom arithmetic has convergent circuit and replayer evidence but no adopted independent relation | — |
| `GAP-UADD-002` | open | — | affects `REL-UADD-003`; owner: human | — | nondeterminism behavior is implementation-defined and its external binding is unspecified | — |
| `GAP-UADD-003` | open | — | affects `OUT-UADD-001`; owner: human | — | executor and fulfillment encodings are located, but profile admission and ABI adoption remain open | — |
