# MWORD: Word memory family

## Supported operations

- `LW rd, imm12(rs1)`
- `SW rs2, imm12(rs1)`

The standalone family admits `LW` only when `rd ≠ x0`. The preprocessor canonicalizes
`LW x0` to `NOP`, so the original effective address emits no memory-argument access.
The emulated machine has no MMIO or external memory-side-effect channel. `LR`, `SC`,
AMOs, and subword loads or stores are outside this module.

## Inputs

- `u12 = [0, 2¹²)`, `u28 = [0, 2²⁸)`, and `u32 = [0, 2³²)` are unsigned
  integer domains
- `pc, rs1, rs2 ∈ u32`
- `execute ∈ {0, 1}` activates the cycle
- `imm12 ∈ u12` is the encoded load or store immediate
- `rd ≠ x0` is the `LW` destination register
- `op ∈ {LW, SW}`
- `sign_extend_12(x)` sign-extends `x ∈ u12` to `u32`
- `ROM[a] ∈ u32` is the fixed program-image word at byte address `a`
- `RAM[a] ∈ u32` is the mutable word at byte address `a`
- `x ← expression` assigns the expression to `x`; the right-hand side uses pre-cycle
  values and unassigned architectural locations remain unchanged

## Assumptions

- **ASM-MWORD-001 — Decoder authentication.** For an active row, the decoder authenticates exactly one supported `op`, its selected source registers, `rd`, and its encoded immediate field against the instruction at the current `pc`
- **ASM-MWORD-002 — Register and RAM consistency.** Register accesses satisfy the global register-memory argument; every RAM-argument access satisfies `addr mod 4 = 0` and `addr < 2³⁰`
- **ASM-MWORD-003 — ROM authenticity.** For `a < 2²²`, `ROM[a]` is the authenticated raw program-image word at `a`, or the profile's zero padding after the supplied image; the ROM table admits exactly the multiples of four
- **ASM-MWORD-004 — Zero register.** Reading `x0` returns `0`
- **ASM-MWORD-005 — PC alignment.** The active decoder lookup binds `pc` to a table key of the form `4 · i`; therefore `pc mod 4 = 0` at the start of the cycle

## Canonical relation tree

> Interpret this tree under `ASM-MWORD-001..005`. Within `execute = 1`, the numbered
> relations are conjoined. The operation and memory-region cases below
> `REL-MWORD-002` are mutually exclusive.

- **`execute = 0`** Outside this module's active-row scope
- **`execute = 1`**
  - **[`REL-MWORD-001`] Effective address**
    `addr = (rs1 + sign_extend_12(imm12)) mod 2³²`
  - **[`REL-MWORD-002`] Memory assignment**
    - **`op = LW`**
      - **`addr < 2²²`**
        `addr mod 4 = 0`
        `rd ← ROM[addr]`
      - **`addr ≥ 2²²`**
        `addr mod 4 = 0`
        `addr < 2³⁰`
        `rd ← RAM[addr]`
    - **`op = SW`**
      `addr ≥ 2²²`
      `addr mod 4 = 0`
      `addr < 2³⁰`
      `RAM[addr] ← rs2`
  - **[`REL-MWORD-003`] Non-wrapping PC assignment**
    `pc + 4 < 2³²`
    `pc ← pc + 4`

## Derived facts

- **32-bit effective address**
  `addr ∈ u32`
- **Word alignment**
  `addr mod 4 = 0`
- **ROM immutability**
  `ROM` unchanged
- **Register and memory effects**
  `op = LW ⇒ only rd may change`
  `op = SW ⇒ only RAM[addr] may change`
- **PC range**
  `pc ≤ 2³² − 8` before assignment
  `pc ≤ 2³² − 4` after assignment
- **PC alignment**
  `pc mod 4 = 0`

## Metadata

These relations are normative for the stated unrolled profile. The effective-address,
load, and store semantics adopt the official
[RV32I specification](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html).
The [RVALP v0.18.4 RV32I reference cards](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf)
corroborate `LW`, `SW`, and `pc ← pc + 4`. Airbender additionally restricts word
accesses through its ROM boundary and aligned memory argument, discards `LW x0`, and
forbids PC overflow. These profile rules are supported by explicit project decisions
and convergent decoder, constraint, table, and memory-argument evidence checked at
`matter-labs/zksync-airbender@dfb1b2a8a`.

- spec revision: `2026-09-02.1`
- profile: unrolled `mem_word_only`, word load/store subrelation

### Statement metadata

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `ASM-MWORD-001` | normative | active row | `external:DEC` | located | program preprocessing and normalized family decoder at `dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:cs/src/gkr_circuits/mem_word_only/decoder.rs#define_decoder_subspace` |
| `ASM-MWORD-002` | normative | active row | `external:REG`; `external:MEM` | located | global register-memory and unrolled RAM arguments | `symbol:cs/src/gkr_circuits/mem_word_only/circuit.rs#apply_mem_word_only_inner`; `symbol:prover/src/gkr/virtual_polys/init_and_teardown_base.rs#materialize_virtual_inits_and_teardowns_base_address_setup_poly`; `symbol:full_statement_verifier/src/unrolled_proof_statement.rs#verify_base_or_recursion_unrolled_circuits` |
| `ASM-MWORD-003` | normative | ROM load | `external:MEM/ROM` | located | `repo:common_constants/src/rom.rs#ROM_BYTE_SIZE_LOG2@dfb1b2a8a`; `repo:cs/src/tables/rom_related.rs#ROM_PADDING_OPCODE@dfb1b2a8a`; aligned program-image table | `symbol:common_constants/src/rom.rs#ROM_BYTE_SIZE_LOG2`; `symbol:cs/src/tables/rom_related.rs#ROM_PADDING_OPCODE`; `symbol:cs/src/tables/rom_related.rs#create_table_for_word_aligned_rom_image` |
| `ASM-MWORD-004` | normative | a selected source register is `x0` | `external:REG` | prose | RISC-V `x0` semantics; global register-memory argument | — |
| `ASM-MWORD-005` | normative | active row | `external:DEC` | located | aligned decoder-table keys in `repo:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask@dfb1b2a8a`; decoder lookup construction in `repo:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask`; `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit` |
| `REL-MWORD-001` | normative | active row | `ASM-MWORD-001`, `ASM-MWORD-002` | located | [RV32I effective-address semantics](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html); [RVALP v0.18.4 RV32I reference cards](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf); `repo:cs/src/gkr_circuits/mem_word_only/circuit.rs#apply_mem_word_only_inner@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/mem_word_only/circuit.rs#apply_mem_word_only_inner` |
| `REL-MWORD-002` | normative | active operation row | `ASM-MWORD-001..004`, `REL-MWORD-001` | located | [RV32I word load/store semantics](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html); [RVALP v0.18.4 RV32I reference cards](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf); `decision:2026-09-01#emulated-memory-has-no-device-side-effects`; word-family and aligned ROM relations at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/mem_word_only/circuit.rs#apply_mem_word_only_inner`; `symbol:cs/src/tables/rom_related.rs#create_table_for_word_aligned_rom_image`; `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode` |
| `REL-MWORD-003` | normative | active row | 32-bit `pc` input domain | located | [RVALP v0.18.4 sequential PC assignment](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf); non-overflow enforcement at `repo:cs/src/gkr_circuits/utils.rs#calculate_pc_next_no_overflows_with_range_checks@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/utils.rs#calculate_pc_next_no_overflows_with_range_checks` |
