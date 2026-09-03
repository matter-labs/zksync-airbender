# MEMSUB: Subword memory family

## Supported operations

- `LB rd, imm12(rs1)`
- `LBU rd, imm12(rs1)`
- `LH rd, imm12(rs1)`
- `LHU rd, imm12(rs1)`
- `SB rs2, imm12(rs1)`
- `SH rs2, imm12(rs1)`

The standalone family admits loads only when `rd ≠ x0`. The preprocessor canonicalizes
a listed load with `rd = x0` to `NOP`, so no access at its original effective address
enters the memory argument. The emulated machine has no MMIO or external
memory-side-effect channel. Stores retain their memory effect.

## Inputs

- `u8 = [0, 2⁸)`, `u12 = [0, 2¹²)`, `u16 = [0, 2¹⁶)`, and `u32 = [0, 2³²)` are
  unsigned integer domains
- `pc, rs1, rs2 ∈ u32` are the current program counter and source-register values
- `execute ∈ {0, 1}` activates the cycle
- `imm12 ∈ u12` is the encoded I-immediate for a load or S-immediate for a store
- `op` is one of the supported operations
- `op ∈ {LB, LBU, LH, LHU} ⇒ rd ≠ x0`
- `ROM_LIMIT = 2²²`
- `ROM[word_addr] ∈ u32` is the fixed program-image word at four-byte-aligned byte
  address `word_addr`
- `RAM[word_addr] ∈ u32` is the mutable word at four-byte-aligned byte address
  `word_addr`
- `sign_extend_n(x)` sign-extends an `n`-bit input to `u32`
- `x[j:i]` is the inclusive bit slice from bit `j` through bit `i`
- `x ← expression` assigns the expression to `x`; the right-hand side uses pre-cycle
  values and unassigned architectural locations remain unchanged

## Assumptions

- **ASM-MEMSUB-001 — Decoder authentication.** For an active row, the decoder authenticates exactly one supported `op`, its selected registers, and its encoded I- or S-immediate against the instruction at the current `pc`.
- **ASM-MEMSUB-002 — Register and memory consistency.** Register reads, load writes, and mutable-memory reads or writes satisfy the global memory argument, including `x0` semantics and the admitted mutable-address domain.
- **ASM-MEMSUB-003 — ROM binding.** For `word_addr < ROM_LIMIT`, `ROM[word_addr]` is the raw program-image word at index `word_addr / 4`, or `ROM_PADDING_OPCODE = 0` beyond the supplied image. The subword ROM tables authenticate extraction from this word.
- **ASM-MEMSUB-004 — PC alignment.** The active decoder lookup binds `pc` to a table key of the form `4 · i`; therefore `pc mod 4 = 0` at the start of the cycle.

## Canonical relation tree

> Interpret this tree under `ASM-MEMSUB-001..004`. Within `execute = 1`, the
> numbered relations are conjoined. The cases below `REL-MEMSUB-001` are
> mutually exclusive.

- **`execute = 0`** Outside this module's active-row scope
- **`execute = 1`**
  - **[`REL-MEMSUB-001`] Effective address and subword assignment**
    `effective_addr = (rs1 + sign_extend_12(imm12)) mod 2³²`
    `word_addr = effective_addr - (effective_addr mod 4)`
    `byte_offset = effective_addr mod 4`
    - **`op ∈ {LB, LBU, LH, LHU}`**
      - **`word_addr < ROM_LIMIT`**
        `source_word = ROM[word_addr]`
      - **`word_addr ≥ ROM_LIMIT`**
        `source_word = RAM[word_addr]`
      - **`op = LB`**
        `rd ← sign_extend_8(source_word[8 · byte_offset + 7 : 8 · byte_offset])`
      - **`op = LBU`**
        `rd ← source_word[8 · byte_offset + 7 : 8 · byte_offset]`
      - **`op = LH`**
        `byte_offset mod 2 = 0`
        `rd ← sign_extend_16(source_word[8 · byte_offset + 15 : 8 · byte_offset])`
      - **`op = LHU`**
        `byte_offset mod 2 = 0`
        `rd ← source_word[8 · byte_offset + 15 : 8 · byte_offset]`
    - **`op = SB`**
      `word_addr ≥ ROM_LIMIT`
      `RAM[word_addr][8 · byte_offset + 7 : 8 · byte_offset] ← rs2[7:0]`
    - **`op = SH`**
      `byte_offset mod 2 = 0`
      `word_addr ≥ ROM_LIMIT`
      `RAM[word_addr][8 · byte_offset + 15 : 8 · byte_offset] ← rs2[15:0]`
  - **[`REL-MEMSUB-002`] Non-wrapping PC assignment**
    `pc + 4 < 2³²`
    `pc ← pc + 4`

## Derived facts

- **32-bit assignments**
  `effective_addr, word_addr, pc ∈ u32`
  `op ∈ {LB, LBU, LH, LHU} ⇒ source_word ∈ u32`
  `op ∈ {LB, LBU, LH, LHU} ⇒ rd ∈ u32`
- **Byte offsets**
  `op ∈ {LB, LBU, SB} ⇒ byte_offset ∈ {0, 1, 2, 3}`
- **Halfword offsets**
  `op ∈ {LH, LHU, SH} ⇒ byte_offset ∈ {0, 2}`
- **Load extension**
  `op = LB ⇒ rd[31:8] ∈ {0, 2²⁴ − 1}`
  `op = LH ⇒ rd[31:16] ∈ {0, 2¹⁶ − 1}`
  `op = LBU ⇒ rd[31:8] = 0`
  `op = LHU ⇒ rd[31:16] = 0`
- **ROM immutability**
  `ROM` unchanged
- **Register and memory effects**
  `op ∈ {LB, LBU, LH, LHU} ⇒` only `rd` may change
  `op ∈ {SB, SH} ⇒` only `RAM[word_addr]` may change
- **PC range**
  `pc ≤ 2³² − 8` before assignment
  `pc ≤ 2³² − 4` after assignment
- **PC alignment**
  `pc mod 4 = 0`

## Metadata

These relations are normative for the stated unrolled profile. Load/store semantics
adopt the official [RV32I specification](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html),
and the [RVALP v0.18.4 RV32I reference cards](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf)
corroborate each subword assignment and `pc ← pc + 4`. Airbender's ROM boundary,
halfword-alignment restriction, non-wrapping PC, and discarded-load behavior are
supported by explicit project decisions and convergent decoder, constraint, table,
and memory-argument evidence checked at
`matter-labs/zksync-airbender@dfb1b2a8a`.

- spec revision: TBD
- implementation: TBD
- profile: unrolled `mem_subword_only`, full-machine subword-memory subrelation

### Statement metadata

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `ASM-MEMSUB-001` | normative | active row | `external:DEC` | located | `repo:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode@dfb1b2a8a`; `repo:cs/src/gkr_circuits/mem_subword_only/decoder.rs#define_decoder_subspace@dfb1b2a8a`; authenticated decoder lookup | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:cs/src/gkr_circuits/mem_subword_only/decoder.rs#define_decoder_subspace`; `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit` |
| `ASM-MEMSUB-002` | normative | active row | `external:REG`; `external:MEM` | located | `repo:cs/src/gkr_circuits/mem_subword_only/circuit.rs#apply_mem_subword_only_inner@dfb1b2a8a`; global memory argument | `symbol:cs/src/gkr_circuits/mem_subword_only/circuit.rs#apply_mem_subword_only_inner`; `symbol:cs/src/cs/circuit_impl.rs#request_mem_access` |
| `ASM-MEMSUB-003` | normative | `word_addr < ROM_LIMIT` | `external:MEM` | located | raw bytecode is passed by `repo:circuit_defs/unrolled_circuits/load_store_subword_only/src/lib.rs#LoadStoreSubwordOnlyCircuit@dfb1b2a8a`; `repo:common_constants/src/rom.rs#ROM_BYTE_SIZE_LOG2@dfb1b2a8a`; `repo:cs/src/tables/rom_related.rs#ROM_PADDING_OPCODE@dfb1b2a8a`; ROM extraction tables | `symbol:circuit_defs/unrolled_circuits/load_store_subword_only/src/lib.rs#LoadStoreSubwordOnlyCircuit`; `symbol:common_constants/src/rom.rs#ROM_BYTE_SIZE_LOG2`; `symbol:cs/src/tables/rom_related.rs#ROM_PADDING_OPCODE`; `symbol:cs/src/tables/rom_related.rs#create_load_byte_from_rom_table`; `symbol:cs/src/tables/rom_related.rs#create_load_halfword_from_rom_table` |
| `ASM-MEMSUB-004` | normative | active row | `external:DEC` | located | aligned authenticated decoder keys in `repo:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask@dfb1b2a8a`; decoder lookup construction | `symbol:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask`; `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit` |
| `REL-MEMSUB-001` | normative | active operation row | `ASM-MEMSUB-001..003` | located | [RV32I load/store semantics](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html); [RVALP v0.18.4 RV32I reference cards](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf); `decision:emulated-memory-has-no-device-side-effects`; `repo:cs/src/gkr_circuits/mem_subword_only/circuit.rs#apply_mem_subword_only_inner@dfb1b2a8a`; subword lookup tables | `symbol:cs/src/gkr_circuits/mem_subword_only/circuit.rs#apply_mem_subword_only_inner`; `symbol:cs/src/tables/memory_opcode_related.rs#create_load_byte_signextend_table`; `symbol:cs/src/tables/memory_opcode_related.rs#create_load_halfword_signextend_table`; `symbol:cs/src/tables/memory_opcode_related.rs#create_store_byte_source_contribution_table`; `symbol:cs/src/tables/memory_opcode_related.rs#create_store_byte_existing_contribution_table` |
| `REL-MEMSUB-002` | normative | active row | `ASM-MEMSUB-004`; 32-bit `pc` input domain | located | [RVALP v0.18.4 sequential PC assignment](https://github.com/johnwinans/rvalp/releases/download/v0.18.4/rvalp.pdf); non-overflow enforcement at `repo:cs/src/gkr_circuits/utils.rs#calculate_pc_next_no_overflows_with_range_checks@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/utils.rs#calculate_pc_next_no_overflows_with_range_checks` |
