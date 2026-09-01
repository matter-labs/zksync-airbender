# MWORD: Word memory family

## Supported operations

- `LW rd, imm12(rs1)`
- `SW rs2, imm12(rs1)`

Under the pinned Airbender profile, `LW` with `rd = x0` is rewritten to the canonical
`NOP` during preprocessing and does not enter this family, so no access at its
original effective address enters the memory argument. The inspected emulated machine
has no MMIO or external memory-side-effect channel. `LR`, `SC`, AMOs, and subword
loads or stores are outside this module.

## Inputs

| Name | Meaning |
|---|---|
| `pc` | current 32-bit program counter |
| `execute` | boolean cycle-activation flag |
| `rs1`, `rs2` | 32-bit values read from the selected source registers |
| `imm12` | encoded 12-bit load/store immediate |
| `rd` | selected `LW` destination register |
| `op` | either `LW` or `SW` |
| `addr` | 32-bit effective byte address |
| `ROM[a]` | authenticated raw 32-bit program-image word at byte address `a` in the fixed ROM region |
| `RAM[a]` | mutable 32-bit word at byte address `a` |

The fixed ROM region is `[0, 2^22)`. Machine words and addresses are 32-bit values.

`x <- expression` denotes the cycle's architectural assignment to `x`. The right-hand
side uses pre-cycle values. An assignment must remain in the target's declared domain
unless the expression explicitly says `mod`. Architectural locations not assigned by
the active relation remain unchanged.

## Assumptions

- **ASM-MWORD-001 — Decoder binding.** `(op, rs1_index, rs2_index, rd, imm12)` is the row committed for the current `pc`; an `LW` row has `rd != x0`.
- **ASM-MWORD-002 — Selector exclusivity.** Exactly one of `LW` and `SW` is selected.
- **ASM-MWORD-003 — Register and RAM consistency.** Register and mutable-RAM reads and writes satisfy the global memory argument.
- **ASM-MWORD-004 — Aligned ROM program-image authenticity.** `ROM[a]` is the raw program-image word at `a`, or the profile's ROM-padding word after the supplied image. The authenticated table admits exactly the multiples of four in `[0, 2^22)`.
- **ASM-MWORD-005 — Zero register.** Reading `x0` returns `0`; writing `x0` preserves `0`.
- **ASM-MWORD-006 — PC alignment.** `pc mod 4 = 0` at the start of the cycle.

## Canonical relation tree

> Interpret this tree under `ASM-MWORD-001..006`. Within `execute = 1`, the numbered
> requirements are conjoined. The cases below `REQ-MWORD-002` are mutually exclusive.

- **`execute = 0`.** Outside this module's active-row scope.
- **`execute = 1`.**
  - **[`REQ-MWORD-001`] Effective address.**
    `addr = (rs1 + sign_extend_12(imm12)) mod 2^32`.
  - **[`REQ-MWORD-002`] Operation and memory-region assignment.**
    - **`op = LW && addr < 2^22`.**
      `addr mod 4 = 0`;
      `rd <- ROM[addr]`.
    - **`op = LW && addr >= 2^22`.**
      `rd <- RAM[addr]`.
    - **`op = SW`.**
      `addr >= 2^22`;
      `RAM[addr] <- rs2`.
  - **[`REQ-MWORD-003`] Non-wrapping PC assignment.**
    `pc + 4 < 2^32`;
    `pc <- pc + 4`.

## Derived facts

For a quick structural view of every active row:

- effective-address overflow wraps by `REQ-MWORD-001`;
- ROM loads are locally word-aligned by `ASM-MWORD-004` and `REQ-MWORD-002`;
- mutable-RAM loads and stores have no local low-bit constraint in this family, but
  `ASM-MWORD-003` closes them against the global RAM universe, whose admitted word
  addresses are divisible by four;
- stores cannot change ROM by `REQ-MWORD-002`;
- `ASM-MWORD-006` and `REQ-MWORD-003` imply `pc <= 2^32 - 8` before the
  assignment and `pc <= 2^32 - 4` afterward, with four-byte alignment preserved;
- among registers and memory, an `LW` changes at most `rd` and an `SW` changes at
  most `RAM[addr]`; both operations separately assign `pc` by `REQ-MWORD-003`.

## Metadata

These relations are normative for the stated unrolled profile. Load/store semantics
adopt the official [RV32I specification](https://docs.riscv.org/reference/isa/v20260120/unpriv/rv32.html),
with Airbender's ROM boundary, global alignment, and discarded-load behavior supported
by explicit project decisions and convergent decoder, constraint, table, and
memory-argument evidence checked at
`matter-labs/zksync-airbender@dfb1b2a8a`.

- spec revision: `2026-08-28.5`
- profile: unrolled `mem_word_only`, word load/store subrelation

### Statement metadata

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `ASM-MWORD-001` | normative | active row | `external:DEC` | located | `repo:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode@dfb1b2a8a`; `repo:cs/src/gkr_circuits/mem_word_only/decoder.rs#define_decoder_subspace@dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:cs/src/gkr_circuits/mem_word_only/decoder.rs#define_decoder_subspace` |
| `ASM-MWORD-002` | normative | active row | `external:DEC` | located | admitted selector rows in `repo:cs/src/gkr_circuits/mem_word_only/decoder.rs#define_decoder_subspace@dfb1b2a8a`; authenticated decoder lookup in `repo:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/mem_word_only/decoder.rs#define_decoder_subspace`; `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit` |
| `ASM-MWORD-003` | normative | active row | `external:REG`; `external:MEM` | located | word-family access relation, word-address initialization/teardown universe, and full-statement product closure | `symbol:cs/src/gkr_circuits/mem_word_only/circuit.rs#apply_mem_word_only_inner`; `symbol:prover/src/gkr/virtual_polys/init_and_teardown_base.rs#materialize_virtual_inits_and_teardowns_base_address_setup_poly`; `symbol:full_statement_verifier/src/unrolled_proof_statement.rs#verify_base_or_recursion_unrolled_circuits` |
| `ASM-MWORD-004` | normative | ROM load | `external:MEM/ROM` | located | `repo:common_constants/src/rom.rs#ROM_BYTE_SIZE_LOG2@dfb1b2a8a`; `repo:cs/src/tables/rom_related.rs#create_table_for_word_aligned_rom_image@dfb1b2a8a`; raw program image and profile ROM-padding word | `symbol:common_constants/src/rom.rs#ROM_BYTE_SIZE_LOG2`; `symbol:cs/src/tables/rom_related.rs#create_table_for_word_aligned_rom_image` |
| `ASM-MWORD-005` | normative | source index `0` | `external:REG` | prose | RISC-V `x0` semantics; global register-memory argument | — |
| `ASM-MWORD-006` | normative | active row | `external:MACH` | located | `repo:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask@dfb1b2a8a`; `repo:cs/src/cs/circuit_impl.rs#allocate_machine_state@dfb1b2a8a`; global PC-state argument | `symbol:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask`; `symbol:cs/src/cs/circuit_impl.rs#allocate_machine_state` |
| `REQ-MWORD-001` | normative | active row | `ASM-MWORD-001..003` | located | `repo:cs/src/gkr_circuits/mem_word_only/circuit.rs#apply_mem_word_only_inner@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/mem_word_only/circuit.rs#apply_mem_word_only_inner` |
| `REQ-MWORD-002` | normative | active operation row | `ASM-MWORD-001..005` | located | `repo:cs/src/gkr_circuits/mem_word_only/circuit.rs#apply_mem_word_only_inner@dfb1b2a8a`; `repo:cs/src/tables/rom_related.rs#create_table_for_word_aligned_rom_image@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/mem_word_only/circuit.rs#apply_mem_word_only_inner`; `symbol:cs/src/tables/rom_related.rs#create_table_for_word_aligned_rom_image` |
| `REQ-MWORD-003` | normative | active row | 32-bit PC word domain | located | `repo:cs/src/gkr_circuits/utils.rs#calculate_pc_next_no_overflows_with_range_checks@dfb1b2a8a` | `symbol:cs/src/gkr_circuits/utils.rs#calculate_pc_next_no_overflows_with_range_checks` |
