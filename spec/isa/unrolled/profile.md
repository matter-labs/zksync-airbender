# UPROF: Unrolled ISA implementation profile

> Inventory of the full-unsigned unrolled executor at `dfb1b2a8a`; this module
> selects family relations and delegated precompiles but does not restate their
> equations, global state arguments, or proof topology.

## Guarantee

The unrolled executor commits and proves one trace per selected instruction family.
Program preprocessing assigns each admitted instruction address to one of those
families. Delegated precompiles use separate circuits and are not ISA-family traces.

## Profile inputs

- `machine_config = IMStandardIsaConfigUnsignedMulDivOnly`.
- `decoder_config = FullUnsignedMachineDecoderConfig`.
- `binary_image` supplies fixed ROM contents; `text_section` supplies instructions
  admitted to the per-family decoder tables.

## Profile facts

### REQ-UPROF-001 — Executor-family inventory

The per-program setup map contains one separately committed entry for each family
below. The linked module owns the listed ordinary ISA relation; this profile only
selects it.

| Unrolled family | Admitted source operations or feature | Relation module |
|---|---|---|
| `AddSubLuiAuipcMopCircuit` | `ADD`, `ADDI`, `LUI`, `SUB`, `AUIPC`; canonical `NOP`; project MOP add/subtract/multiply/FMA; delegation and nondeterminism CSR paths | [ADD](add-sub.md) for the ordinary integer operations |
| `JumpBranchSltCircuit` | `JAL`, `JALR`, `BEQ`, `BNE`, `BLT`, `BGE`, `BLTU`, `BGEU`, `SLT`, `SLTI`, `SLTU`, `SLTIU` | [JUMP](jump-branch-slt.md) |
| `ShiftBinaryCircuit` | `AND`, `ANDI`, `OR`, `ORI`, `XOR`, `XORI`, `SLL`, `SLLI`, `SRL`, `SRLI`, `SRA`, `SRAI` | [BSHIFT](binary-shifts.md) |
| `LoadStoreWordOnlyCircuit` | `LW`, `SW` | [MWORD](memory-word.md) |
| `LoadStoreSubwordOnlyCircuit` | `LB`, `LBU`, `LH`, `LHU`, `SB`, `SH` | [MEMSUB](memory-subword.md) |
| `UnsignedMulDivCircuit` | `MUL`, `MULHU`, `DIVU`, `REMU` | [MULDIV](mul-div.md) |

`ROL`, `ROR`, and the project tri-add/XOR-rotate variants are not admitted by these
installed family decoders. A preprocessing feature flag or generic IR variant does
not by itself add an operation to this profile.

### REQ-UPROF-002 — Unsigned multiplication and division scope

This profile instantiates `DivMulDecoder<false>` and `UnsignedMulDivCircuit`. Its
M-extension surface is exactly `MUL`, `MULHU`, `DIVU`, and `REMU`.

Generic signed branches for `MULH`, `MULHSU`, `DIV`, and `REM` are not selected by
this profile. Their unfinished implementation is therefore outside this profile and
does not weaken the four admitted unsigned operations.

### REQ-UPROF-003 — Subword-memory presence

The full-unsigned unrolled setup includes `LoadStoreSubwordOnlyCircuit`; byte and
halfword loads and stores are part of this profile. Their absence from a reduced
unified profile does not alter this inventory.

### REQ-UPROF-004 — Canonical NOP routing

An operation constructed through `Instruction::pure_from_imm` with `rd = x0` is
replaced during preprocessing by the single row
`Instruction::nop() = (Nop, x0, x0, x0, 0)`. The add-family decoder admits that row
as its all-zero add case. This includes loads to `x0`: they emit no access at the
original memory address, and the inspected machine has no external/MMIO side-effect
channel. Instructions whose architectural effect is not a pure destination write,
including branches, jumps, stores, and delegation calls, do not follow this rule
merely because an encoded `rd` field is zero.

### REQ-UPROF-005 — Word-memory alignment boundary

The unrolled word-memory family locally authenticates a ROM `LW` only at an address
divisible by four. Its mutable-RAM `LW` and `SW` branches impose no local
`addr mod 4 = 0` predicate, but the global memory argument closes those accesses
against an initialization/teardown universe containing only word-aligned addresses.
Thus accepted unrolled word accesses are aligned even though the restriction is owned
by shared memory consistency rather than the family circuit.

### REQ-UPROF-006 — Delegated-precompile set

The machine config admits exactly these delegation CSR types, with a separate setup
circuit for each:

- Blake2s with compression/control;
- big-integer operations with control;
- Keccak `special5`;
- Blake2s G-function.

The add-family trace records the delegation call. The delegated circuit owns the
precompile computation; that relation is outside this ISA-profile inventory.

## Open boundary

- **GAP-UPROF-001 — Profile-specific add-family relations.** The ordinary [ADD](add-sub.md)
  module does not yet specify the project MOP, nondeterminism, or delegation-call
  branches that share `AddSubLuiAuipcMopCircuit`. Those relations require dedicated
  modules; their absence does not make the ordinary ADD equations apply to them.

## Metadata

The profile inventory is normative for the selected full-unsigned unrolled machine.
It combines explicit project direction with the independently reviewed family
relations and matching decoder, setup, and global-argument evidence.

- spec revision: `2026-09-01.1`
- implementation: `matter-labs/zksync-airbender@dfb1b2a8a+dirty`
- profile: unrolled full-unsigned base machine

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `REQ-UPROF-001` | normative | profile setup | `REQ-ADD-001..002`; `REQ-JUMP-001..003`; `REQ-BSHIFT-001..002`; `REQ-MWORD-001..003`; `REQ-MEMSUB-001..002`; `REQ-MULDIV-001..002` | located | `repo:circuit_defs/setups/src/unrolled_circuits/mod.rs#get_unrolled_circuits_setups_for_machine_type@dfb1b2a8a`; `repo:cs/src/gkr_circuits/decoder_trait.rs#opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization@dfb1b2a8a`; installed family decoders | `symbol:circuit_defs/setups/src/unrolled_circuits/mod.rs#get_unrolled_circuits_setups_for_machine_type`; `symbol:cs/src/gkr_circuits/decoder_trait.rs#opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization`; `symbol:cs/src/gkr_circuits/add_sub_family/decoder.rs#AddSubLuiAuipcMopDecoder::define_decoder_subspace`; `symbol:cs/src/gkr_circuits/jump_branch_slt_family/decoder.rs#JumpSltBranchDecoder::define_decoder_subspace`; `symbol:cs/src/gkr_circuits/binary_shifts_family/decoder.rs#ShiftBinaryDecoder::define_decoder_subspace`; `symbol:cs/src/gkr_circuits/mem_word_only/decoder.rs#WordOnlyMemoryFamilyDecoder::define_decoder_subspace`; `symbol:cs/src/gkr_circuits/mem_subword_only/decoder.rs#SubwordOnlyMemoryFamilyDecoder::define_decoder_subspace`; `symbol:cs/src/gkr_circuits/mul_div/decoder.rs#DivMulDecoder::define_decoder_subspace` |
| `REQ-UPROF-002` | normative | `machine_config = IMStandardIsaConfigUnsignedMulDivOnly` | `REQ-UPROF-001`; `REQ-MULDIV-001..002` | located | `repo:riscv_transpiler/src/cycle/mod.rs#IMStandardIsaConfigUnsignedMulDivOnly@dfb1b2a8a`; `repo:circuit_defs/setups/src/unrolled_circuits/mod.rs#decoders_for_machine_type@dfb1b2a8a`; `repo:circuit_defs/setups/src/unrolled_circuits/mod.rs#get_unrolled_circuits_setups_for_machine_type@dfb1b2a8a` | `symbol:riscv_transpiler/src/cycle/mod.rs#IMStandardIsaConfigUnsignedMulDivOnly`; `symbol:circuit_defs/setups/src/unrolled_circuits/mod.rs#decoders_for_machine_type`; `symbol:circuit_defs/setups/src/unrolled_circuits/mod.rs#get_unrolled_circuits_setups_for_machine_type` |
| `REQ-UPROF-003` | normative | profile setup | `REQ-UPROF-001`; `REQ-MEMSUB-001..002` | located | `repo:riscv_transpiler/src/ir/mod.rs#FullUnsignedMachineDecoderConfig@dfb1b2a8a`; `repo:circuit_defs/setups/src/unrolled_circuits/mod.rs#get_unrolled_circuits_setups_for_machine_type@dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/mod.rs#FullUnsignedMachineDecoderConfig`; `symbol:circuit_defs/setups/src/unrolled_circuits/mod.rs#get_unrolled_circuits_setups_for_machine_type` |
| `REQ-UPROF-004` | normative | preprocessed pure destination write with `rd = x0` | `REQ-UPROF-001` | located | `repo:riscv_transpiler/src/ir/simple_instruction_set.rs#Instruction::pure_from_imm@dfb1b2a8a`; `repo:riscv_transpiler/src/ir/simple_instruction_set.rs#Instruction::nop@dfb1b2a8a`; `repo:cs/src/gkr_circuits/add_sub_family/decoder.rs#AddSubLuiAuipcMopDecoder::define_decoder_subspace@dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#Instruction::pure_from_imm`; `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#Instruction::nop`; `symbol:cs/src/gkr_circuits/add_sub_family/decoder.rs#AddSubLuiAuipcMopDecoder::define_decoder_subspace` |
| `REQ-UPROF-005` | normative | unrolled `LW` or `SW` | `REQ-UPROF-001`; `REQ-MWORD-001..003`; `external:MEM` | located | family-local relation, word-address initialization/teardown universe, and global product closure | `symbol:cs/src/gkr_circuits/mem_word_only/circuit.rs#apply_mem_word_only_inner`; `symbol:cs/src/tables/rom_related.rs#create_table_for_word_aligned_rom_image`; `symbol:prover/src/gkr/virtual_polys/init_and_teardown_base.rs#materialize_virtual_inits_and_teardowns_base_address_setup_poly`; `symbol:full_statement_verifier/src/unrolled_proof_statement.rs#verify_base_or_recursion_unrolled_circuits` |
| `REQ-UPROF-006` | normative | delegation CSR call | `REQ-UPROF-001`; `external:DELEG` | located | `repo:riscv_transpiler/src/cycle/mod.rs#IMStandardIsaConfigUnsignedMulDivOnly@dfb1b2a8a`; `repo:riscv_transpiler/src/ir/simple_instruction_set.rs#DelegationType@dfb1b2a8a`; `repo:circuit_defs/setups/src/circuits/mod.rs#produce_verifier_setup_for_all_delegations@dfb1b2a8a` | `symbol:riscv_transpiler/src/cycle/mod.rs#IMStandardIsaConfigUnsignedMulDivOnly`; `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#DelegationType`; `symbol:circuit_defs/setups/src/circuits/mod.rs#produce_verifier_setup_for_all_delegations` |
| `GAP-UPROF-001` | open | — | affects profile-specific add-family relations; owner `specification` | — | `AddSubLuiAuipcMopDecoder` and circuit branches exist; no dedicated relation modules yet | — |
