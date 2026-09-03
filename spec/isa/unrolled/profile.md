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

## Composition

### REQ-UPROF-001 — Selected components

The per-program setup map contains exactly the ordinary ISA families below. The
linked modules own their relations.

| Unrolled family | Admitted source operations or feature | Relation module |
|---|---|---|
| `AddSubLuiAuipcMopCircuit` | `ADD`, `ADDI`, `LUI`, `SUB`, `AUIPC`; canonical `NOP`; project MOP add/subtract/multiply/FMA; delegation and nondeterminism CSR paths | [ADD](add-sub.md) for the ordinary integer operations |
| `JumpBranchSltCircuit` | `JAL`, `JALR`, `BEQ`, `BNE`, `BLT`, `BGE`, `BLTU`, `BGEU`, `SLT`, `SLTI`, `SLTU`, `SLTIU` | [JUMP](jump-branch-slt.md) |
| `ShiftBinaryCircuit` | `AND`, `ANDI`, `OR`, `ORI`, `XOR`, `XORI`, `SLL`, `SLLI`, `SRL`, `SRLI`, `SRA`, `SRAI` | [BSHIFT](binary-shifts.md) |
| `LoadStoreWordOnlyCircuit` | `LW`, `SW` | [MWORD](memory-word.md) |
| `LoadStoreSubwordOnlyCircuit` | `LB`, `LBU`, `LH`, `LHU`, `SB`, `SH` | [MEMSUB](memory-subword.md) |
| `UnsignedMulDivCircuit` | `MUL`, `MULHU`, `DIVU`, `REMU` | [MULDIVU](mul-div-unsigned.md) |

Delegated-precompile admission and fulfillment selection are defined by
[PRECOMP](../precompiles/profile.md), under its `full-unrolled` profile.

## Open boundary

- **GAP-UPROF-001 — Profile-specific add-family relations.** The ordinary [ADD](add-sub.md)
  module does not yet specify the project MOP, nondeterminism, or delegation-call
  branches that share `AddSubLuiAuipcMopCircuit`. Those relations require dedicated
  modules; their absence does not make the ordinary ADD equations apply to them.

## Metadata

The profile inventory is normative for the selected full-unsigned unrolled machine.
It combines explicit project direction with the independently reviewed family
relations and matching decoder, setup, and global-argument evidence.

- spec revision: TBD
- implementation: TBD
- profile: unrolled full-unsigned base machine

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `REQ-UPROF-001` | normative | profile setup | `REL-ADD-001..002`; `REL-JUMP-001..003`; `REL-BSHIFT-001..002`; `REL-MWORD-001..003`; `REL-MEMSUB-001..002`; `REL-MULDIVU-001..002`; `REQ-PRECOMP-002`; `REQ-PRECOMP-004` | located | `repo:riscv_transpiler/src/cycle/mod.rs#IMStandardIsaConfigUnsignedMulDivOnly@dfb1b2a8a`; `repo:riscv_transpiler/src/ir/mod.rs#FullUnsignedMachineDecoderConfig@dfb1b2a8a`; installed family decoders and setup map; full-unrolled precompile admission and dispatch | `symbol:riscv_transpiler/src/cycle/mod.rs#IMStandardIsaConfigUnsignedMulDivOnly`; `symbol:riscv_transpiler/src/ir/mod.rs#FullUnsignedMachineDecoderConfig`; `symbol:circuit_defs/setups/src/unrolled_circuits/mod.rs#get_unrolled_circuits_setups_for_machine_type`; `symbol:cs/src/gkr_circuits/decoder_trait.rs#opcodes_for_full_machine_with_unsigned_mul_div_only_with_mem_word_access_specialization`; `symbol:circuit_defs/setups/src/circuits/mod.rs#produce_verifier_setup_for_all_delegations` |
| `GAP-UPROF-001` | open | — | affects profile-specific add-family relations; owner `specification` | — | `AddSubLuiAuipcMopDecoder` and circuit branches exist; no dedicated relation modules yet | — |
