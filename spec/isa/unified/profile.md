# UNIFIED: Reduced unified ISA profile

> Operation inventory and dispatch boundary for the reduced unified executor
> at `dfb1b2a8a`; sibling modules own the selected operation relations

## Guarantee

The profile admits one reduced instruction set into circuit family `128`. Each active
cycle selects exactly one embedded operation body inside a single compiled executor
circuit. Standard multiply/divide and subword-memory operations are outside this
profile; delegated precompiles remain separate circuits.

## Profile inputs

- `execute ∈ {0, 1}` activates one machine cycle
- `op` is the decoder-authenticated preprocessed operation
- `d₁`, `d₂`, `d₃`, and `d₄` select the add/MOP, jump/branch/compare,
  binary/shift, and word-memory bodies
- `ReducedMachineDecoderConfig` enables MOPs and unified XOR-rotate/tri-add, and
  disables standard multiply/divide, subword memory, and ordinary rotate

## Operation inventory and dispatch

### REQ-UNIFIED-001 — Admitted operations

The profile admits exactly the following source operations and machine-interface
operations after preprocessing. Each row names the module that owns its relation.

| Body | Admitted operations | Normalized operation | Relation |
|---|---|---|---|
| `d₁` | `NOP`; `ADD`, `ADDI`, `LUI`; `SUB`; `AUIPC` | `Nop`, `Add`, `Sub`, `Auipc` | [UADD](add-sub-mop.md) |
| `d₁` | `MOP.RR.0` (`ADDMOD`), `MOP.RR.1` (`SUBMOD`), `MOP.RR.2` (`MULMOD`), `MOP.RR.3` (`FMAMOD`), `MOP.RR.4` (`TRIADD`) | internal `ZimopAdd`, `ZimopSub`, `ZimopMul`, `ZimopFMA`, `ZimopTriAdd` | [UADD](add-sub-mop.md) |
| `d₁` | `CSRRW rd, 0x7C0, x0`; `CSRRW x0, 0x7C0, rs1`; `CSRRW x0, d, x0` for `d ∈ {0x7C7, 0x7C8, 0x7CA, 0x7CB}` | internal `ZicsrNonDeterminismRead`, `ZicsrNonDeterminismWrite`, `ZicsrDelegation` | [UADD](add-sub-mop.md) and [PRECOMP](../precompiles/profile.md) |
| `d₂` | `JAL`, `JALR`; `BEQ`, `BNE`, `BLT`, `BGE`, `BLTU`, `BGEU`; `SLT`, `SLTI`, `SLTU`, `SLTIU` | `Jal`, `Jalr`, `Branch`, `Slt`, `Sltu` | [UJUMP](jump-branch-slt.md) |
| `d₃` | `AND`, `ANDI`, `OR`, `ORI`, `XOR`, `XORI`; `SLL`, `SLLI`, `SRL`, `SRLI`, `SRA`, `SRAI` | `And`, `Or`, `Xor`, `Sll`, `Srl`, `Sra` | [UBSHIFT](binary-shifts.md) |
| `d₃` | `MOP.R.16` (`XORROT16`), `MOP.R.12` (`XORROT12`), `MOP.R.8` (`XORROT8`), `MOP.R.7` (`XORROT7`) | internal `ZimopIXorRot` | [UBSHIFT](binary-shifts.md) |
| `d₄` | `LW`, `SW` | `Lw`, `Sw` | [UMWORD](memory-word.md) |

`MOP.RR.2` (`MULMOD`) is project modular arithmetic, not the standard RISC-V
`MUL`

Pure destination writes with `rd = x0`, including loads, normalize to the canonical
`Nop` row before dispatch. Jumps, branches, stores, and delegation calls do not use
that rewrite merely because their encoded destination field is `x0`.

### REQ-UNIFIED-002 — Active one-hot dispatch

Under decoder authentication:

`execute = d₁ + d₂ + d₃ + d₄`

where each `dᵢ ∈ {0, 1}` and the selected body enforces the relation named by
`REQ-UNIFIED-001`. The symbols aggregate the body's mutually exclusive operation
flags; auxiliary flags such as jump destination-is-`x0` are not dispatch selectors.
All four bodies share one machine-state allocation inside one compiled executor
circuit; delegated fulfillment uses separate precompile circuits.

## Decision tree

- **`execute = 0`**
  - `d₁ = d₂ = d₃ = d₄ = 0` under `REQ-UNIFIED-002`
  - no operation relation is active
- **`execute = 1`**
  - **`op` occurs in one row of `REQ-UNIFIED-001`**
    - exactly that row's body is active under `REQ-UNIFIED-002`
    - the linked sibling module defines the architectural relation
  - **`op` does not occur in `REQ-UNIFIED-001`**
    - unreachable under decoder authentication

Delegated-precompile admission and fulfillment selection are defined by
[PRECOMP](../precompiles/profile.md), under its `reduced-unified` profile.

## Derived facts

- **Single active body**
  `execute = 1 ⇒ d₁ + d₂ + d₃ + d₄ = 1`
- **Inactive dispatch**
  `execute = 0 ⇒ d₁ = d₂ = d₃ = d₄ = 0`

## Open boundary

- **GAP-UNIFIED-001 — Common-ISA equivalence.** No reviewed theorem or exhaustive
  conformance check establishes that every standard operation shared by the unified
  and unrolled profiles accepts exactly the same architectural transition after
  preprocessing. The profile-specific relation modules remain authoritative until a
  common implementation-independent ISA layer is adopted.

## Metadata

- spec revision: TBD
- implementation: TBD
- profile: reduced unified machine, circuit family `128`

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `REQ-UNIFIED-001` | normative | profile selection | `REL-UADD-001..004`; `OUT-UADD-001`; `REL-UJUMP-001..003`; `REL-UBSHIFT-001..003`; `REL-UMWORD-001..003`; [PRECOMP](../precompiles/profile.md) | located | [Zimop carrier syntax](https://docs.riscv.org/reference/isa/unpriv/zimop.html); [Zicsr carrier syntax](https://docs.riscv.org/reference/isa/unpriv/zicsr.html); explicit reduced-unified profile direction; reduced decoder configuration and unified decoder | `symbol:riscv_transpiler/src/ir/mod.rs#ReducedMachineDecoderConfig`; `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/decoder.rs#UnifiedReducedMachineDecoder::define_decoder_subspace` |
| `REQ-UNIFIED-002` | normative | every unified cycle | `REQ-UNIFIED-001`; `external:DEC` | located | unified decoder row, single compiled executor, and circuit dispatch constraints | `symbol:cs/src/gkr_circuits/unified_reduced_machine/decoder.rs#UnifiedReducedMachineDecoder::define_decoder_subspace`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/circuit.rs#apply_unified_family_dispatch_one_hot`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/circuit.rs#unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr_core` |
| `GAP-UNIFIED-001` | open | — | affects common ISA adoption; owner `human` | — | shared standard operations and separate profile relations; no accepted equivalence artifact | — |
