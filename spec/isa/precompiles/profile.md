# PRECOMP: Precompile profiles

> Profile-aware inventory of delegated operations and their shared invocation interface;
> precompile arithmetic, ABI equations, and proof topology are out of scope.

`*` marks a provisional relation whose exact carrier or delegation interface is still
supported primarily by implementation evidence and the gaps below.

## Guarantee

The selected machine profile admits only the delegation types listed below. Each
admitted carrier run becomes one delegated operation, identified by its delegation
type and invocation timestamp, and is fulfilled by the designated circuit through
the global delegation argument.

## Assumptions

- **ASM-PRECOMP-001* — Authenticated carrier decode.** Bytecode preprocessing
  authenticates the carrier sequence, delegation type, and selected machine profile.
- **ASM-PRECOMP-002* — Delegation-argument closure.** The global argument equates the
  machine's invocation multiset with the fulfillment circuits' complementary multiset,
  including delegation type and invocation timestamp.

## Supported operations

### REQ-PRECOMP-001* — Profile admission

| Delegated operation | Carrier | Complete carrier run | Full unrolled | Reduced unrolled | Reduced unified | Fulfillment circuit | Planned relation |
|---|---:|---:|---|---|---|---|---|
| Blake2s round/compression, reduced or full rounds | `CSRRW x0, 0x7c7, x0` | 7 or 10 calls | admitted | admitted | admitted | `Blake2sWithCompressionDelegationCircuit` | `blake2s-round.md` |
| Blake2s G-function sequence, reduced or full rounds | `CSRRW x0, 0x7c8, x0` | 56 or 80 calls | admitted | admitted | admitted | `Blake2sGFunctionDelegationCircuit` | `blake2s-g.md` |
| Bigint with control bits for add, subtract, subtract-and-negate, low/high multiply, equality, memory copy, and carry/borrow | `CSRRW x0, 0x7ca, x0` | 1 call | admitted | not admitted | not admitted | `BigIntDelegationCircuit` | `bigint.md` |
| Keccak-f1600 `special5` | `CSRRW x0, 0x7cb, x0` | 649 calls | admitted | not admitted | not admitted | `KeccakSpecial5DelegationCircuit` | `keccak.md` |

Here, full unrolled means `IMStandardIsaConfigUnsignedMulDivOnly`; reduced unrolled
means `ReducedMachineWithDelegation`; reduced unified uses the same two allowed Blake
CSR types in `unified_reduced_machine_circuit_setup`.
`ReducedMachineWithoutDelegation` admits no row in this table.
`IMStandardIsaConfig` advertises the same four delegation CSR types, but this module
does not claim that its signed-M unrolled proving path is supported.

### REQ-PRECOMP-002* — Invocation and fulfillment

For an admitted carrier run:

1. preprocessing emits one `ZicsrDelegation` operation with the selected delegation
   type;
2. machine execution contributes one zero-valued delegation-bus item at the virtual
   register address equal to that type and binds it to the invocation timestamp;
3. the designated fulfillment circuit contributes the complementary bus item with
   the same type and timestamp and constrains its register and indirect-memory
   accesses; and
4. acceptance requires the two multisets to match under `ASM-PRECOMP-002`.

The planned per-precompile relation owns the operation-specific state transformation
and ABI; this profile module owns only admission and dispatch.

## Open boundary

- **GAP-PRECOMP-001 — Precompile relations.** Specify the exact Blake2s round,
  Blake2s G-function, bigint-control, and Keccak-f1600 relations in the four planned
  modules named in `REQ-PRECOMP-001`.
- **GAP-PRECOMP-002 — Carrier and precompile ABIs.** Review and adopt the exact
  carrier encodings and run lengths, profile admission, delegation-bus encoding,
  register roles, pointer alignment, control encoding, indirect-memory layout, access
  timestamps, and state/output conventions.

## Metadata

- spec revision: `2026-08-28.5`
- implementation: `matter-labs/zksync-airbender@dfb1b2a8ab3c29cd1024ae98dbc2bd4a7d164365+dirty`
- profile: `full-unrolled; reduced-unrolled-with-delegation; reduced-unified`

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `ASM-PRECOMP-001` | provisional | always | `GAP-PRECOMP-002`; `external:decoder-and-bytecode-authentication` | located | `repo:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode@dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode` |
| `ASM-PRECOMP-002` | provisional | always | `GAP-PRECOMP-002`; `external:delegation-global-argument` | located | `repo:cs/src/gkr_compiler/memory_like_grand_product.rs#layout_initial_grand_product_accumulation@dfb1b2a8a` | `symbol:cs/src/gkr_compiler/memory_like_grand_product.rs#layout_initial_grand_product_accumulation` |
| `REQ-PRECOMP-001` | provisional | selected machine profile | `ASM-PRECOMP-001`; `GAP-PRECOMP-002` | located | `repo:riscv_transpiler/src/cycle/mod.rs#MachineConfig@dfb1b2a8a`; `repo:circuit_defs/setups/src/unrolled_circuits/unifier_reduced_machine_circuit/mod.rs#unified_reduced_machine_circuit_setup@dfb1b2a8a`; `repo:circuit_defs/setups/src/circuits/mod.rs#produce_verifier_setup_for_all_delegations@dfb1b2a8a` | `symbol:riscv_transpiler/src/cycle/mod.rs#MachineConfig`; `symbol:circuit_defs/setups/src/unrolled_circuits/unifier_reduced_machine_circuit/mod.rs#unified_reduced_machine_circuit_setup`; `symbol:circuit_defs/setups/src/circuits/mod.rs#produce_verifier_setup_for_all_delegations` |
| `REQ-PRECOMP-002` | provisional | admitted carrier run | `ASM-PRECOMP-001`, `ASM-PRECOMP-002`, `REQ-PRECOMP-001`; `GAP-PRECOMP-001..002` | located | `repo:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode@dfb1b2a8a`; `repo:cs/src/gkr_circuits/add_sub_family/circuit.rs#apply_add_sub_lui_auipc_mop_inner@dfb1b2a8a`; `repo:cs/src/gkr_compiler/delegation_circuit.rs#compile_delegation_circuit@dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:cs/src/gkr_circuits/add_sub_family/circuit.rs#apply_add_sub_lui_auipc_mop_inner`; `symbol:cs/src/gkr_compiler/delegation_circuit.rs#compile_delegation_circuit` |
| `GAP-PRECOMP-001` | open | — | affects future `blake2s-round.md`, `blake2s-g.md`, `bigint.md`, and `keccak.md`; owner: human | — | implementation circuits exist, but their exact relations have not been reconciled into specification modules | — |
| `GAP-PRECOMP-002` | open | — | affects `ASM-PRECOMP-001..002`, `REQ-PRECOMP-001..002`, and all four future relation modules; owner: human | — | carrier, profile, ABI, witness, and circuit-access details are currently supported primarily by implementation evidence | — |
