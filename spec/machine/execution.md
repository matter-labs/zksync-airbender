# MACH: Machine execution composition

> Composes initialized machine state, active-cycle relations, and shared interfaces.
> ISA-family equations, profile operation inventories, and precompile internals are
> specified by their owning modules.

## Guarantee

An execution starts from the state admitted by the selected machine profile. Each
active cycle authenticates one decoder row, selects exactly one ISA relation, and
applies that relation to the machine state. A selected delegation instruction may
emit a precompile request; separate fulfillment circuits close that interface. The
complete trace closes its register, memory, continuity, lookup, and precompile
interfaces.

## Symbols

- `u32 = [0, 2^32)`.
- `P` — selected unrolled or unified machine profile.
- `B` — authenticated program image.
- `S_i = (pc_i, ts_i, Reg_i, Mem_i)` — row-`i` architectural-state witness.
- `execute_i : {0,1}` — cycle-activation flag.
- `d_i` — authenticated decoder row for cycle `i`.
- `ISA(P)` — cycle-transition relations admitted by profile `P`.
- `PRECOMP(P)` — separate fulfillment relations admitted for delegation requests in
  profile `P`.
- `Auth_DEC(P, B, pc, d)` — imported decoder-authentication predicate.
- `Select_P(d, R)` — decoder row `d` selects relation `R` under profile `P`.
- `T_i^X` — cycle-`i` multiset contribution to interface `X`, where
  `X in {REG, MEM, CONT, LOOKUP, PRECOMP}`.
- `T_i = (T_i^REG, T_i^MEM, T_i^CONT, T_i^LOOKUP, T_i^PRECOMP)` — all interface
  contributions emitted by row `i`.
- `T^X = multiset_union_i T_i^X` — complete-trace contribution to interface `X`.
- `Init_P(B, S_0)` — conjunction of the profile's imported register, memory, and
  continuity initialization predicates.
- `Close_X(T^X)` — interface `X` accepts and closes its complete-trace contribution.

The relation notation `R(S_i, S_{i+1}, T_i)` keeps both adjacent states explicit
because this module composes cycle relations. Assignment notation remains canonical
inside each selected ISA or precompile relation.

## Inputs

| Name | Meaning |
|---|---|
| `P` | selected machine profile |
| `B` | claimed program image |
| `N` | number of rows in the supplied execution trace |
| `S_0` | claimed initial architectural state |
| `(execute_i, d_i, S_{i+1}, T_i)` | row data for every `i in [0,N)` |

## Assumptions

- **ASM-MACH-001 — Decoder relation.** `DEC` defines authentication of `d_i` against
  the selected profile, program, and `pc_i`, including its relation selector.
- **ASM-MACH-002 — Lookup relation.** `LOOKUP` defines decoder-table, range-table,
  and other local lookup acceptance, including inactive-row neutrality.
- **ASM-MACH-003 — Register state.** `REG` defines register initialization and the
  consistency relation for emitted register reads and writes, including inactive-row
  neutrality.
- **ASM-MACH-004 — Memory state.** `MEM` defines RAM and ROM initialization and the
  consistency relation for emitted memory accesses, including inactive-row
  neutrality.
- **ASM-MACH-005 — Cycle continuity.** `CONT` defines initial `pc` and `ts`, active
  cycle continuity, trace-boundary continuity, and inactive-row encoding.
- **ASM-MACH-006 — ISA profiles.** `UPROF` and `UNIFIED` define `ISA(P)` and each
  admitted instruction relation for their respective profiles.
- **ASM-MACH-007 — Precompile profiles.** `PRECOMP` defines profile-dependent
  invocation and fulfillment relations for delegation requests, plus inactive-row
  neutrality; fulfillment is not a second CPU-cycle transition.

## Canonical execution tree

> Interpret the tree under `ASM-MACH-001..007`. Requirements listed on an active
> branch are conjoined.

- **Trace start.** `REQ-MACH-001` initializes `S_0`.
- **Cycle `i in [0,N)`.**
  - **`execute_i = 0`.** Padding is outside the architectural transition sequence;
    `ASM-MACH-002..005` and `ASM-MACH-007` define neutral interface encodings for
    this row.
  - **`execute_i = 1`.**
    - **[`REQ-MACH-002`] Authenticated unique selection.** Authenticate `d_i` and
      select exactly one relation in `ISA(P)`.
    - **[`REQ-MACH-003`] Selected transition.** Apply that relation to
      `(S_i, S_{i+1}, T_i)`.
- **Trace end.** `REQ-MACH-004` closes every shared interface.

## Requirements

### REQ-MACH-001 — Initialization

`Init_P(B, S_0)`.

The imported component predicates supply the concrete register, RAM/ROM, `pc`, and
timestamp values. This module only requires their conjunction for the same profile.

### REQ-MACH-002 — Authenticated unique selection

For every active cycle `i`:

`Auth_DEC(P, B, pc_i, d_i) && exists exactly one R_i in ISA(P): Select_P(d_i, R_i)`.

### REQ-MACH-003 — Selected transition

For the unique `R_i` selected by `REQ-MACH-002`:

`R_i(S_i, S_{i+1}, T_i^REG, T_i^MEM, T_i^CONT, T_i^LOOKUP, T_i^PRECOMP)`.

### REQ-MACH-004 — Interface closure

Over all rows:

`Close_REG(T^REG) && Close_MEM(T^MEM) && Close_CONT(T^CONT) && Close_LOOKUP(T^LOOKUP) && Close_PRECOMP(T^PRECOMP)`.

## Derived facts

- `REQ-MACH-001..004` make the states attached to active rows a sequence of
  profile-admitted transitions connected through the shared state interfaces.
- Choosing an unrolled or unified profile changes `ISA(P)` and its concrete
  interface encodings, not this composition rule.

## Metadata

The composition relation is normative for the selected unrolled and reduced-unified
profiles. It is supported by the adopted module interfaces and matching compiler,
prover, and full-statement-verifier evidence.

- spec revision: `2026-08-28.5`
- implementation: `matter-labs/zksync-airbender@dfb1b2a8a`
- profile: unrolled and unified machine-execution composition

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `ASM-MACH-001` | normative | active row | `external:DEC` | located | decoder preprocessing and circuit lookup at `dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit` |
| `ASM-MACH-002` | normative | all rows | `external:LOOKUP` | located | local lookup construction at `dfb1b2a8a` | `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/circuit.rs#flush_unified_lookup_pool` |
| `ASM-MACH-003` | normative | initialization and register traffic | `external:REG` | located | global register contribution construction at `dfb1b2a8a` | `symbol:prover/src/definitions/mod.rs#produce_initial_permutation_product_separate_contributions`; `symbol:full_statement_verifier/src/unrolled_proof_statement.rs#verify_base_or_recursion_unrolled_circuits` |
| `ASM-MACH-004` | normative | initialization and RAM/ROM traffic | `external:MEM` | located | family memory contributions and full-statement closure at `dfb1b2a8a` | `symbol:prover/src/gkr/witness_gen/family_circuits/memory.rs#evaluate_gkr_memory_witness_for_executor_family`; `symbol:full_statement_verifier/src/unified_circuit_statement.rs#verify_unrolled_or_unified_circuit_recursion_layer` |
| `ASM-MACH-005` | normative | initialization, active rows, and trace boundaries | `external:CONT` | located | initial PC/timestamp constants and state-product closure at `dfb1b2a8a` | `symbol:common_constants/src/lib.rs#INITIAL_PC`; `symbol:common_constants/src/timestamps.rs#INITIAL_TIMESTAMP`; `symbol:common_constants/src/timestamps.rs#TIMESTAMP_STEP`; `symbol:full_statement_verifier/src/unrolled_proof_statement.rs#verify_base_or_recursion_unrolled_circuits` |
| `ASM-MACH-006` | normative | selected profile | `external:UPROF`; `external:UNIFIED` | located | unrolled profile configuration and unified family dispatch at `dfb1b2a8a` | `symbol:riscv_transpiler/src/cycle/mod.rs#IMStandardIsaConfigUnsignedMulDivOnly`; `symbol:riscv_transpiler/src/cycle/mod.rs#ReducedMachineWithDelegation`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/circuit.rs#apply_unified_family_dispatch_one_hot` |
| `ASM-MACH-007` | normative | selected profile | `external:PRECOMP` | located | delegation profile configuration and precompile circuit modules at `dfb1b2a8a` | `symbol:riscv_transpiler/src/cycle/mod.rs#IMStandardIsaConfigUnsignedMulDivOnly`; `symbol:cs/src/gkr_circuits/delegation/blake2_g_function/mod.rs#define_blake2_g_function_delegation_circuit`; `symbol:cs/src/gkr_circuits/delegation/keccak_special5/mod.rs#define_keccak_special5_delegation_circuit` |
| `REQ-MACH-001` | normative | trace start | `ASM-MACH-003..005` | located | implementation initialization at `dfb1b2a8a` | `symbol:prover/src/definitions/mod.rs#produce_initial_permutation_product_separate_contributions`; `symbol:common_constants/src/lib.rs#INITIAL_PC`; `symbol:common_constants/src/timestamps.rs#INITIAL_TIMESTAMP` |
| `REQ-MACH-002` | normative | active row | `ASM-MACH-001`, `ASM-MACH-002`, `ASM-MACH-006`, `ASM-MACH-007` | located | unrolled decode lookup and unified one-hot dispatch at `dfb1b2a8a` | `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/circuit.rs#apply_unified_family_dispatch_one_hot` |
| `REQ-MACH-003` | normative | active row | `REQ-MACH-002`, `ASM-MACH-003..007` | located | family-circuit and unified-machine constraint construction at `dfb1b2a8a` | `symbol:cs/src/gkr_compiler/family_circuit.rs#GKRCompiler::compile_family_circuit`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/circuit.rs#apply_unified_reduced_machine_inner` |
| `REQ-MACH-004` | normative | complete trace | `REQ-MACH-001..003`, `ASM-MACH-002..005`, `ASM-MACH-007` | located | full-statement unrolled and unified closure at `dfb1b2a8a` | `symbol:full_statement_verifier/src/unrolled_proof_statement.rs#verify_base_or_recursion_unrolled_circuits`; `symbol:full_statement_verifier/src/unified_circuit_statement.rs#verify_unrolled_or_unified_circuit_recursion_layer` |
