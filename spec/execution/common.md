# EXEC: Machine execution and cycle progression

1. Define the admitted program image and how it is bound to its decoder/setup data.
2. Define the logical execution as a sequence of cycles.
3. For each cycle:
    - authenticate the instruction at the current pc;
    - select exactly one ISA-family relation;
    - apply its state changes;
    - connect its ending machine state to the next cycle.

4. Partition logical cycles by circuit family.
5. Preserve every cycle exactly once, including its logical ordering information.
6. Split each family sequence into fixed-capacity chunks.
7. Pad the final chunk with inactive rows that create no machine transition or argument contribution.

> Defines the shared machine-cycle relation. ISA equations, physical unrolled or
> unified layouts, and the algebra of register, memory, and lookup arguments are
> specified by their owning modules.

`*` marks a provisional relation whose intended detail or implementation binding
remains open.

## Guarantee

One admitted program image determines the decoder data used by every active cycle.
Each active cycle authenticates one instruction family and applies exactly that
family's ISA relation. The active cycle effects compose into one logical execution
between the admitted initial and final machine boundaries. Inactive rows create no
logical cycle or architectural effect.

The logical execution is a semantic view of the accepted rows. It need not be an
additional sequence serialized by the prover.

## Symbols and inputs

- **IN-EXEC-001 — Execution profile.** `P` selects one ISA inventory and one
  execution layout; `ISA(P)` is the set of ISA-family relations it admits
- **IN-EXEC-002* — Program image.** `B = (B_rom, B_text)` is the program whose
  execution is claimed; `B_rom` supplies the ROM image and `B_text` supplies the
  instruction words used for preprocessing and decoder setup
- **IN-EXEC-003 — Physical rows.** `Rows` is the finite collection of execution rows
  supplied by the selected layout
- `execute_r ∈ {0, 1}` — activation flag of row `r ∈ Rows`
- `Active = {r ∈ Rows | execute_r = 1}` and `n = |Active|`
- `d_r` — decoder data carried by row `r`
- `op_r` — instruction operation authenticated by `d_r`
- `f_r` — ISA family selected for row `r`
- `family_P(op)` — circuit family assigned to operation `op` by profile `P`
- `place_P` — placement of logical cycles into profile-selected circuit chunks and
  rows; this may be a semantic correspondence rather than proof-carried data
- `S_r^start`, `S_r^end` — logical machine-state endpoints of an active row
- `T_r` — register, memory, PC-state, lookup, and delegation contributions emitted
  by row `r`
- **IN-EXEC-004* — Machine boundaries.** `S_initial` and `S_final` are the admitted
  execution-boundary claims
- `C = (c_0, ..., c_{n-1})` — logical cycle chain induced by the active rows and the
  accepted state-continuity arguments
- `u38 = [0, 2³⁸)` — timestamp domain
- `PCState(pc, ts)` — typed global-state tuple carrying a program counter and
  timestamp

`S_r^start` and `S_r^end` are semantic endpoints. Their register and memory parts may
be represented by timestamped argument contributions rather than explicit complete
state vectors in each row.

## Assumptions

- **ASM-EXEC-001 — ISA-family relations.** Every `R ∈ ISA(P)` defines its active
  cycle state changes and emitted argument contributions.
- **ASM-EXEC-002* — Decoder-table membership.** The lookup component binds an
  activated decoder query to the program-dependent table selected for `B` and `P`.
- **ASM-EXEC-003* — State-argument closure.** The register, memory, PC-state, lookup,
  and delegation components bind accepted row contributions according to their
  respective relations.

## Canonical relation tree

> Interpret the relations below under `ASM-EXEC-001..003`. All top-level relations
> are conjoined. A relation branches only where its accepted cases differ.

- **[`REL-EXEC-001`]* Proven program**

  `B = (B_rom, B_text) ∈ Programs(P)`

  Each raw file has byte length divisible by four and is interpreted as
  little-endian `u32` words. Proving padding is derived after loading the raw files.
  The execution proving path does not parse these files as ELF containers.
  The same `B` determines the ROM contents, preprocessed decoder data, circuit
  setups, and expected exit PC.

  - **Base application profile.** `B_rom` and `B_text` come from the caller-supplied
    `ProgramSource.bin_path` and `ProgramSource.text_path`. If `text_path` is omitted,
    it is derived from `bin_path`. The base profile admits the full-unsigned Airbender
    RV32I/unsigned-M ISA and its selected custom operations. The repository's
    `riscv_transpiler/examples/zksync_os/app.{bin,text}` pair is one example, not the
    complete admitted set
  - **Unrolled recursion profile.** `B` is loaded from
    `<fsv_dir>/fsv_unrolled_{base_layer,recursion_layer}_sec_100_<blake>.{bin,text}`,
    where `<fsv_dir>` is `FSV_DIR` when set and otherwise `tools/gkr_verifier`, and
    `<blake> ∈ {blake2_with_compression, blake2_g_function}`
  - **Unified bridge profile.** `B` is the selected unrolled base-layer or
    recursion-layer verifier pair above, executed by the reduced unified machine
  - **Unified recursion profile.** `B` is loaded from
    `<fsv_dir>/fsv_unified_recursion_layer_sec_100_<blake>.{bin,text}`,
    where `<blake> ∈ {blake2_with_compression, blake2_g_function,
    special_opcodes_extension}`
  - **Experimental L1 profile.** `B` is
    `tools/gkr_verifier/fsv_unified_recursion_layer_sec_100_l1_feeder_special_opcodes_extension.{bin,text}`

  A registry entry names an admissible verifier program variant but does not provide
  its bytes. The selected `.bin` and `.text` pair must exist in `<fsv_dir>`; the
  current checkout contains the compression variants for both unrolled programs and
  the compression and special-opcode variants for unified recursion. Other
  registry-supported variants require separately generated files

- **[`REL-EXEC-002`]* Bounded clocked cycles**

  Let `c_i` be logical cycle `i ∈ [0, n)`. The accepted execution satisfies:

  ```text
  n < 2³⁶
  c_i.ts_start = 4 + 4i
  c_i.ts_end = c_i.ts_start + 4
  c_i.ts_start, c_i.ts_end ∈ u38
  ```

  The selected execution profile may impose a smaller bound: the current recursion
  profiles use `2²⁸` for unrolled recursion and `2²⁷` for unified bridge and
  recursion; the experimental L1 execution must fit one `2²²`-row chunk. The base
  application bound is supplied by the proving configuration and remains below the
  global timestamp bound

- **[`REL-EXEC-003`]* Opcode-derived cycle placement**

  For every logical cycle `c_i`:

  `f_i = family_P(op_i)`

  `place_P(c_i)` is an active physical row whose authenticated opcode is `op_i`

  - **Unrolled layout.** The destination chunk has family `f_i`; its circuit identity
    fixes the family relation
  - **Unified layout.** The destination chunk has the unified circuit identity; its
    in-row selector fixes `f_i`

- **[`REL-EXEC-004`]* Active and padding witnesses**

  For every `r ∈ Rows`, `execute_r ∈ {0, 1}`

  - **`execute_r = 1`.** `r` lies in the image of `place_P` and contains the witness
    values derived for its logical cycle
  - **`execute_r = 0`.** `r` is padding, uses the profile- and family-specific padding
    witness, creates no machine transition, and contributes the identity element to
    every shared argument

  An ADD/NOP-shaped padding witness is not an executed architectural NOP: if such
  dummy values are used, `execute_r = 0` must mask all architectural and argument
  effects

- **[`REL-EXEC-005`] ISA transition and global-state contributions**

  For every active row `r = place_P(c_i)`, the authenticated decoder data selects
  exactly one `R_i ∈ ISA(P)`, with `f_i = family_P(op_i)`, and:

  `R_i(S_i^start, S_i^end, T_i)`

  - Decoder data derived from `(P, B_text, S_i^start.pc)` determines `op_i`, register
    indexes, immediates, and the selected family
  - Register and RAM reads in `T_i` determine the instruction operands through the
    global state argument
  - The ISA relation determines the cycle's next PC, register/RAM writes, lookup
    queries, and any delegation request, and binds them into `T_i`

- **[`REL-EXEC-006`]* Complete logical execution**

  `place_P` is a bijection from the logical cycles `C` to `Active`. Equivalently, the
  accepted rows contain no injected, omitted, duplicated, or altered active cycle

  This correspondence need not be serialized. It may follow from program-bound
  decoding, the initial and final boundaries, the strictly increasing clock, and the
  global PC/state argument. In particular, the PC-state projection satisfies:

  ```text
  {PCState(S_initial.pc, S_initial.ts)}
    ⊎ {PCState(c_i.pc_end, c_i.ts_end)}_i
  = {PCState(S_final.pc, S_final.ts)}
    ⊎ {PCState(c_i.pc_start, c_i.ts_start)}_i
  ```

- **[`REL-EXEC-007`]* Initial and final machine state**

  ```text
  S_initial.pc = 0
  S_initial.ts = 4
  S_final.pc = exit_pc(B_rom)
  S_final.ts = 4 + 4n
  ```

  `exit_pc(B_rom)` is the address of the final instruction in the unique
  `riscv_common::EXIT_SEQUENCE` contained by the admitted ROM image. Register and RAM
  initialization, finalization, and public-output selection are imported from their
  owning memory and recursion relations

- **[`OUT-EXEC-001`]* Full execution relation**

  The conjunction `REL-EXEC-001..007` states that the accepted physical rows encode
  exactly one execution of `B` from `S_initial` to `S_final` under profile `P`

## Deprecated previous relation tree

> Non-normative. Preserved temporarily for comparison while the new relation-first
> structure is reviewed.

````markdown
> Interpret this tree under `ASM-EXEC-001..003`. Within an active row, its numbered
> relations are conjoined.

- **Row `r ∈ Rows` — [`REQ-EXEC-001`] Boolean activation**
  `execute_r ∈ {0, 1}`
  - **`execute_r = 0` — [`REL-EXEC-005`] Inactive-row neutrality**
    Row `r` creates no logical cycle, performs no architectural state change, and
    contributes the identity element to every shared argument
  - **`execute_r = 1`**
    - **[`REL-EXEC-001`]* Program-bound instruction authentication**
      `d_r` authenticates against the instruction associated with
      `S_r^start.pc` under the decoder/setup data derived from the same `(P, B)`
      accepted for the execution
    - **[`REL-EXEC-002`] Unique ISA-family selection**
      The authenticated `d_r` selects exactly one `R_r ∈ ISA(P)`; its family is
      `f_r`

      The ISA profile owns the admitted family inventory. The execution layout owns
      whether a family-specific circuit or selectors inside a unified circuit
      represent `f_r`
    - **[`REL-EXEC-003`] Selected cycle transition**
      `R_r(S_r^start, S_r^end, T_r)`

      The selected ISA relation owns the instruction equation. This module owns its
      use as one step of the machine execution
- **All active rows — [`REL-EXEC-004`]* Logical machine-state progression**
  The active-row contributions induce one cycle chain
  `C = (c_0, ..., c_{n-1})` such that:

  ```text
  c_0 starts at S_initial
  c_i ends where c_(i+1) starts, for every i ∈ [0, n - 1)
  c_(n-1) ends at S_final, when n > 0
  ```

  For an empty execution, the accepted boundary relation determines whether
  `S_initial = S_final` is admitted
  - **[`OUT-EXEC-001`]* Logical execution**
    The active rows represent one program-bound logical cycle chain between
    `S_initial` and `S_final`, with every cycle governed by exactly one admitted
    ISA-family relation
````

## Open boundary

- **GAP-EXEC-001 — Accepted program/setup identity.** Specify the end-to-end binding
  from `B` to the exact decoder/setup data accepted by every execution chunk.
- **GAP-EXEC-002 — Global cycle-chain realization.** Specify which accepted proof
  structure and global arguments establish that all active rows, across all chunks,
  form exactly one chain with no omitted or additional component. This must clarify
  whether cycle coverage is explicit in the proof structure or implicit in the fixed
  program, boundary claims, PC-state transitions, and argument closure.
- **GAP-EXEC-003 — Execution boundary policy.** Specify the exact admitted initial
  and final register/RAM state, public-output selection, and the treatment of an empty
  execution. Initial PC/timestamp and the program-derived final PC are identified
  above.
- **GAP-EXEC-004 — Canonical padding witnesses.** Record the exact inactive witness
  values selected for every unrolled family and for the unified circuit, including
  which values merely resemble an ADD/NOP row while remaining masked by `execute = 0`.
- **GAP-EXEC-005 — Effective cycle bounds.** Reconcile the profile-level active-cycle
  limits, fixed chunk capacities, strict verifier capacity bound, and timestamp
  non-overflow condition into exact inequalities for every execution profile.

## Metadata

- spec revision: TBD
- implementation: `matter-labs/zksync-airbender@87b9d98ce+dirty`
- profile: shared by unrolled and reduced-unified execution profiles

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `IN-EXEC-001` | normative | — | — | prose | `decision:execution-structure-2026-09-04`; [proof profiles](../profiles/INDEX.md) | — |
| `IN-EXEC-002` | provisional | — | `GAP-EXEC-001` | prose | current execution design; legacy decoder model | — |
| `IN-EXEC-003` | normative | — | selected execution layout | prose | `decision:execution-structure-2026-09-04` | — |
| `IN-EXEC-004` | provisional | — | `GAP-EXEC-003` | prose | current execution design; legacy continuity model | — |
| `ASM-EXEC-001` | normative | active row | `external:ISA` | prose | [ISA relations](../isa/INDEX.md) | — |
| `ASM-EXEC-002` | provisional | active decoder query | `external:LOOKUP`; `GAP-EXEC-001` | located | [lookup relations](../lookups/INDEX.md); current decoder setup construction | `symbol:circuit_defs/setups/src/program_setups.rs#compute_unrolled_program_setups`; `symbol:circuit_defs/setups/src/program_setups.rs#compute_unified_program_setups` |
| `ASM-EXEC-003` | provisional | all accepted rows | `external:MEMORY`; `external:LOOKUP`; `GAP-EXEC-002..003` | located | legacy register, memory, and continuity models; full-statement verifiers | `symbol:full_statement_verifier/src/unrolled_proof_statement.rs#verify_full_statement_for_unrolled_circuits`; `symbol:full_statement_verifier/src/unified_circuit_statement.rs#verify_full_statement_for_unified_circuit` |
| `REL-EXEC-001` | provisional | selected execution profile | `IN-EXEC-001..002`; `ASM-EXEC-002`; `GAP-EXEC-001` | located | current CLI and recursion pipeline program sources | `symbol:prover_pipeline/src/lib.rs#ProgramSource`; `symbol:prover_pipeline/src/lib.rs#load_program`; `symbol:full_statement_verifier/src/host_utils/mod.rs#load_fsv_program`; `symbol:verifier_common/src/fsv_binaries.rs#FsvProgram` |
| `REL-EXEC-002` | provisional | all active cycles | `IN-EXEC-001..004`; `GAP-EXEC-005` | located | current timestamp constants, verifier ceiling, and profile bounds | `symbol:common_constants/src/timestamps.rs#INITIAL_TIMESTAMP`; `symbol:common_constants/src/timestamps.rs#TIMESTAMP_STEP`; `symbol:full_statement_verifier/src/lib.rs#MAX_CYCLES`; `symbol:prover_pipeline/src/lib.rs#UNROLLED_RECURSION_CYCLES_BOUND`; `symbol:prover_pipeline/src/lib.rs#UNIFIED_CYCLES_BOUND` |
| `REL-EXEC-003` | provisional | every logical cycle | `IN-EXEC-001..003`; `REL-EXEC-001`; `GAP-EXEC-002` | prose | `decision:execution-relations-2026-09-04`; [hierarchy](../HIERARCHY.md) | — |
| `REL-EXEC-004` | provisional | every physical row | `IN-EXEC-003`; `GAP-EXEC-004` | prose | `decision:execution-relations-2026-09-04`; current execution layouts | — |
| `REL-EXEC-005` | normative | active row | `ASM-EXEC-001..003`; `REL-EXEC-001..004` | prose | `decision:execution-relations-2026-09-04`; [ISA relations](../isa/INDEX.md) | — |
| `REL-EXEC-006` | provisional | all accepted rows | `ASM-EXEC-003`; `REL-EXEC-002..005`; `GAP-EXEC-002` | located | current full-statement permutation closure; legacy continuity relation | `symbol:full_statement_verifier/src/unrolled_proof_statement.rs#verify_full_statement_for_unrolled_circuits`; `symbol:full_statement_verifier/src/unified_circuit_statement.rs#verify_full_statement_for_unified_circuit` |
| `REL-EXEC-007` | provisional | execution boundaries | `IN-EXEC-002..004`; `REL-EXEC-001..002`; `GAP-EXEC-003` | located | current initialization, exit-sequence, and end-parameter construction | `symbol:common_constants/src/timestamps.rs#INITIAL_TIMESTAMP`; `symbol:circuit_defs/setups/src/program_setups.rs#find_binary_exit_point`; `symbol:riscv_common/src/lib.rs#EXIT_SEQUENCE` |
| `OUT-EXEC-001` | provisional | all accepted rows | `REL-EXEC-001..007`; `GAP-EXEC-001..005` | prose | derived from the execution relations above | — |
| `GAP-EXEC-001` | open | — | affects `IN-EXEC-002`, `ASM-EXEC-002`, `REL-EXEC-001`, and `OUT-EXEC-001`; owner: human | — | accepted program/setup edge not yet specified | — |
| `GAP-EXEC-002` | open | — | affects `ASM-EXEC-003`, `REL-EXEC-003`, `REL-EXEC-006`, and `OUT-EXEC-001`; owner: human | — | explicit placement versus implicit global-argument completeness unresolved | — |
| `GAP-EXEC-003` | open | — | affects `IN-EXEC-004`, `ASM-EXEC-003`, `REL-EXEC-007`, and `OUT-EXEC-001`; owner: human | — | exact register/RAM boundary and empty-execution policy not yet specified | — |
| `GAP-EXEC-004` | open | — | affects `REL-EXEC-004` and `OUT-EXEC-001`; owner: human | — | exact per-family inactive witness values not yet enumerated | — |
| `GAP-EXEC-005` | open | — | affects `REL-EXEC-002` and `OUT-EXEC-001`; owner: human | — | profile bounds and strict timestamp/capacity inequalities not yet reconciled | — |
