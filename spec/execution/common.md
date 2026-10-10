# EXEC: Machine execution and cycle progression

> Defines the shared machine-cycle relation. ISA equations, physical unrolled or
> unified layouts, and the algebra of register, memory, and lookup arguments are
> specified by their owning modules.

`*` marks a provisional relation whose intended detail or implementation binding
remains open.

## Guarantee

The selected `program.bin` determines the initial ROM; `program.text` and `profile`
determine the decoder tables. Every active cycle fetches an instruction from
`program.text`, selects exactly one ISA family, and satisfies that family's
relation. Ordered by timestamp, the active cycles form one execution from the
admitted entry state to the admitted exit state. Inactive chunk slots create no
machine transition or shared-argument contribution.

Timestamp order defines the logical execution independently of the physical order
of rows and chunks.

## Symbols and inputs

- `profile ∈ Profiles` — selects one ISA inventory and one execution layout from the
  [available profiles](../profiles/INDEX.md); the selected ISA module specifies
  `profile.isa`
- `program = (program.bin, program.text) ∈ Programs` — program whose execution is
  claimed
- `u32 = [0, 2³²)` — machine-word domain
- `Timestamps = u38 = [0, 2³⁸)` — global logical-clock domain
- `s.{bin,text} := (s.bin, s.text)` — shorthand for the binary/text pair with path
  stem `s`
- `EXIT_SEQUENCE ∈ profile.isa^17` — fixed instruction sequence:

  ```text
  EXIT_SEQUENCE = (
    lw x10,  0(x26),
    lw x11,  4(x26),
    lw x12,  8(x26),
    lw x13, 12(x26),
    lw x14, 16(x26),
    lw x15, 20(x26),
    lw x16, 24(x26),
    lw x17, 28(x26),
    lw x18, 32(x26),
    lw x19, 36(x26),
    lw x20, 40(x26),
    lw x21, 44(x26),
    lw x22, 48(x26),
    lw x23, 52(x26),
    lw x24, 56(x26),
    lw x25, 60(x26),
    jal x0, 0
  )
  ```
- `exit_pc` — byte address of the final word in the unique `EXIT_SEQUENCE`
- `Families` — accepted instruction-circuit families
- `Families(isa) ⊆ Families` — families selected by `isa`; `𝓕` denotes one such family
- <code>text</code><sub>𝓕</sub> — complete indexed subsequence of
  `program.text` belonging to `𝓕`, retaining its original program indices
- `⊎` — indexed disjoint union; every original indexed element occurs in exactly one
  operand and retains its index
- `𝓕.Decode(instruction)` — decoder row derived from one instruction of `𝓕`
- `𝓕.Decoder` — immutable decoder table for `𝓕`
- `𝓕.Padding` — non-member decoder row used to fill `𝓕.Decoder`
- `ROM, RAM : 4ℕ ⇀ u32` — word-valued maps indexed by aligned byte addresses
- `dom(M)` — addresses on which partial map `M` is defined
- `x0, ..., x31 ∈ u32` — RISC-V integer registers, with ABI aliases:

  ```text
  x0/zero, x1/ra,  x2/sp,   x3/gp,  x4/tp,  x5/t0,  x6/t1,  x7/t2,
  x8/s0/fp, x9/s1, x10/a0, x11/a1, x12/a2, x13/a3, x14/a4, x15/a5,
  x16/a6, x17/a7, x18/s2, x19/s3, x20/s4, x21/s5, x22/s6, x23/s7,
  x24/s8, x25/s9, x26/s10, x27/s11, x28/t3, x29/t4, x30/t5, x31/t6
  ```
- `cycles` — finite unordered set of active machine cycles
- `PCState : Timestamps ⇀ u32` — program counter at each admitted state boundary
- `program_output` — profile-selected tuple of terminal register values
- `cycle.text ∈ program.text` — instruction executed by `cycle`
- `cycle.timestamp ∈ Timestamps` — timestamp at the beginning of `cycle`; its ending
  timestamp is `cycle.timestamp + 4`
- `𝓕.Execute(cycle)` — family execution predicate exported by the
  [shared ISA execution interface](../isa/INDEX.md#shared-execution-notation)
- <code>cycles</code><sub>𝓕</sub> — cycles whose instruction belongs to
  <code>text</code><sub>𝓕</sub>
- <code>k</code><sub>𝓕</sub><code> = |cycles</code><sub>𝓕</sub><code>|</code> — number of
  active cycles of `𝓕`
- `𝓕.ChunkCycles` — cycle slots in one `𝓕` chunk under the selected profile
- <code>chunks</code><sub>𝓕</sub> — number of supplied execution chunks for `𝓕`
- <code>chunk</code><sub>𝓕</sub><code>[j][t]</code> — slot `t` of family `𝓕`'s chunk `j`;
  `.execute ∈ {0, 1}` selects an active `.cycle` or padding
- `capacity` — total number of supplied chunk slots

## Assumptions

- **ASM-EXEC-001 — ISA-family relations.** Every instruction in `profile.isa` has one
  owning ISA-family relation defining its active-cycle state changes and emitted
  argument contributions.
- **ASM-EXEC-002* — Decoder-table membership.** Every active cycle's decoder query
  is authenticated against the family decoder derived from the selected
  `program.text` and `profile`.
- **ASM-EXEC-003* — State-argument closure.** The register, memory, PC-state, lookup,
  and delegation arguments close the active-cycle and boundary contributions under
  their owning relations. The [common memory relation](../memory/common.md) owns
  the read/write realization of PC-state continuity.

## Canonical relation tree

> Interpret the relations below under `ASM-EXEC-001..003`. All top-level relations
> are conjoined. A relation branches only where its accepted cases differ.

- **[`REL-EXEC-001`]* Proven program**

  ```text
  program ∈ Programs ⊆ Bin × Text
  Bin × Text = u32^N × u32^n
  N = |program.bin| ∧ n = |program.text|
  0 ≤ n ≤ N ≤ 2²⁰
  profile.isa ⊆ RV32IM + Zimop + Zicsr
  program.text ∈ profile.isa^n
  program.text = program.bin[0 .. n)

  {exit_pc} = {4i | i ∈ [16, n) ∧ program.text[i - 16 .. i + 1) = EXIT_SEQUENCE}

  Programs = {
    matter-labs/zksync-os::{singleblock_batch,multiblock_batch}.{bin,text},
    tools/gkr_verifier/fsv_unrolled_base_layer_sec_100_blake2_with_compression.{bin,text},
    tools/gkr_verifier/fsv_unrolled_recursion_layer_sec_100_blake2_with_compression.{bin,text},
    tools/gkr_verifier/fsv_unified_recursion_layer_sec_100_blake2_with_compression.{bin,text},
    tools/gkr_verifier/fsv_unified_recursion_layer_sec_100_special_opcodes_extension.{bin,text},
    tools/gkr_verifier/fsv_unified_recursion_layer_sec_100_l1_feeder_special_opcodes_extension.{bin,text}
  }
  ```

  `program.bin` is the raw load image: instruction words, initialized static data,
  and linker-inserted alignment. `program.text` is its executable `.text` prefix.
  Both are little-endian word sequences extracted from the same linked RISC-V ELF.
  Proving consumes the raw pair, not the ELF container

- **[`REL-EXEC-002`]* Offline decoder and initial memory**

  - **Offline preprocessing — no timestamp**

    <pre>∀ Family 𝓕 ∈ Families(profile.isa):
      text<sub>𝓕</sub> ⊆ program.text
      m<sub>𝓕</sub> = |text<sub>𝓕</sub>|
      text<sub>𝓕</sub> ∈ 𝓕<sup>m<sub>𝓕</sub></sup>

      ∀ i ∈ [0, m<sub>𝓕</sub>): 𝓕.Decoder[i] = 𝓕.Decode(text<sub>𝓕</sub>[i])
      ∀ i ∈ [m<sub>𝓕</sub>, 2²⁰): 𝓕.Decoder[i] = 𝓕.Padding

    program.text = ⊎<sub>𝓕 ∈ Families(profile.isa)</sub> text<sub>𝓕</sub>
    <small><i>(each executable instruction belongs to exactly one ISA family)</i></small>
    </pre>

    ```text
    Families = {
      AddSubLuiAuipcMopCircuit,
      JumpBranchSltCircuit,
      ShiftBinaryCircuit,
      LoadStoreWordOnlyCircuit,
      LoadStoreSubwordOnlyCircuit,
      UnsignedMulDivCircuit,
      UnifiedReducedMachineCircuit
    }
    ```

  - **`timestamp = 0` — Memory and registers initialization**

    ```text
    dom(ROM) = {4i | i ∈ [0, 2²⁰)}
    dom(RAM) = {4i | i ∈ [2²⁰, 2²⁸)}
    dom(ROM) ∩ dom(RAM) = ∅

    ∀ i ∈ [0, 2²⁰):
                    ⎧ program.bin[i]  if i < |program.bin|
      ROM[4i] =     ⎨
                    ⎩ 0               if i ≥ |program.bin|

    ∀ i ∈ [2²⁰, 2²⁸): RAM[4i] ← 0
    ∀ x ∈ {x0, x1, …, x31}: x ← 0
    ```

- **[`REL-EXEC-003`]* PC-state and final machine state**

  - **PC-state domain**

    ```text
    PCState : {4 + 4i | i ∈ [0, |cycles| + 1)} → u32
    ```

  - **`timestamp = 4` — Execution entry**

    `PCState[4] = 0`

  - **`timestamp = 4 + 4 · |cycles|` — Execution exit**

    ```text
    PCState[4 + 4 · |cycles|] = exit_pc
    x0 = 0
    ```

    - **`profile = base-unrolled-full-unsigned`**

      ```text
      program_output = (x10, x11, x12, x13, x14, x15, x16, x17)
      (x18, x19, ..., x25) = (0, 0, ..., 0)
      ```

    - **`profile ∈ {recursion-unrolled-reduced, bridge-unified-reduced,`**
      **`recursion-unified-reduced, l1-proth120}`**

      `program_output = (x10, x11, ..., x25)`

- **[`REL-EXEC-004`]* Bounded cycle timeline**

  - **Cycle execution, collection, and chunking**

    <pre>cycles ⊆ program.text × Timestamps
    <small><i>(active cycles are instruction–timestamp pairs)</i></small>

    ∀ cycle ∈ cycles:
      PCState[cycle.timestamp] ∈ {4i | i ∈ [0, n)}
    <small><i>(active PCs are aligned executable addresses)</i></small>

    ∀ cycle ∈ cycles:
      cycle.text = program.text[PCState[cycle.timestamp] / 4]
    <small><i>(instruction fetch follows PCState)</i></small>

    ∀ Family 𝓕 ∈ Families(profile.isa):
      cycles<sub>𝓕</sub> ⊆ cycles
      cycles<sub>𝓕</sub> ⊆ text<sub>𝓕</sub> × Timestamps
      ∀ cycle ∈ cycles:
        cycle ∈ cycles<sub>𝓕</sub> ⇔ cycle.text ∈ text<sub>𝓕</sub>
      <small><i>(exact family restriction)</i></small>

      ∀ cycle ∈ cycles<sub>𝓕</sub>:
        pc = PCState[cycle.timestamp]
        next_pc = PCState[cycle.timestamp + 4]
        𝓕.Execute(cycle)
      <small><i>(family ISA transition across adjacent PC states)</i></small>

      k<sub>𝓕</sub> = |cycles<sub>𝓕</sub>|
      chunks<sub>𝓕</sub> = ⌈k<sub>𝓕</sub> / 𝓕.ChunkCycles⌉
      <small><i>(family cycle and chunk counts)</i></small>

      ∀ j ∈ [0, chunks<sub>𝓕</sub>), t ∈ [0, 𝓕.ChunkCycles):
        chunk<sub>𝓕</sub>[j][t].execute =
          ⎧ 1  if j · 𝓕.ChunkCycles + t &lt; k<sub>𝓕</sub>
          ⎩ 0  otherwise
        <small><i>(active-prefix and padding selection)</i></small>

        chunk<sub>𝓕</sub>[j][t].execute = 1
          ⇒ chunk<sub>𝓕</sub>[j][t].cycle ∈ cycles<sub>𝓕</sub>
        <small><i>(active slots contain family cycles)</i></small>

      ∀ cycle ∈ cycles<sub>𝓕</sub>:
        ∃ j ∈ [0, chunks<sub>𝓕</sub>), t ∈ [0, 𝓕.ChunkCycles):
          chunk<sub>𝓕</sub>[j][t].execute = 1
          ∧ chunk<sub>𝓕</sub>[j][t].cycle = cycle
      <small><i>(every family cycle is placed)</i></small>

    </pre>

    <small><i>(Inactive slots create no machine transition and contribute the identity
    element to every shared argument)</i></small>

  <pre>𝓕.ChunkCycles =
    ⎧ 2²⁴  if profile ∈ {base-unrolled-full-unsigned,
    ⎪                      recursion-unrolled-reduced}
    ⎨ 2²³  if profile ∈ {bridge-unified-reduced,
    ⎪                      recursion-unified-reduced}
    ⎩ 2²²  if profile = l1-proth120
  <small><i>(profile-selected cycles per chunk)</i></small>
  </pre>

  <pre>|cycles| = Σ<sub>𝓕 ∈ Families(profile.isa)</sub> k<sub>𝓕</sub>  <small><i>(total active-cycle count)</i></small>
  |cycles| ≤ capacity = Σ<sub>𝓕 ∈ Families(profile.isa)</sub> chunks<sub>𝓕</sub> · 𝓕.ChunkCycles &lt; 2³⁶  <small><i>(padded chunk capacity)</i></small>
  4 + 4 · |cycles| &lt; 2³⁸  <small><i>(no timestamp overflow)</i></small>
  </pre>

  <pre>
  ∀ cycle_a ∈ cycles:
    cycle_a.timestamp + 4 ∈ dom(PCState)
    cycle_a.timestamp + 4 &lt; 4 + 4 · |cycles|
      ⇒ ∃ cycle_b ∈ cycles:
           cycle_b.timestamp = cycle_a.timestamp + 4
  <small><i>(successive cycles are four timestamps apart; the final PCState has no cycle)</i></small>

  ∀ cycle_a, cycle_b ∈ cycles:
    cycle_a.timestamp = cycle_b.timestamp ⇒ cycle_a = cycle_b
  <small><i>(no duplicate cycle timestamps)</i></small>
  </pre>

- **[`REL-EXEC-005`]* Nondeterministic input and output**

  Every nondeterministic value affecting an active cycle is read or written through
  an authenticated CSR operation admitted by `profile.isa`. The ISA relation owns the
  CSR address, value, and local state transition; execution composes its emitted
  contribution into the logical cycle chain

- **[`REL-EXEC-006`]* Recursive execution**

  Under a recursive profile, the executed program is the profile-selected verifier
  program. Its nondeterministic input contains the preceding proof, and the resulting
  proof may become the input to the next recursive execution

## Derived facts

- **Full execution**

  `REL-EXEC-001..005` imply that the accepted physical rows encode exactly one
  execution of `program` from `pc = 0` at `timestamp = 4` to `pc = exit_pc` at
  `timestamp = 4 + 4 · |cycles|` under `profile`

- **Effective cycle bound**

  `|cycles| ≤ min(capacity, 2³⁶ - 2)`

- **Initialization separation**

  `min(dom(PCState)) = 4 > 0`

- **Nonempty execution**

  `|cycles| > 0`

- **First cycle**

  ```text
  |cycles| > 0 ⇒ ∃! cycle ∈ cycles:
    cycle.timestamp = 4
    cycle.text = program.text[0]
  ```

- **Active-row completeness**

  Every logical cycle occupies exactly one active chunk slot, and every active chunk
  slot contains exactly one logical cycle

## Open boundary

- **GAP-EXEC-001 — Accepted program-pair and setup identity.** Specify the end-to-end
  binding from the same-ELF `(program.bin, program.text)` relation and named program
  source to the exact ROM, decoder, and setup data accepted by every execution chunk.
- **GAP-EXEC-002 — Global cycle-chain realization.** Specify which accepted proof
  structure and global arguments establish that all active rows, across all chunks,
  form exactly one chain with no omitted or additional component. This must clarify
  whether cycle coverage is explicit in the proof structure or implicit in the fixed
  program, boundary claims, PC-state transitions, and argument closure.
- **GAP-EXEC-005 — Unified capacity accounting.** Decide whether the shared `2³⁶`
  ceiling counts each reduced-unified chunk by its actual `2²³` rows or the full-
  statement verifier's current conservative `2²⁴` charge.
- **GAP-EXEC-006 — Nondeterministic interface binding.** Specify the exact external
  ordering and binding of nondeterministic CSR reads and writes imported from the ISA
  relation.

## Metadata

- spec revision: TBD
- implementation: `matter-labs/zksync-airbender@303ea6fa+dirty`
- profile: `base-unrolled-full-unsigned`, `recursion-unrolled-reduced`,
  `bridge-unified-reduced`, `recursion-unified-reduced`, and `l1-proth120`

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `ASM-EXEC-001` | normative | active row | `external:ISA` | prose | [ISA relations](../isa/INDEX.md) | — |
| `ASM-EXEC-002` | provisional | active decoder query | `external:LOOKUP`; `GAP-EXEC-001` | located | [lookup relations](../lookups/INDEX.md); current decoder setup construction | `symbol:circuit_defs/setups/src/program_setups.rs#compute_unrolled_program_setups`; `symbol:circuit_defs/setups/src/program_setups.rs#compute_unified_program_setups` |
| `ASM-EXEC-003` | provisional | all accepted rows | `external:MEMORY`; `external:LOOKUP`; `GAP-EXEC-002` | located | legacy register, memory, and continuity models; full-statement verifiers | `symbol:full_statement_verifier/src/unrolled_proof_statement.rs#verify_full_statement_for_unrolled_circuits`; `symbol:full_statement_verifier/src/unified_circuit_statement.rs#verify_full_statement_for_unified_circuit` |
| `REL-EXEC-001` | provisional | selected program | `GAP-EXEC-001` | located | `decision:execution-program-model-2026-09-08`; zkSync OS build source at `matter-labs/zksync-os/zksync_os/dump_bin.sh` with revision unresolved by `GAP-EXEC-001`; current linker, raw program loader, recursion pipeline, and shipped verifier pairs | `symbol:prover_pipeline/src/lib.rs#ProgramSource`; `symbol:prover_pipeline/src/lib.rs#load_program`; `symbol:full_statement_verifier/src/host_utils/mod.rs#load_fsv_program`; `symbol:verifier_common/src/fsv_binaries.rs#FsvProgram`; `symbol:tools/gkr_verifier/dump_recursive_verifiers.sh#build_variant`; `symbol:circuit_defs/setups/src/program_setups.rs#find_binary_exit_point`; `symbol:riscv_common/src/lib.rs#EXIT_SEQUENCE`; `region:riscv_common/src/lds/link.x#SECTIONS` |
| `REL-EXEC-002` | provisional | offline preprocessing and `timestamp = 0` | `REL-EXEC-001`; `ASM-EXEC-002..003`; `GAP-EXEC-001` | located | `decision:execution-program-model-2026-09-08`; current ROM, register initialization, and decoder preprocessing | `symbol:circuit_defs/setups/src/lib.rs#pad_bytecode_for_proving`; `symbol:riscv_transpiler/src/vm/ram_with_rom_region.rs#RamWithRomRegion::from_rom_content`; `symbol:riscv_transpiler/src/vm/mod.rs#State::initial_with_counters`; `symbol:cs/src/gkr_circuits/decoder_trait.rs#process_binary_into_separate_tables_ext`; `symbol:cs/src/gkr_circuits/decoder_trait.rs#materialize_flattened_decoder_table_with_bitmask` |
| `REL-EXEC-003` | provisional | timestamps `4` and `4 + 4 · |cycles|` | `REL-EXEC-001..002`; `ASM-EXEC-003`; `GAP-EXEC-002` | located | `decision:execution-program-model-2026-09-08`; current entry and terminal machine boundaries | `symbol:riscv_transpiler/src/vm/mod.rs#State::initial_with_counters`; `symbol:common_constants/src/lib.rs#INITIAL_PC`; `symbol:common_constants/src/timestamps.rs#INITIAL_TIMESTAMP`; `symbol:circuit_defs/setups/src/program_setups.rs#find_binary_exit_point`; `symbol:full_statement_verifier/src/unrolled_proof_statement.rs#verify_full_statement_for_unrolled_circuits`; `symbol:full_statement_verifier/src/unified_circuit_statement.rs#verify_full_statement_for_unified_circuit` |
| `REL-EXEC-004` | provisional | every logical cycle and supplied execution chunk | `ASM-EXEC-001..003`; `REL-EXEC-001..003`; `GAP-EXEC-002`; `GAP-EXEC-005` | located | `decision:execution-program-model-2026-09-08`; four-timestamp cycle clock, circuit trace lengths, chunk construction, and verifier capacity ceiling | `symbol:common_constants/src/timestamps.rs#TIMESTAMP_STEP`; `symbol:program_prover/src/unrolled.rs#make_tracer_buffers`; `symbol:program_prover/src/unified_transition.rs#prove_unified_transition_with_replayer`; `symbol:circuit_defs/unrolled_circuits/unified_reduced_machine/src/lib.rs#UnifiedReducedMachineCircuit`; `symbol:full_statement_verifier/src/lib.rs#MAX_CYCLES` |
| `REL-EXEC-005` | provisional | authenticated nondeterministic CSR cycle | `ASM-EXEC-001`; `REL-EXEC-004`; `GAP-EXEC-006` | located | `decision:execution-program-model-2026-09-08`; [unified add/MOP/CSR relation](../isa/unified/add-sub-mop.md) | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:riscv_transpiler/src/replayer/instructions/add_sub_family/non_determinism.rs#nd_read`; `symbol:cs/src/gkr_circuits/add_sub_family/circuit.rs#add_sub_lui_auipc_mop_circuit_with_preprocessed_bytecode_for_gkr`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/circuit.rs#unified_reduced_machine_circuit_with_preprocessed_bytecode_for_gkr` |
| `REL-EXEC-006` | provisional | recursive profile | `REL-EXEC-001`; `REL-EXEC-005`; `REQ-TOPO-004`; `GAP-TOPO-001`; `GAP-TOPO-003` | prose | [recursion topology](../recursion/topology.md) | — |
| `GAP-EXEC-001` | open | — | affects `ASM-EXEC-002` and `REL-EXEC-001..002`; owner: human | — | same-ELF program-pair, named-source, and accepted setup edge not yet bound end to end | — |
| `GAP-EXEC-002` | open | — | affects `ASM-EXEC-003` and `REL-EXEC-004`; owner: human | — | explicit placement versus implicit global-argument completeness unresolved | — |
| `GAP-EXEC-005` | open | — | affects `REL-EXEC-004`; owner: human | — | reduced-unified chunks contain `2²³` rows but the current full-statement verifier charges `2²⁴` rows per chunk | `symbol:full_statement_verifier/src/unified_circuit_statement.rs#verify_full_statement_for_unified_circuit` |
| `GAP-EXEC-006` | open | — | affects `REL-EXEC-005`; owner: human | — | exact nondeterministic CSR ordering and external binding remain owned but unresolved in the ISA boundary | — |
