# MEM: Shared ROM and RAM state

> Defines byte-addressed program ROM, mutable RAM, and the RAM-history interface.
> Register and PC state, instruction-specific value transformations, and the proof
> protocol that verifies the permutation product are outside this module.

## Inputs and notation

| Name | Meaning |
|---|---|
| `P[0..L)` | raw program image as `L` little-endian 32-bit words, `L <= 2^20` |
| `profile` | `unrolled` or `unified-reduced` |
| `Q` | RAM-tagged read/write records emitted by all active execution rows |
| `a` | 32-bit architectural byte address |
| `w` | word base `a - (a mod 4)` |

Let `ROM_LIMIT = 2^22`. A word is represented by two 16-bit limbs and denotes the
corresponding value in `[0, 2^32)`. Byte `i` of a word is bits `8i..8i+7`, so byte
offset zero is the least-significant byte.

For a RAM record

`q = (w, t_read, value_read, t_write, value_write)`,

define the tagged tuples

```text
read(q)  = (RAM, w, t_read,  value_read)
write(q) = (RAM, w, t_write, value_write).
```

The timestamps order versions of a word; they are not architectural memory contents.

## Assumptions

- **ASM-MEM-001 — Program binding.** `P` is the raw program image bound by the selected setup and proof statement.
- **ASM-MEM-002 — Local access binding.** Each ISA relation supplies the effective address, access width, read/write choice, local timestamp, and any subword replacement or extension used by its emitted record.
- **ASM-MEM-003 — Permutation binding.** The proof topology binds every participating circuit's RAM-tagged read and write tuples to the same challenges and checks their aggregate products for equality.

## Canonical relation tree

> Interpret the tree under `ASM-MEM-001..003`. The leaf IDs name the canonical
> statements below; the global closure requirement applies to all emitted records.

- **Load was canonicalized to `NOP`.** [`REQ-MEM-006`]; if a RAM record is
  retained, [`REQ-MEM-003`], [`REQ-MEM-004`], and [`REQ-MEM-005`] also
  apply.
- **An architectural memory access remains.**
  - **`w < ROM_LIMIT`.**
    - **Load.** [`REQ-MEM-001`], [`REQ-MEM-002`], [`REQ-MEM-003`],
      [`REQ-MEM-004`], [`REQ-MEM-005`]
    - **Store.** Unsatisfiable under [`REQ-MEM-002`].
  - **`w >= ROM_LIMIT`.**
    - **Load or store.** [`REQ-MEM-002`], [`REQ-MEM-003`],
      [`REQ-MEM-004`], [`REQ-MEM-005`]

## Requirements

### REQ-MEM-001 — Fixed program ROM

For every word-aligned `w < ROM_LIMIT`, the authenticated ROM word is

```text
ROM[w] = P[w / 4],  when w / 4 < L;
ROM[w] = 0,         otherwise.
```

ROM byte and halfword reads select the corresponding little-endian part of this word.

### REQ-MEM-002 — ROM/RAM region selection

A load takes its source word from `ROM[w]` when `w < ROM_LIMIT`, and from the
current `RAM[w]` when `w >= ROM_LIMIT`. A store requires `w >= ROM_LIMIT` and
assigns the family-computed next word to `RAM[w]`; therefore no store changes ROM.

For a ROM load, ROM content is authenticated only by `REQ-MEM-001`. Any RAM-tagged
slot retained for a fixed-shape circuit is read-only (`value_write = value_read`) and
does not authenticate or alter the ROM value.

### REQ-MEM-003 — Profile address domain and alignment

| Profile | Initialized/finalized word-address set `A_profile` | Alignment enforcement |
|---|---|---|
| `unrolled` | `{ 4i | 0 <= i < 2^28 }`, covering the low `2^30` bytes | ROM word loads are aligned by the ROM table. Subword rows use `w`; halfword rows additionally require `a mod 2 = 0`. A mutable-RAM word access is word-aligned through membership in `A_profile` and global closure, although the standalone word-family circuit does not repeat that local check. |
| `unified-reduced` | the union of verifier-bound, pairwise-disjoint init/teardown windows; every admitted address is a multiple of four | The unified word family locally requires `a mod 4 = 0`. This profile contains no subword-memory family. |

These are normative facts for the selected profiles, not alternative architectural
meanings of a word access.

### REQ-MEM-004 — Ordered RAM versions

Every `q in Q` has `w in A_profile`, 32-bit read and write values, and
`t_read < t_write`. Its read tuple names the version consumed by the access and its
write tuple names the next version. A read-only access has
`value_write = value_read`; a store's `value_write` is the next word supplied under
`ASM-MEM-002`.

### REQ-MEM-005 — Initialization and final closure

For every `w in A_profile`, the RAM-argument shadow state begins with value `0` at
timestamp `0`. Architectural mutable RAM is the subset `w >= ROM_LIMIT`; the low
region exists in this argument only for state-preserving ROM-shaped contributions. Let
`final(w) = (RAM, w, t_final(w), value_final(w))` be its terminal version, including
`(RAM, w, 0, 0)` when it is never accessed. The checked multiset relation is

```text
{ (RAM, w, 0, 0) | w in A_profile } + { write(q) | q in Q }
  =
{ read(q) | q in Q } + { final(w) | w in A_profile }.
```

Together with `REQ-MEM-004`, this makes every admitted RAM history a chain from its
zero initialization to exactly one terminal version.

### REQ-MEM-006 — No device effects for discarded loads

The machine models program ROM and ordinary mutable RAM, not hardware/MMIO effects or
an architectural exception handler. A supported load canonicalized to `NOP` because
`rd = x0` has no architectural memory-state effect. Its proof representation may be
the memory-product identity (no RAM tuple) or a read-only RAM tuple; neither changes a
memory value.

## Derived facts

- **ROM padding**
  `w / 4 >= L && w < ROM_LIMIT => ROM[w] = 0`
- **ROM immutability**
  `ROM` unchanged
- **RAM initialization**
  `initial(w) = (RAM, w, 0, 0)`
- **RAM chronology**
  `q in Q => t_read < t_write`
- **Read-only contribution**
  `value_write = value_read`
- **Discarded load**
  `rd = x0 => no architectural memory-state change`
- **Unrolled word alignment**
  `profile = unrolled && word access => w mod 4 = 0`

## Metadata

The shared memory relation is normative for the selected profiles. It combines the
project decisions on emulated-memory effects and alignment with matching ROM tables,
family constraints, RAM chronology, initialization/teardown construction, and
full-statement closure.

- spec revision: TBD
- implementation: TBD
- profile: unrolled full/unsigned machine and unified reduced machine

| ID | Authority | Activation | Depends / discharged by | Binding | Source | Anchor / check |
|---|---|---|---|---|---|---|
| `ASM-MEM-001` | normative | always | `external:proof statement` | located | program-specific ROM tables and setup construction at `dfb1b2a8a` | `symbol:cs/src/tables/rom_related.rs#create_table_for_word_aligned_rom_image`; `symbol:circuit_defs/setups/src/program_setups.rs#compute_unrolled_program_setups`; `symbol:circuit_defs/setups/src/program_setups.rs#compute_unified_program_setups` |
| `ASM-MEM-002` | normative | emitted memory record | `external:UPROF`; `external:UNIFIED` | located | unrolled and unified memory-family relations at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/mem_word_only/circuit.rs#apply_mem_word_only_inner`; `symbol:cs/src/gkr_circuits/mem_subword_only/circuit.rs#apply_mem_subword_only_inner`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/mem_word_only_lw_sw.rs#apply_unified_mem_word_only_lw_sw_data_path` |
| `ASM-MEM-003` | normative | proof acceptance | `external:proof topology` | located | aggregate read/write products at `dfb1b2a8a` | `symbol:full_statement_verifier/src/unrolled_proof_statement.rs#verify_full_statement_for_unrolled_circuits`; `symbol:full_statement_verifier/src/unified_circuit_statement.rs#verify_full_statement_for_unified_circuit` |
| `REQ-MEM-001` | normative | `w < 2^22` ROM read | `ASM-MEM-001` | located | `repo:common_constants/src/rom.rs#ROM_BYTE_SIZE_LOG2@dfb1b2a8a`; `repo:cs/src/tables/rom_related.rs#ROM_PADDING_OPCODE@dfb1b2a8a`; ROM tables | `symbol:common_constants/src/rom.rs#ROM_BYTE_SIZE_LOG2`; `symbol:cs/src/tables/rom_related.rs#ROM_PADDING_OPCODE`; `symbol:cs/src/tables/rom_related.rs#create_table_for_word_aligned_rom_image`; `symbol:cs/src/tables/rom_related.rs#create_load_halfword_from_rom_table`; `symbol:cs/src/tables/rom_related.rs#create_load_byte_from_rom_table` |
| `REQ-MEM-002` | normative | load or store | `ASM-MEM-001`, `ASM-MEM-002` | located | memory-family region selection and ROM-store constraints at `dfb1b2a8a` | `symbol:cs/src/gkr_circuits/mem_word_only/circuit.rs#apply_mem_word_only_inner`; `symbol:cs/src/gkr_circuits/mem_subword_only/circuit.rs#apply_mem_subword_only_inner`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/mem_word_only_lw_sw.rs#apply_unified_mem_word_only_lw_sw_data_path`; `symbol:riscv_transpiler/src/vm/ram_with_rom_region.rs#RamWithRomRegion::write_word` |
| `REQ-MEM-003` | normative | selected profile | `ASM-MEM-003` | located | unrolled and unified init/teardown address domains and local alignment constraints at `dfb1b2a8a` | `symbol:circuit_defs/unrolled_circuits/inits_and_teardowns/src/lib.rs#NUM_INIT_AND_TEARDOWN_SETS`; `symbol:circuit_defs/unrolled_circuits/inits_and_teardowns/src/lib.rs#TRACE_LEN_LOG2`; `symbol:circuit_defs/unrolled_circuits/inits_and_teardowns/src/lib.rs#WORD_BITS`; `symbol:prover/src/gkr/virtual_polys/init_and_teardown_base.rs#materialize_virtual_inits_and_teardowns_base_address_setup_poly`; `symbol:cs/src/gkr_circuits/unified_reduced_machine/mem_word_only_lw_sw.rs#apply_unified_mem_word_only_lw_sw_data_path`; `symbol:full_statement_verifier/src/unified_circuit_statement.rs#verify_full_statement_for_unified_circuit` |
| `REQ-MEM-004` | normative | every `q in Q` | `ASM-MEM-002`, `ASM-MEM-003`, `REQ-MEM-003` | located | RAM tuple construction and timestamp comparison at `dfb1b2a8a` | `symbol:cs/src/gkr_compiler/memory_like_grand_product.rs#layout_initial_grand_product_accumulation`; `symbol:cs/src/gkr_compiler/range_check_exprs.rs#compile_timestamp_comparison_range_checks`; `symbol:cs/src/cs/circuit_trait.rs#MemoryAccess::is_readonly` |
| `REQ-MEM-005` | normative | proof acceptance | `ASM-MEM-003`, `REQ-MEM-003`, `REQ-MEM-004` | located | zero init, teardown, and final product equality at `dfb1b2a8a` | `symbol:cs/src/gkr_compiler/inits_and_teardowns.rs#compile_inits_and_teardowns_circuit`; `symbol:prover/src/gkr/prover/forward_loop/inits_and_teardowns.rs#evaluate_init`; `symbol:prover/src/gkr/prover/forward_loop/inits_and_teardowns.rs#evaluate_teardown`; `symbol:full_statement_verifier/src/unrolled_proof_statement.rs#verify_full_statement_for_unrolled_circuits`; `symbol:full_statement_verifier/src/unified_circuit_statement.rs#verify_full_statement_for_unified_circuit` |
| `REQ-MEM-006` | normative | load decoded with `rd = x0` | `external:DEC`, `ASM-MEM-002` | located | `decision:emulated-memory-has-no-device-side-effects`; current canonicalization at `dfb1b2a8a` | `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#Instruction::pure_from_imm`; `symbol:riscv_transpiler/src/ir/simple_instruction_set.rs#preprocess_bytecode`; `symbol:cs/src/cs/circuit_trait.rs#MemoryAccess::is_readonly` |
