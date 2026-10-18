# Column cuts in the unified circuit: 104 → 96 committed base columns

NO MEMORY, LOOKUP OR RANGE-CHECK STATEMENT OF THE UNIFIED CIRCUIT IS WEAKENED, AND EVERY
RELATION THAT A REMOVED HELPER COLUMN ENFORCED IS STILL ENFORCED BY A CONSTRAINT ON THE
RETAINED COLUMNS. EACH OF THE EIGHT REMOVED WITNESS COLUMNS WAS EITHER A VALUE THAT ANOTHER
FAMILY'S SCRATCH SLOT CAN HOLD ON EVERY ROW WHERE IT IS READ, OR A HELPER WHOSE VALUE IS A
LINEAR FUNCTION OF `execute` AND THE DECODER FLAGS. THE DECODER FLAGS STAY BOUND TO THE SETUP
DECODER TABLE BY THE SAME EXECUTE-GATED LOOKUP AS BEFORE.

The unified circuit (`cs/src/gkr_circuits/unified_reduced_machine/`) now commits 38 memory
plus 58 witness base columns instead of 38 plus 66, in both fields. Four edits remove eight
witness columns: three temporaries move into scratch-pool slots that Family 3 already owns,
the family one-hot helper becomes a linear tie on `execute`, the PC-bump helper becomes
`execute` minus the four Family 2 sub-opcode flags, and three Family 2 rd-write helpers become
affine expressions in the decoder flags. The helper columns' defining constraints and
Booleanity checks go with them, which is why the first GKR layer has nine fewer gates; the
relations they enforced are carried by constraints on the retained columns. Nothing else about
the circuit changes: the memory layout, the lookup counts, the scratch width 41, the
generic-lookup setup width 10 and every GKR layer above the first keep their dimensions.

`circuit.rs`, `decoder.rs`, `jump_branch_slt.rs`, `binary_shifts.rs`, `add_sub_lui_auipc_mop.rs`,
`mem_word_only_lw_sw.rs` and `column_cuts_tests.rs` are under
`cs/src/gkr_circuits/unified_reduced_machine/`; other paths are relative to the repository
root.

## 1. What changed

| Quantity | BabyBear 2^23 | Proth120 2^22 |
|---|---|---|
| Memory columns | 38 → 38 | 38 → 38 |
| Witness columns | 66 → 58 | 66 → 58 |
| Committed base columns | 104 → 96 | 104 → 96 |
| First GKR layer gates | 149 → 140 | 150 → 141 |
| First GKR layer inputs | 111 → 103 | 111 → 103 |
| Generic lookups, RC-16 lookups, timestamp lookups | unchanged | unchanged |
| Scratch width, setup width, higher layers | 41, 10, unchanged | 41, 10, unchanged |

The widths and the first layer's gate count are those of the committed layouts
`cs/compiled_circuits/unified_reduced_machine_layout_gkr.json` and
`unified_reduced_machine_layout_gkr_proth120.json` (`memory_layout.total_width`,
`witness_layout.total_width`, `layers[0].gates`), against the same files in the parent commit.

The eight columns, by their names in the previous layout:

| # | Removed column | Family, role | Why it existed | Why it can go | What enforces the statement now |
|---|---|---|---|---|---|
| 1, 2 | `shared F1/F2 intermediate reg[0..1]` | F1 modular-op canonicity residual, F2 saved PC / comparison result, F4 (limb 0) `top_14` of the SW/LW address split | A 16-bit-range-checked u32 temporary shared by three families that never fire on the same row | Family 3's rs1 byte-split slots `shared scratch var[17]`, `[18]` are free on every non-F3 row and are read only under F3 flags; F3's values there are bytes, so the slots' RC-16 holds on F3 rows too | The same register, now `Register(scratch_vars[17], scratch_vars[18])` with an explicit RC-16 on each slot; every F1/F2/F4 reader keeps its family gate (§3.1) |
| 3 | `Intermedaite low for PC computation` | F2 low limb of the next PC before the alignment cleanup, for every F2 sub-op including SLT's sequential `pc + 4` | u16 temporary read only by F2 | F3's shift-output slot `shared scratch var[7]` is free on non-F3 rows and read only under F3 flags | slot 7 with the same RC-16; all F2 readers keep their gates (§3.1) |
| 4 | `unified family-dispatch one-hot` | Boolean `execute · Σ dispatch bits`, enforcing "at most one family per executing row" | Degree-2 trick: a Boolean helper bounds the product | The bound is a linear fact once the helper is dropped | `execute − Σ dispatch bits = 0`, an explicit degree-1 constraint; "exactly one" on executing rows, none on padding (§3.2) |
| 5 | `unified pc-bump gate` | Boolean `execute · (1 − Σ F2 sub-op bits)` gating `pc_out = pc_in + 4` | Keeps the two PC-bump constraints at degree 2 | On admitted rows this value equals the linear `execute − Σ F2 sub-op bits` | gate := `execute − Σ F2 sub-op bits` (`pc_bump_gate`); both PC-bump constraints unchanged otherwise (§3.3) |
| 6 | `is_jal_or_jalr_writes_rd` | F2 gate `(jal + jalr)(1 − rd_is_zero)` | Degree-2 helper | On every decoder row it equals `jal + jalr + branch − rd_is_zero` | that affine gate (`f2_rd_write_gates`) in the unchanged rd-write constraints (§3.4) |
| 7 | `is_slt_writes_rd` | F2 gate `slt · (1 − rd_is_zero)` | Degree-2 helper | SLT never carries `rd_is_zero`, so it equals `slt` | `slt` (§3.4) |
| 8 | `gate_fam2_rd_zero` | F2 gate `(jal + jalr + slt + branch) · rd_is_zero` | Degree-2 helper | `rd_is_zero` only ever comes with an F2 sub-op, so it equals `rd_is_zero` | `rd_is_zero` (§3.4) |

Rows 1–3 are the aliasing edit (−3), row 4 the dispatch tie (−1), row 5 the PC-bump gate
(−1), rows 6–8 the F2 affine identities (−3).

## 2. What the four edits rely on

All four edits are row-local: no changed constraint reads a neighbouring row, so the same
argument applies to the first row, the last row, every executing row of every family, and
every padding row. Three facts about the flags are the shared premise.

1. **Booleanity.** `execute` carries `execute · (execute − 1) = 0`
   (`cs/src/cs/circuit_impl.rs`), and each of the 19 family flags is allocated as a Boolean
   variable.
2. **The decoder lookup binds the flags on executing rows.** The compiled decoder lookup is
   the tuple `(pc[0], pc[1], rs1, rs2, rd, imm[0], imm[1], funct3, Σ 2^i · flag_i)` into the
   `Decoder` table, gated by `execute` (`cs/src/gkr_compiler/family_circuit.rs`). The packed
   sum of 19 Boolean flags is below 2^19 and so below either field's characteristic: on an
   executing row the 19 flags are exactly the mask of one table row. The table rows are
   produced only by `UnifiedReducedMachineDecoder::define_decoder_subspace` through
   `preprocess_bytecode` (`cs/src/gkr_circuits/decoder_trait.rs`), which the setups call.
   Unsupported PCs are materialized as all-`MINUS_ONE` rows and cannot match a range-checked
   PC.
3. **Padding rows have no flags.** `(1 − execute) · Σ (all 19 flags) = 0` is unchanged; with
   Booleanity it zeroes every flag, including `RD_IS_ZERO`, on `execute = 0` rows, where the
   decoder lookup is disabled.

The decoder masks satisfy the facts `unified_decoder_mask_violation` encodes: exactly one
dispatch bit; `RD_IS_ZERO` only together with a Family 2 sub-opcode; `BRANCH` always with
`RD_IS_ZERO`; `SLT`/`SLTU` never with it. These are structural in the Family 2 decoder
(`cs/src/gkr_circuits/jump_branch_slt_family/decoder.rs`: `RD_IS_ZERO` is set only in the
`Jal`/`Jalr` arms when `rd == 0` and unconditionally in `Branch`; `Slt`/`Sltu` assert
`rd != 0`, the transpiler having turned `rd = 0` ALU ops into `Nop`), and the unified decoder
panics at table-build time on any mask that violates them, so a setup cannot be built from a
table that breaks them.

So the only flag assignments a prover can present are a mask that passes
`unified_decoder_mask_violation` on an executing row, or all zeros on padding. These are the
admitted rows; every gate identity below is checked on exactly these.

**Reduction to the previous circuit.** Every witness the new circuit accepts extends to a
witness the previous circuit accepts, with the same memory and public values: copy slots 17,
18 and 7 into the former register and PC-temporary columns, and set each removed helper to its
defining formula. Every former reader of the register or the PC temporary then reads exactly
the value the new circuit's reader of the slot reads, on every row; the RC-16 the former
columns carried holds because the slots are range-checked; the helpers' definitions and
Booleanity hold on admitted rows; and each helper-gated constraint equals the new one because
each new gate equals its helper on admitted rows. Soundness therefore needs only the slot
range checks and the gate identities. That no reader of a slot is active on another family's
rows is what an honest witness needs (completeness), not a soundness premise.

## 3. The four edits

### 3.1 Pool aliasing: three temporaries move into Family 3 scratch slots 17, 18 and 7

The unified circuit shares one scratch pool of 21 variables and 5 Booleans among the four
families; each family's own scratch occupies a prefix of the pool (F1: 2 vars, F2: 5, F3: 21,
F4: 2). Family 3 is the only family that uses slots 7 and 17/18: slot 7 is
`shift_outputs[6]` (contribution chunk 1, byte 2) and slots 17/18 are the rs1 byte-split
points `rs1_b0`, `rs1_b2`. A `const` assertion in `circuit.rs` checks that slot 7 is at or
beyond every other family's scratch count, that 17 > 7, and that 18 is inside the pool.

Owner sets:

| Slot | Family 3 (own scratch) | Other occupants |
|---|---|---|
| 17 | `rs1_b0`, a byte | F1 `intermediate_tmp[0]` (modular residual low limb), F2 `comparison_rel_or_jump_saved_pc_low`, F4 `top_14` |
| 18 | `rs1_b2`, a byte | F1 `intermediate_tmp[1]`, F2 `comparison_rel_or_jump_saved_pc_high` |
| 7 | `shift_outputs[6]`, a byte | F2 `pc_intermediate_addition_tmp_low` |

Every reader of these slots and its gate:

| Slot | Reader | Gate |
|---|---|---|
| 17, 18 | F3 per-byte lookup inputs: `rs1_bytes[i]` and the complementary `(rs1_limb − byte)/256` (`binary_shifts.rs`) | each term multiplied by `is_binary_op` or `is_shift` |
| 17, 18 | F1 modular canonicity `eq_modular_{low,high}` (`add_sub_lui_auipc_mop.rs`) | `· is_modular` |
| 17, 18 | F2 add/compare/saved-PC equations (`jump_branch_slt.rs`) | per sub-op flag |
| 17, 18 | F2 RegIsZero lookup input `saved_pc_low + saved_pc_high` (the table id `is_fam2_sum() · RegIsZero` does not read the slots) | `· is_fam2_sum()` |
| 17, 18 | F2 rd-write constraints | the affine gates of §3.4, zero off F2 |
| 17 | F4 LW/SW address decomposition `4·top_14 + 2·bit_1 + bit_0 = addr_lo` (`mem_word_only_lw_sw.rs`) | `· is_lw`, `· is_sw` |
| 7 | F2 low PC-add equation | per sub-op flag |
| 7 | F2 JumpCleanupOffset lookup input | `· is_fam2_sum()` |
| 7 | F3 per-byte lookup output columns and the high-limb rd-write reconstruction (`binary_shifts.rs`) | `· is_shift`, `· is_binary_op` |
| 17, 18, 7 | RC-16 | unconditional |

On an executing row exactly one family's flags are 1 (§2), so every non-RC reader that is
live belongs to the family whose value occupies the slot; on padding all flags are 0 and no
non-RC reader is live. The RC-16 is the only unconditional reader and it is exactly the range
check the former columns had: `Register::new_named` (`cs/src/types.rs`) allocates both limbs
through `add_variable_with_range_check(16)`, which is the same `RangeCheckQuery` that
`require_invariant(RangeChecked { width: 16 })` pushes; the F2 PC temporary had the same
`require_invariant`. F1's modular canonicity (`2^16·of + out − modulus = intermediate_tmp`
with u16 limbs), F2's saved PC and F4's `4·top_14` alignment therefore keep exactly the range
statement they had, and Family 3's byte occupants satisfy it. Family 3 does not rely on the
RC-16 for byte validity: its byte and shift tables accept only byte inputs, and the
complementary byte `(rs1_limb − byte)/256` is also a table input, so on F3 rows the split of
each rs1 limb is unique, as it was when slots 17/18 had no range check.

The register does not use slots 5/6: F2's RegIsZero peek reads the register and writes slot 0,
and F3's shift-output peeks write slots 1–16 and read slot 0, so the SSA witness scheduler,
which waits for every conditional writer of a variable before any read, would wait on itself.
The rs1 byte-split writers of 17/18 depend only on the rs1 limbs.

### 3.2 The dispatch tie replaces the family one-hot helper

The previous circuit allocated a Boolean `is_any_family_active` with the setup constraint
`is_any_family_active = execute · Σ dispatch bits`; Booleanity of the helper then forced
`Σ dispatch bits ∈ {0, 1}` on executing rows. The dispatch bits are the 18 flags other than
`RD_IS_ZERO` (`dispatch_sum`).

The circuit now asserts the explicit degree-1 constraint

```text
execute − Σ dispatch bits = 0
```

through `add_constraint_expr_allow_explicit_linear_prevent_optimizations_expr`; the compiler
keeps every `AssertZero` statement and places a degree-1 one into the compiled linear
constraints (`cs/src/gkr_compiler/compiled_constraint.rs`).

- Executing rows: exactly one dispatch bit. The previous helper allowed zero or one; the
  decoder lookup already forces one on every executing row (every admitted mask has exactly
  one dispatch bit), so on admitted rows the two agree, and off the table the tie is strictly
  stronger: an executing row with no family bit, which the previous arithmetic accepted and
  only the lookup rejected, now fails arithmetic too.
- Padding: the tie reads `0 = 0`; the padding-zeroing constraint does the work as before, and
  still clears `RD_IS_ZERO`, which the tie does not mention.

### 3.3 The PC-bump gate becomes `execute` minus the Family 2 sub-opcode flags

The two PC-bump constraints are unchanged:

```text
gate · (pc_in[0] + 4 − pc_out[0] − 2^16 · pc_inc_carry) = 0
gate · (pc_inc_carry + pc_in[1] − pc_out[1]) = 0
```

with `pc_inc_carry` Boolean and `pc_out` limbs RC-16 as before. The previous circuit computed
`gate` into a Boolean helper defined by `gate = execute − Σ execute · F2 sub-op bits`. Now

```text
gate := execute − (jal + jalr + slt + branch)        (pc_bump_gate)
```

which is the helper's defining value without the `execute` factor on the F2 flags. The two
agree on every admitted row: there `execute = 1`, or the F2 flags are zero on padding. The
gate is 1 on F1/F3/F4 rows, 0 on F2 rows (Family 2 owns the PC there) and 0 on padding, where
the PC-bump equations impose nothing, as before; the unconditional RC-16 on the `pc_out` limbs
and the memory and boundary obligations on the PC are untouched. The gate is degree 1, so both
constraints stay degree 2. `RD_IS_ZERO` is not subtracted: a branch row has
`execute = branch = RD_IS_ZERO = 1` and needs gate 0.

The sum of the 14 non-F2 dispatch flags is an equivalent gate: the two differ by exactly the
tie residual, `(execute − Σ F2 sub-op bits) − Σ non-F2 dispatch bits = execute − Σ dispatch
bits`, so with the tie asserted they impose the same PC-bump constraints. The 5-term form is
used because each gate term multiplies both PC-bump constraints: with the 14-term gate the
first layer's backward programs grow by about 9 %, with the 5-term gate they end up smaller
than before (§3.5).

### 3.4 The three F2 rd-write gates become affine in the decoder flags

With `J = jal + jalr`, `S = slt`, `B = branch`, `Z = rd_is_zero`:

| Gate | Previous helper | Now |
|---|---|---|
| JAL/JALR writes rd | `J · (1 − Z)` | `J + B − Z` |
| SLT writes rd | `S · (1 − Z)` | `S` |
| rd = x0 | `(J + S + B) · Z` | `Z` |

(`f2_rd_write_gates`.) The five rd-write constraints that consume them are unchanged: low limb
`jj·saved_pc_low + slt·slt_value − (jj + slt)·rd_write[0] = 0`, high limb
`jj·(saved_pc_high − rd_write[1]) = 0`, `slt·rd_write[1] = 0`, and `rd_zero·rd_write[0..1] = 0`.

On admitted rows the two columns agree because of the mask facts of §2:

| Row class | JAL/JALR writes rd | SLT writes rd | rd = x0 |
|---|---:|---:|---:|
| JAL/JALR, rd ≠ x0 | 1 | 0 | 0 |
| JAL/JALR, rd = x0 | 0 | 0 | 1 |
| BRANCH (always `Z`) | 0 | 0 | 1 |
| SLT/SLTU (never `Z`) | 0 | 1 | 0 |
| F1/F3/F4, padding | 0 | 0 | 0 |

The derivation: `Z` is set only on JAL/JALR with `rd = 0` and on BRANCH, so
`J·Z = Z − B` and `J·(1 − Z) = J + B − Z`; `S·Z = 0` gives `S·(1 − Z) = S`; and
`(J+S+B)·Z = Z` because `Z` implies one F2 sub-op.

### 3.5 What each edit costs in the first layer's backward programs

Removing columns does not by itself make the GKR backward pass cheaper: the first layer's
expressions are compiled into an R0 window program and a main-continuation window program,
and the two backward kernels that run them do work that grows with the program length.
Per-edit sizes for the regular BabyBear 2^23 circuit:

| Edit | Witness columns | R0 window words | Base-field records | Main-continuation words | Degree-2 quadratic terms |
|---|---:|---:|---:|---:|---:|
| Pool aliasing (§3.1) | −3 | 0 | 0 | 0 | 0 |
| Dispatch tie (§3.2) | −1 | −8 | −2 | −6 | −19 |
| PC-bump gate as the 14-term non-F2 sum | −1 | +244 | +61 | +183 | +73 |
| PC-bump gate as `pc_bump_gate` (5 terms, §3.3) | −1 | +16 | +4 | +12 | +19 |
| F2 affine gates (§3.4) | −3 | −40 | −10 | −30 | +2 |
| **All four, 5-term gate** | **−8** | **2,232 → 2,200** | **548 → 540** | **1,710 → 1,686** | **382 → 384** |

With the 14-term gate the totals were 2,428 R0 words (597 base-field records) and 1,857
continuation words. GPU profiling of that version showed both layer-0 kernels' instruction
counts and times growing with these word counts at approximately equal cost per word, which
is what motivated the 5-term form.

The sizes come from compiling layer 0 with `gpu_gkr_compiler`'s `compile_r0` and
`lower_main_continuation_window_program` for builds with each edit added alone and removed
from the full set; both directions changed every count by the same amount, so the rows are
additive marginals that sum to the totals. The 5-term row is the difference to the build
without the PC-bump edit.

## 4. Writer width of the shared slots

The SSA → Rust lowering of a masked conditional write is a select against a readback of the
target at the writer's own type (`witness_eval_generator/src/derive_from_ssa/mod.rs`, the
`Expression::U8` and `U16` arms). A u8 or bool writer of slot 17, 18 or 7 would therefore
write another family's u16 limb back truncated on every row where its mask is false. The cs
debug evaluator skips a conditional write whose mask is false
(`cs/src/witness_placer/cs_debug_evaluator.rs`), so single-cycle replays through it cannot see
such a truncation. A truncated limb produces honest proofs that fail verification; it cannot
produce an accepting proof of a false statement, since the prover still commits whatever
values it has and the verifier checks the same constraints.

Rule: every masked writer of a shared slot is at least as wide as every value another family
leaves in that slot. Family 3 writes its byte splits as
`conditionally_assign_u16(slot, is_f3, byte.widen())`; the F1, F2 and F4 writers of slots
17/18/7 are u32/u16, and the F3 shift-output peek writes slot 7 as a field value.

## 5. Verification map

| Claim | Test | Crate | Notes |
|---|---|---|---|
| Widths of §1 | committed layouts; the generated verifiers declare `[38, 58, 10]` columns for the regular circuit and `[96, 10]` for the feeder variant | | regenerated from the circuit, see §6 |
| Decoder masks obey the facts of §2 | the panic in `define_decoder_subspace`; `decoder::tests::invalid_decoded_mask_panics`; the existing decoder tests decode a representative of each accepted opcode through the panic (`decoder_family_dispatch_bits_exclusive` and the per-family tests) | `cs` | fail-closed at table build |
| Each new gate equals its removed helper on every admitted row, and the tie holds there | `column_cuts_tests::column_cut_gates_equal_the_replaced_helpers_on_admitted_rows` | `cs` | the 20 masks that pass `unified_decoder_mask_violation` plus padding, both fields |
| Slots 17, 18, 7 each carry one bare RC-16 lookup; no u8 or bool writer (§4) | `column_cuts_tests::aliased_slots_are_range_checked_and_written_at_least_u16` | `cs` | committed layouts and SSA graphs, both fields |
| Forged flags, padding flags, `RD_IS_ZERO` misuse, rd writes on x0/branch, wrong non-F2 PC, forged carry, slot-7 attacks all rejected | `tests::gkr::unified_negative_tests::column_cuts_negative_cases_rejected`, plus the pre-existing `two_family_bits_on_one_row_rejected`, `empty_family_mask_on_executing_row_rejected`, `unified_f2_pooled_var_binds_on_slt_row_rejected`, `unified_top14_pooled_corruption_on_sw_row_rejected`, `unified_mulmod_intermediate_forge_rejected` | `prover` | one honest trace, each case attributed to the named constraint |
| The PC-bump carry at the 0xFFFC boundary | `tests::single_cycle_tests::unified_circuit_tests::pc_carry_boundary_tests::pc_bump_carry_boundary_rejects_forgeries` | `prover` | honest carry, dropped carry, unchanged high limb; both fields |
| Generated witness code is satisfying on real traces (§4) | `tests::gkr::unified_generated_witness::generated_witness_satisfies_{regular_layout,proth120_wrap_layout}` | `prover` | also asserts a non-F3 row with a register limb above 0xFF in slot 17 |
| Committed CUDA witness source and forward schedule follow the new layout | `gpu_witness_eval_generator` `tests::{committed_witness_cuh_is_current, every_committed_cuh_is_listed}`; `gpu_gkr_compiler` `every_retained_forward_artifact_validates_compiles_and_encodes` (`tests/forward_corpus.rs`) | GPU crates | currentness guards, no GPU needed; they do not establish GPU execution parity |
| BabyBear proof generation and native verification | `prover::tests::gkr::unified_circuit::gkr_run_unified_test_sec_100`; `verifier::native::unified_reduced_machine_sec_100` | `prover`, `verifier` | Set `GKR_BLAKE=compression` for the smoke fixture. The producer regenerates the unified CPU proof; the `native` integration target verifies the committed proof with the generated verifier. |
| Full-statement verification of the BabyBear fixture | `full_statement_verifier::unified::{unified_base_layer_accepts_valid_proof, unified_base_layer_rejects_corrupted_stream, rejects_corrupted_setup_cap, rejects_tampered_final_register_state, rejects_num_it_circuits_zero, rejects_num_it_circuits_exceeds_num_circuits, rejects_duplicated_multi_instance, unified_base_layer_transpiler_accepts_valid_proof}` | `full_statement_verifier` | Eight tests in integration target `unified`, all `#[ignore]`; the transpiler test also requires the optional base-layer verifier binary. |
| Proth120 2^22 packed proof and calldata consistency | `prover::tests::gkr::large_field::gkr_unified_packed_commitment_basic_fibonacci`; `verifier_evm::flatten_roundtrip::flatten_and_seed_match_reference` | `prover`, `verifier_evm` | The ignored producer proves `circuit_tester` despite its name. This smoke fixture is not full-chain L1 parity coverage. |
| Merged EVM verifier acceptance and rejection | `GkrWhirMergedTest::{test_merged_single_tx, test_production_verifier_rejects_other_program, test_noncanonical_dim_reduce_lane_rejected, test_zero_registry_rejected, test_codeless_registry_rejected, test_refusing_registry_fails_verification}` | `verifier_evm` Foundry suite | `generated_contracts/merged/test/GkrWhirMerged.t.sol`. The fixture contract binds the saved proof's program; the production contract retains the feeder binding. |

For integration tests, `crate::target::test` names the crate, Cargo test target and test.
The regenerated verifier binaries were reproduced using the pinned Docker build in
[`tools/reproduce`](../tools/reproduce/README.md): all 57 tracked artifacts matched
byte-for-byte. Nine artifacts changed relative to the parent commit: the three unified FSV
variants, each with `.bin`, `.elf` and `.text` outputs.

Coverage limits:

- The generated-witness tests check arithmetic, the two range-check families and decoder
  membership. They do not check membership of the other generic lookups (Family 3's byte
  and shift tables, RegIsZero, JumpCleanupOffset, and the rest). A corruption of slot 17 or
  18 on an F3 row that keeps arithmetic and RC-16 satisfied is rejected only by the real
  lookup argument. The native round trip enforces that argument on the honest program it
  proves; no adversarial round trip with such an injected corruption was run.
- No test checks that a reader of slot 17, 18 or 7 is inactive on other families' rows. §2
  needs that only for completeness; the generated-witness tests and the proof round trips
  exercise it on real programs.
- The writer-width rule is checked for slots 17, 18 and 7 only.

On the regular 2^23 GPU path, a same-device comparison of trunk against this change over 10
Ethereum blocks (two processes per side over the same blocks, interleaved, warmup excluded)
measured mean per-block proving times of 4,774.6 and 4,761.9 ms. The paired per-block
difference is −12.7 ms mean and −12.0 ms median (range −35.0 to +12.0 ms). It sits in the
recursion layers that use the unified circuit (bridge −7.5 ms, recursion rounds −5.5 ms);
the base layer, which does not use the unified circuit, changed by +0.4 ms. Profiles of one
block's seven regular unified proofs attribute −11.8 ms to witness generation plus
commitment and −2.5 ms to the first layer's backward kernels. This is one session on one
device, not an equivalence bound. The regular GKR verifier-input stream shrinks from 329,072
to 323,248 bytes (−1.77 %), and recursion verifier cycles fall by about 0.7–0.8 % across the
two observed proof classes. L1 feeder/wrap GPU measurements are pending.

## 6. Re-deriving the artifacts

Release builds; `RUST_MIN_STACK=1073741824`:

```sh
# the four layouts and the two SSA graphs
cargo test -p cs --release --lib -- --exact \
  gkr_circuits::unified_reduced_machine::circuit::test::compile_unified_reduced_machine_into_gkr \
  gkr_circuits::unified_reduced_machine::circuit::test::compile_unified_reduced_machine_into_no_caches_gkr \
  gkr_circuits::unified_reduced_machine::circuit::test::compile_unified_reduced_machine_gkr_witness_graph \
  gkr_circuits::unified_reduced_machine::circuit::test::compile_unified_reduced_machine_into_gkr_large_field \
  gkr_circuits::unified_reduced_machine::circuit::test::compile_unified_reduced_machine_gkr_witness_graph_large_field \
  --test-threads=1
# generated Rust witness functions, circuit-crate artifacts, CUDA witness, forward schedule, verifiers
cargo test -p witness_eval_generator --release --lib -- --exact derive_from_ssa::test::gen_for_gkr derive_from_ssa::test::gen_for_large_field --test-threads=1
cargo test -p unified_reduced_machine --release --lib test::generate -- --exact
cargo run --release -p gpu_witness_eval_generator --bin generate -- cs/compiled_circuits/unified_reduced_machine_layout_gkr.json cs/compiled_circuits/unified_reduced_machine_ssa_gkr.json circuit_defs/unrolled_circuits/unified_reduced_machine/generated/witness_generation_fn.cuh
cargo run --release -p gpu_gkr_compiler --features search --bin gkr-forward-artifact -- --if-stale --circuit unified_reduced_machine --layout cs/compiled_circuits/unified_reduced_machine_layout_gkr.json --output cs/compiled_circuits/unified_reduced_machine_schedule_b4_gkr.json --seed 42 --cache-buckets 4 --population 64 --evaluations 1024
cargo test -p verifier_generator --no-default-features --test generate_verifiers -- --exact unified_reduced_machine unified_reduced_machine_l1_feeder --test-threads=1
# the column-cut checks
cargo test -p cs --release --lib column_cuts
cargo test -p cs --release --lib unified_reduced_machine::decoder::tests
cargo test -p prover --release --lib column_cuts_negative_cases_rejected
cargo test -p prover --release --lib pc_bump_carry_boundary_rejects_forgeries
cargo test -p prover --release --lib unified_generated_witness
```

The committed layouts must show `memory_layout.total_width = 38` and
`witness_layout.total_width = 58`; the generated verifiers declare `[38, 58, 10]` columns for
the regular circuit and `[96, 10]` for the feeder variant.
