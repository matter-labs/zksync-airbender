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
the family one-hot helper becomes a linear tie on `execute`, the PC-bump helper becomes a sum
of dispatch flags, and three Family 2 rd-write helpers become affine expressions in the
decoder flags. The helper columns' defining constraints and Booleanity checks go with them,
which is why the first GKR layer has nine fewer gates; the relations they enforced are
carried by constraints on the retained columns. Nothing else about the circuit changes: the
memory layout, the lookup counts, the scratch width 41, the generic-lookup setup width 10 and
every GKR layer above the first keep their dimensions. This document says what each removed column was, why it could go, what
now enforces the statement it carried, on which rows, and how that is tested.

Paths are relative to the repository root; `circuit.rs`, `decoder.rs`, `jump_branch_slt.rs`,
`binary_shifts.rs`, `add_sub_lui_auipc_mop.rs`, `mem_word_only_lw_sw.rs`,
`column_cuts_tests.rs` and `liveness.rs` are under `cs/src/gkr_circuits/unified_reduced_machine/`.
The previous circuit is kept as `UnifiedCircuitProfile::Baseline` for differential tests
only; both fields use the shared production `REGULAR_UNIFIED_PROFILE = ColumnCuts`
(`circuit.rs:69-82`) and there is no production opt-in.

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

Source: `prover` test `tests::gkr::unified_column_profile::unified_profile_width_vectors`,
which compiles both profiles in both fields, asserts the memory, witness and setup widths and
the equality of the generic-lookup, RC-16 and timestamp-lookup counts, and prints the scratch
width and the per-layer dimensions. The scratch and layer rows above are read from its output:
`regular 2^23 cuts: memory=38 witness=58 setup=10 scratch=41 layers=[(140, 0, 16, None, 103), ...]`
and `proth120 2^22 cuts: ... layers=[(141, 0, 16, None, 103), ...]`, each tuple being gates,
gates with external connections, cached relations, intermediate width and inputs of a layer;
the baseline lines print 149/150 gates and 111 inputs with the same remaining entries.

The eight columns, by the `Baseline` variable names that disappear from the compiled layout:

| # | Removed column (Baseline name) | Family, role | Why it existed | Why it can go | What enforces the statement now |
|---|---|---|---|---|---|
| 1, 2 | `shared F1/F2 intermediate reg[0..1]` | F1 modular-op canonicity residual, F2 saved PC / comparison result, F4 (limb 0) `top_14` of the SW/LW address split | A 16-bit-range-checked u32 temporary shared by three families that never fire on the same row | Family 3's rs1 byte-split slots `shared scratch var[17]`, `[18]` are free on every non-F3 row and are read only under F3 flags; F3's values there are bytes, so the slots' RC-16 holds on F3 rows too | The same register, now `Register(scratch_vars[17], scratch_vars[18])` with an explicit RC-16 on each slot (`circuit.rs:395-407`); every F1/F2/F4 reader keeps its family gate (§3.1) |
| 3 | `Intermedaite low for PC computation` | F2 low limb of the next PC before the alignment cleanup, for every F2 sub-op including SLT's sequential `pc + 4` | u16 temporary read only by F2 | F3's shift-output slot `shared scratch var[7]` is free on non-F3 rows and read only under F3 flags | `pc_tmp_slot = scratch_vars[7]` with the same RC-16 (`jump_branch_slt.rs:100-109`); all F2 readers keep their gates (§3.1) |
| 4 | `unified family-dispatch one-hot` | Boolean `execute · Σ dispatch bits`, enforcing "at most one family per executing row" | Degree-2 trick: a Boolean helper bounds the product | The bound is a linear fact once the helper is dropped | `execute − Σ dispatch bits = 0`, explicit degree-1 constraint (`circuit.rs:691-695`); "exactly one" on executing rows, none on padding (§3.2) |
| 5 | `unified pc-bump gate` | Boolean `execute · (1 − Σ F2 sub-op bits)` gating `pc_out = pc_in + 4` | Keeps the two PC-bump constraints at degree 2 | Under the tie, this value equals the sum of the non-F2 dispatch bits, which is linear | gate := `Σ (F1 + F3 + F4 dispatch bits)` (`circuit.rs:607`, `non_f2_dispatch_sum` at `:480`); both PC-bump constraints unchanged otherwise (§3.3) |
| 6 | `is_jal_or_jalr_writes_rd` | F2 gate `(jal + jalr)(1 − rd_is_zero)` | Degree-2 helper | On every decoder row it equals `jal + jalr + branch − rd_is_zero` | that affine gate (`jump_branch_slt.rs:1090-1102`) in the unchanged rd-write constraints (§3.4) |
| 7 | `is_slt_writes_rd` | F2 gate `slt · (1 − rd_is_zero)` | Degree-2 helper | SLT never carries `rd_is_zero`, so it equals `slt` | `slt` (§3.4) |
| 8 | `gate_fam2_rd_zero` | F2 gate `(jal + jalr + slt + branch) · rd_is_zero` | Degree-2 helper | `rd_is_zero` only ever comes with an F2 sub-op, so it equals `rd_is_zero` | `rd_is_zero` (§3.4) |

Rows 1–3 are the aliasing edit (−3), row 4 the dispatch tie (−1), row 5 the PC-bump gate
(−1), rows 6–8 the F2 affine identities (−3).

## 2. What the four edits rely on

All four edits are row-local: no changed constraint reads a neighbouring row, so the same
argument applies to the first row, the last row, every executing row of every family, and
every padding row. Three facts about the flags are the shared premise.

1. **Booleanity.** `execute` carries `execute · (execute − 1) = 0` (`cs/src/cs/circuit_impl.rs:1400-1402`),
   and each of the 19 family flags is allocated as a Boolean variable (`circuit_impl.rs:1448-1456`).
2. **The decoder lookup binds the flags on executing rows.** The compiled decoder lookup is
   the tuple `(pc[0], pc[1], rs1, rs2, rd, imm[0], imm[1], funct3, Σ 2^i · flag_i)` into the
   `Decoder` table, gated by `execute` (`cs/src/gkr_compiler/family_circuit.rs:113-158`). The
   packed sum of 19 Boolean flags is below 2^19 and so below either field's characteristic:
   on an executing row the 19 flags are exactly the mask of one table row. The table rows are
   produced only by `UnifiedReducedMachineDecoder::define_decoder_subspace`
   (`decoder.rs:147-153`; `preprocess_bytecode` at `cs/src/gkr_circuits/decoder_trait.rs:282-310`
   is the one builder, and the setups call it: `circuit_defs/setups/src/unrolled_circuits/unifier_reduced_machine_circuit/mod.rs`,
   `unified_decoder_table`). Unsupported PCs are materialized as all-`MINUS_ONE` rows
   (`decoder_trait.rs:264-274`) and cannot match a range-checked PC.
3. **Padding rows have no flags.** `(1 − execute) · Σ (all 19 flags) = 0` is unchanged
   (`circuit.rs:698-720`); with Booleanity it zeroes every flag, including `RD_IS_ZERO`, on
   `execute = 0` rows, where the decoder lookup is disabled.

So the only flag assignments a prover can present are a validated decoder-table mask on an
executing row, or all zeros on padding. Every equivalence below is checked on exactly those
row classes.

The decoder masks satisfy, by construction, the facts `unified_decoder_mask_violation`
(`decoder.rs:35-54`) encodes: exactly one dispatch bit; `RD_IS_ZERO` only together with a
Family 2 sub-opcode; `BRANCH` always with `RD_IS_ZERO`; `SLT`/`SLTU` never with it. These are
structural in the Family 2 decoder (`cs/src/gkr_circuits/jump_branch_slt_family/decoder.rs:74-135`:
`RD_IS_ZERO` is set only in the `Jal`/`Jalr` arms when `rd == 0` and unconditionally in
`Branch`; `Slt`/`Sltu` assert `rd != 0`, the transpiler having turned `rd = 0` ALU ops into
`Nop`), and the unified decoder panics at table-build time on any mask that violates them
(`decoder.rs:157-163`), so a setup cannot be built from a table that breaks them.

## 3. The four edits

### 3.1 Pool aliasing: three temporaries move into Family 3 scratch slots 17, 18 and 7

The unified circuit shares one scratch pool of 21 variables and 5 Booleans among the four
families; each family's own scratch occupies a prefix of the pool (F1: 2 vars, F2: 5, F3: 21,
F4: 2; `circuit.rs:108-111`). Family 3 is the only family that uses slots 7 and 17/18:
slot 7 is `shift_outputs[6]` (contribution chunk 1, byte 2) and slots 17/18 are the rs1
byte-split points `rs1_b0`, `rs1_b2` (`binary_shifts.rs:58-67`). The constants at
`circuit.rs:126-127` put 17 and 18 beyond 7, and the `const` assertion at `:128-132` checks
that slot 7 is at or beyond every other family's scratch count, that 17 > 7, and that 18 is
inside the pool.

Owner sets after the edit:

| Slot | Family 3 (own scratch) | Other occupants |
|---|---|---|
| 17 | `rs1_b0`, a byte | F1 `intermediate_tmp[0]` (modular residual low limb), F2 `comparison_rel_or_jump_saved_pc_low`, F4 `top_14` |
| 18 | `rs1_b2`, a byte | F1 `intermediate_tmp[1]`, F2 `comparison_rel_or_jump_saved_pc_high` |
| 7 | `shift_outputs[6]`, a byte | F2 `pc_intermediate_addition_tmp_low` |

Every reader of these slots and its gate (standalone tree; the same list is produced
mechanically on the compiled layouts by `liveness.rs`, see §5):

| Slot | Reader | Gate |
|---|---|---|
| 17, 18 | F3 per-byte lookup inputs: `rs1_bytes[i]` and the complementary `(rs1_limb − byte)/256` (`binary_shifts.rs:68-82, 216-262`) | each term multiplied by `is_binary_op` or `is_shift` |
| 17, 18 | F1 modular canonicity `eq_modular_{low,high}` (`add_sub_lui_auipc_mop.rs:691, 745`) | `· is_modular` |
| 17, 18 | F2 add/compare/saved-PC equations (`jump_branch_slt.rs:309-328, 370-385`) | per sub-op flag |
| 17, 18 | F2 RegIsZero lookup input `saved_pc_low + saved_pc_high` (`jump_branch_slt.rs:408-424`; the table id `is_fam2_sum() · RegIsZero` does not read the slots) | `· is_fam2_sum()` |
| 17, 18 | F2 rd-write constraints (`jump_branch_slt.rs:1051-1060`) | the affine gates of §3.4, zero off F2 |
| 17 | F4 LW/SW address decomposition `4·top_14 + 2·bit_1 + bit_0 = addr_lo` (`mem_word_only_lw_sw.rs:438-450`) | `· is_lw`, `· is_sw` |
| 7 | F2 low PC-add equation (`jump_branch_slt.rs:766-772`) | per sub-op flag |
| 7 | F2 JumpCleanupOffset lookup input (`jump_branch_slt.rs:886-895`) | `· is_fam2_sum()` |
| 7 | F3 per-byte lookup output columns and the high-limb rd-write reconstruction (`binary_shifts.rs:253-262, 345-376`) | `· is_shift`, `· is_binary_op` |
| 17, 18, 7 | RC-16 (`circuit.rs:397-403`; `jump_branch_slt.rs:106-109`) | unconditional |

On an executing row exactly one family's flags are 1 (§2), so every non-RC reader that is
live belongs to the family whose value occupies the slot; on padding all flags are 0 and no
non-RC reader is live. The RC-16 is the only unconditional reader and it is exactly the range
check the `Baseline` columns had: `Register::new_named` (`cs/src/types.rs:480-486`) allocates both limbs through
`add_variable_with_range_check(16)` (`cs/src/cs/circuit_trait.rs:240-248`), which is the
same `RangeCheckQuery` that `require_invariant(RangeChecked { width: 16 })` pushes
(`circuit_impl.rs:1308-1324`); the F2 PC temporary had the same `require_invariant`. F1's
modular canonicity (`2^16·of + out − modulus = intermediate_tmp` with u16 limbs), F2's saved
PC and F4's `4·top_14` alignment therefore keep exactly the range statement they had, and
Family 3's byte occupants satisfy it. Family 3 does not rely on the RC-16 for byte validity:
its byte and shift tables accept only byte inputs, and the complementary byte
`(rs1_limb − byte)/256` is also a table input, so on F3 rows the split of each rs1 limb is
unique; this was already the case in `Baseline`, where slots 17/18 had no range check at all.

A satisfying `ColumnCuts` witness extends to a satisfying `Baseline` witness: copy each of
the three pooled values into its former column; every former reader sees the same value on
its live rows, and the RC-16 on the former columns is implied by the RC-16 on the slots.

Why slots 5/6, the design's first choice, were not used: not a constraint matter. The SSA
witness scheduler waits for every conditional writer of a variable before any read. F2's
RegIsZero peek reads the shared register and writes slot 0; F3's shift-output peeks write
slots 1–16 and read slot 0 (the truncated shift amount). With the register in 5/6 the
scheduler waits on itself ("Graph resolver is stuck"). The rs1 byte-split writers of 17/18
depend only on the rs1 limbs, so there is no cycle (`circuit.rs:119-125`).

### 3.2 The dispatch tie replaces the family one-hot helper

`Baseline` allocated a Boolean `is_any_family_active` with the setup constraint
`is_any_family_active = execute · Σ dispatch bits`; Booleanity of the helper then forced
`Σ dispatch bits ∈ {0, 1}` on executing rows. The dispatch bits are the 18 flags other than
`RD_IS_ZERO` (`dispatch_sum`, `circuit.rs:495-507`).

`ColumnCuts` asserts the explicit degree-1 constraint

```text
execute − Σ dispatch bits = 0        (circuit.rs:691-695)
```

through `add_constraint_expr_allow_explicit_linear_prevent_optimizations_expr`; the compiler
keeps every `AssertZero` statement and places a degree-1 one into the compiled linear
constraints (`cs/src/gkr_compiler/compiled_constraint.rs:150-175`).

- Executing rows: exactly one dispatch bit. `Baseline` allowed zero or one; the decoder
  lookup already forces one on every executing row (every table mask has exactly one
  dispatch bit), so on admitted rows the two agree, and off the table the tie is strictly
  stronger: an executing row with no family bit, which `Baseline` arithmetic accepted and only
  the lookup rejected, now fails arithmetic too.
- Padding: the tie reads `0 = 0`; the padding-zeroing constraint does the work as before, and
  still clears `RD_IS_ZERO`, which the tie does not mention.

`column_cuts_tests.rs::dispatch_tie_strengthens_one_hot_exhaustively` checks this over all
2^20 Boolean `(execute, mask)` assignments: the set the tie admits (with padding zeroing) is a
subset of the set the `Baseline` helper admitted, and the difference is exactly the two
assignments `execute = 1` with mask 0 or `RD_IS_ZERO` alone, neither of which is a decoder
row.

### 3.3 The PC-bump gate becomes the sum of the non-F2 dispatch bits

The two PC-bump constraints are unchanged:

```text
gate · (pc_in[0] + 4 − pc_out[0] − 2^16 · pc_inc_carry) = 0
gate · (pc_inc_carry + pc_in[1] − pc_out[1]) = 0          (circuit.rs:615-624)
```

with `pc_inc_carry` Boolean and `pc_out` limbs RC-16 as before (`circuit.rs:526-556`).
`Baseline` computed `gate` into a Boolean helper defined by
`gate = execute − Σ execute · F2 sub-op bits`. `ColumnCuts` uses
`gate := Σ (F1 + F3 + F4 dispatch bits)` (`circuit.rs:607`, `non_f2_dispatch_sum`). Under the
tie, `Σ non-F2 = execute − Σ F2 sub-ops`, which is the helper's defining value on every
admitted row: 1 on F1/F3/F4 rows, 0 on F2 rows (Family 2 owns the PC there) and 0 on padding,
where the PC-bump equations impose nothing, as before; the unconditional RC-16 on the
`pc_out` limbs and the memory and boundary obligations on the PC are untouched. The gate is degree 1, so both constraints stay
degree 2. The exhaustive test above also checks, on every tie-admitted assignment, that the
new gate equals the value the old helper's definition forces.

### 3.4 The three F2 rd-write gates become affine in the decoder flags

With `J = jal + jalr`, `S = slt`, `B = branch`, `Z = rd_is_zero`:

| Gate | `Baseline` helper | `ColumnCuts` expression |
|---|---|---|
| JAL/JALR writes rd | `J · (1 − Z)` | `J + B − Z` |
| SLT writes rd | `S · (1 − Z)` | `S` |
| rd = x0 | `(J + S + B) · Z` | `Z` |

(`f2_rd_write_gates`, `jump_branch_slt.rs:1090-1102`.) The five rd-write constraints that
consume them are unchanged (`jump_branch_slt.rs:1050-1073`): low limb
`jj·saved_pc_low + slt·slt_value − (jj + slt)·rd_write[0] = 0`, high limb
`jj·(saved_pc_high − rd_write[1]) = 0`, `slt·rd_write[1] = 0`, and `rd_zero·rd_write[0..1] = 0`.

On the decoder domain the two columns agree because of the mask facts of §2:

| Row class | JAL/JALR writes rd | SLT writes rd | rd = x0 |
|---|---:|---:|---:|
| JAL/JALR, rd ≠ x0 | 1 | 0 | 0 |
| JAL/JALR, rd = x0 | 0 | 0 | 1 |
| BRANCH (always `Z`) | 0 | 0 | 1 |
| SLT/SLTU (never `Z`) | 0 | 1 | 0 |
| F1/F3/F4, padding | 0 | 0 | 0 |

The derivation: `Z` is set only on JAL/JALR with `rd = 0` and on BRANCH, so
`J·Z = Z − B` and `J·(1 − Z) = J + B − Z`; `S·Z = 0` gives `S·(1 − Z) = S`; and `(J+S+B)·Z = Z`
because `Z` implies one F2 sub-op. The facts are sufficient and, within the one-dispatch-bit
domain, each is necessary for the corresponding identity. They are enforced on the real table
by the setup-time panic (§2) and tested on every entry of the regular guests' setup tables by
`circuit_defs/setups/tests/unified_decoder_masks.rs`.

Two tests verify the identities against the circuit rather than against this table:
`column_cuts_tests.rs::column_cuts_gates_match_baseline_helpers_on_all_row_classes` builds
the `Baseline` system in both fields, solves each removed helper from its own defining
constraint and compares it with the `ColumnCuts` gate on every decoder row class and on
padding; `dispatch_tie_strengthens_one_hot_exhaustively` does the same over all 2^20 Boolean
assignments and confirms that among the tie-admitted executing assignments the affine gates differ from
the helpers on exactly 16 masks, every one of which the validator rejects.

## 4. The completeness defect found during implementation, and the rule it produced

The first native prove → verify round trip with the aliases failed in the verifier
(`GkrFinalStepCheckFailed { layer: 0 }`) although every constraint-side check passed. The
cause was in witness generation, not in the circuit: the SSA → Rust lowering of a masked
conditional write is a select against a readback of the target at the writer's own type
(`witness_eval_generator/src/derive_from_ssa/mod.rs`, the `Expression::U8` and `U16` arms:
`set_witness_place_u8(idx, select(mask, value, get_witness_place_u8(idx)))`). Family 3's
first version wrote its byte splits into slots 17/18 with `conditionally_assign_u8`, so on
every non-F3 row the masked-off branch wrote the F1/F2/F4 register limb back truncated to
eight bits. The cs debug evaluator cannot see this: it skips a conditional write whose mask
is false (`cs/src/witness_placer/cs_debug_evaluator.rs`, `conditionally_assign_u8/u16`), so
single-cycle replays through it produce the right witness while the generated code does not.
The defect produced honest proofs that fail verification; it cannot produce an accepting
proof of a false statement, since the prover still commits whatever values it has and the
verifier checks the same constraints.

What follows from it:

- Every masked writer of a shared slot must be at least as wide as every value another family
  leaves in that slot. Family 3 now writes the byte splits as
  `conditionally_assign_u16(slot, is_f3, byte.widen())` (`binary_shifts.rs:85-113`); the F1,
  F2 and F4 writers of slots 17/18/7 are u32/u16 (`add_sub_lui_auipc_mop.rs:514`,
  `jump_branch_slt.rs:279-285, 718`, `mem_word_only_lw_sw.rs:432`), and the F3 shift-output
  peek writes slot 7 as a field value (`cs/src/cs/lookup_utils.rs:28-36`).
- The writer-width rule `liveness.rs::check_slot_write_widths` reads the committed SSA graphs
  and rejects any u8 or bool `WriteVariable` into slots 17, 18 or 7
  (`aliased_slot_writers_are_at_least_u16_{committed,in_memory}`).
- `prover` `tests::gkr::unified_generated_witness` runs the SSA-generated witness functions
  over real traces in both fields and checks arithmetic, RC-16/timestamp ranges and decoder
  membership on the result; under `ColumnCuts` it also asserts that some non-F3 row holds a
  register limb above 0xFF in slot 17, so the test exercises the defect class.
- A census of every masked `WriteVariable` in both committed SSA graphs found no other
  narrowing readback: the Boolean pool has only Boolean writers, and scratch variables 0–18
  have only u16/u32/field masked writers (slots 19/20 have unconditional u8 writers only).

## 5. Verification map

| Claim | Test | Crate | Notes |
|---|---|---|---|
| Widths and layer dimensions of §1, in both fields | `tests::gkr::unified_column_profile::unified_profile_width_vectors` | `prover` | `#[ignore]`; compiles four artifacts |
| Decoder masks obey the facts of §2; validator exact over all 2^19 masks | `decoder::tests::{unified_decoder_accepts_exactly_the_enumerated_kinds, unified_decoder_mask_validator_is_exact, invalid_decoded_mask_panics}` (11 decoder tests) | `cs` | |
| The real setup tables obey the facts | `unified_setup_decoder_tables_pass_the_mask_validator` | `setups` (tests) | every entry of the regular guests' tables through the setups' own builder |
| Each new gate equals its removed helper on every row class and padding; tie strictly stronger; 16 off-table masks | `column_cuts_tests::{column_cuts_gates_match_baseline_helpers_on_all_row_classes, dispatch_tie_strengthens_one_hot_exhaustively}` | `cs` | exhaustive over 2^20 `(execute, mask)` |
| No reader of slots 17/18/7 is live on a row another family occupies; one unconditional RC-16 per slot; no memory-tuple reader | `liveness::tests::{aliasing_liveness_committed_layouts, aliasing_liveness_in_memory}` | `cs` | `#[ignore]`; resolves every compiled relation to a polynomial over base columns and substitutes each row class |
| The walker can fail | `liveness::tests::aliasing_liveness_checker_rejects_injected_readers` | `cs` | `#[ignore]`; negative control |
| The decoder-lookup oracle used by the tests matches the compiled decoder relation | `liveness::tests::decoder_lookup_oracle_matches_compiled_relation` | `cs` | `#[ignore]` |
| No u8/bool masked writer into slots 17/18/7 | `liveness::tests::aliased_slot_writers_are_at_least_u16_{committed,in_memory}` | `cs` | `#[ignore]` |
| Forged flags, padding flags, `RD_IS_ZERO` misuse, rd writes on x0/branch, wrong non-F2 PC, forged carry, slot-7 attacks all rejected | `tests::gkr::unified_negative_tests::column_cuts_negative_cases_rejected`, plus the pre-existing `two_family_bits_on_one_row_rejected`, `empty_family_mask_on_executing_row_rejected`, `unified_f2_pooled_var_binds_on_slt_row_rejected`, `unified_top14_pooled_corruption_on_sw_row_rejected`, `unified_mulmod_intermediate_forge_rejected` | `prover` | one honest trace, each case attributed to the named constraint |
| Generated witness code is satisfying on real traces (§4) | `tests::gkr::unified_generated_witness::generated_witness_satisfies_{regular_layout,proth120_wrap_layout}` | `prover` | |
| cs-evaluator control on real cycles | `single_cycle_tests::unified_circuit_tests::test::unified_column_cuts_real_cycles_satisfied` | `prover` | `#[ignore]`; replays ~700 cycles |
| Committed CUDA witness source and forward schedule follow the new layout | `gpu_witness_eval_generator` `tests::{committed_witness_cuh_is_current, every_committed_cuh_is_listed}`; `gpu_gkr_compiler` `every_retained_forward_artifact_validates_compiles_and_encodes` (`tests/forward_corpus.rs:42`) | GPU crates | currentness guards, no GPU needed; they do not establish GPU execution parity |
| BabyBear proof generation and native verification | `prover::tests::gkr::unified_circuit::gkr_run_unified_test_sec_100`; `verifier::native::unified_reduced_machine_sec_100` | `prover`, `verifier` | The producer regenerates the unified CPU proof; the `native` integration target verifies the committed proof with the generated verifier. |
| Full-statement verification of the BabyBear fixture | `full_statement_verifier::unified::{unified_base_layer_accepts_valid_proof, unified_base_layer_rejects_corrupted_stream, rejects_corrupted_setup_cap, rejects_tampered_final_register_state, rejects_num_it_circuits_zero, rejects_num_it_circuits_exceeds_num_circuits, rejects_duplicated_multi_instance, unified_base_layer_transpiler_accepts_valid_proof}` | `full_statement_verifier` | Eight tests in integration target `unified`, all `#[ignore]`; checks the valid fixture, corrupted proof/setup/state, invalid instance counts and the RISC-V verifier. The transpiler test also requires the optional base-layer verifier binary. |
| Proth120 2^22 packed proof and calldata consistency | `prover::tests::gkr::large_field::gkr_unified_packed_commitment_basic_fibonacci`; `verifier_evm::flatten_roundtrip::flatten_and_seed_match_reference` | `prover`, `verifier_evm` | The ignored producer proves `circuit_tester` despite its name. The `flatten_roundtrip` integration test checks calldata and transcript values against the committed proof. This smoke fixture is not full-chain L1 parity coverage. |
| Merged EVM verifier acceptance and rejection | `GkrWhirMergedTest::{test_merged_single_tx, test_production_verifier_rejects_other_program, test_noncanonical_dim_reduce_lane_rejected, test_zero_registry_rejected, test_codeless_registry_rejected, test_refusing_registry_fails_verification}` | `verifier_evm` Foundry suite | Six tests in `generated_contracts/merged/test/GkrWhirMerged.t.sol`. The fixture contract binds the saved proof's program; the production contract retains the feeder binding. |

For integration tests, `crate::target::test` names the crate, Cargo test target and test.
The regenerated verifier binaries were reproduced using the pinned
Docker build in [`tools/reproduce`](../tools/reproduce/README.md): all 57 tracked artifacts
matched byte-for-byte. Nine artifacts changed relative to the baseline: the three unified
FSV variants, each with `.bin`, `.elf` and `.text` outputs.

Coverage limits:

- The generated-witness tests check arithmetic, the two range-check families and decoder
  membership. They do not check membership of the other generic lookups (Family 3's byte
  and shift tables, RegIsZero, JumpCleanupOffset, and the rest). A corruption of slot 17 or
  18 on an F3 row that keeps arithmetic and RC-16 satisfied is rejected only by the real
  lookup argument. The native round trip enforces that argument on the honest program it
  proves; no adversarial round trip with such an injected corruption was run, and the unit
  checkers would not see it. A lookup-membership oracle and a negative case for that
  corruption would cover this gap.
- The writer-width rule is scoped to slots 17/18/7, and the six `liveness` tests are
  `#[ignore]` by default; the committed-layout and committed-SSA variants only read JSON and
  should run in CI.

On the regular 2^23 GPU path, a same-device comparison over 10 Ethereum blocks used the
baseline, the column cuts and a baseline with a freshly searched forward schedule. Each
arm ran two processes over the same blocks, excluding warmup. Mean per-block proving
times were 4,779, 4,781 and 4,780 ms respectively: the column-cut deltas were within the
schedule control's noise. The regular GKR verifier-input stream shrank from 329,072 to
323,248 bytes (−1.77%), and recursion verifier cycles fell by 0.70–0.81% across the two
observed proof classes. L1 feeder/wrap GPU measurements are pending.

On an earlier L1 branch, rather than this change's trunk base, the regular unified
recursion verifier program went from 3,519,971 to 3,502,526 cycles and the L1 wrap program
from 2,062,486 to 2,043,353 cycles. The regular verifier ROM grew by 512 bytes
(2,211,108 → 2,211,620). These are results for that branch's programs and proof shapes,
not timing predictions for the trunk or L1 GPU paths.

## 6. Where to look first, and how to re-derive

Read in this order:

1. `circuit.rs`: the `UnifiedCircuitProfile` enum and slot constants (`:69-132`), the
   register allocation (`:393-407`), `non_f2_dispatch_sum`/`dispatch_sum` (`:480-505`), the
   PC-bump gate (`:560-624`) and the dispatch tie with the padding-zeroing constraint
   (`:629-720`).
2. `jump_branch_slt.rs:1084-1102` (`f2_rd_write_gates`) and the rd-write constraints at
   `:1050-1073`; `decoder.rs:35-54` and `:147-163` for the mask facts and the panic.
3. `binary_shifts.rs:58-113` for the slot assignment and the u16 conditional writers; then
   the reader table of §3.1 against the source.
4. `column_cuts_tests.rs` and `liveness.rs` for the mechanical checks; `unified_negative_tests.rs`
   from `column_cuts_negative_cases_rejected` for the attacks.

Re-derive the widths and the artifacts (release builds; `RUST_MIN_STACK=1073741824`):

```sh
# widths and layer dimensions of both profiles, both fields
cargo test -p prover --release --lib unified_profile_width_vectors -- --ignored --nocapture
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
# the mechanical soundness checks on the committed artifacts
cargo test -p cs --release --lib column_cuts
cargo test -p cs --release --lib unified_reduced_machine::decoder::tests
cargo test -p cs --release --lib liveness -- --ignored --nocapture
cargo test -p setups --release --test unified_decoder_masks
cargo test -p prover --release --lib column_cuts_negative_cases_rejected
cargo test -p prover --release --lib unified_generated_witness
```

The committed layouts must show `memory_layout.total_width = 38` and
`witness_layout.total_width = 58`; the generated verifiers declare `[38, 58, 10]` columns for
the regular circuit and `[96, 10]` for the feeder variant.
