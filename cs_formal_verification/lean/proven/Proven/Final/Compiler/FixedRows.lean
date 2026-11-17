module
public import Human.Compiler.NativeSetups.Ranges
public import Human.Compiler.NativeSetups.Claims
public import Proven.Setup.Native.Fixture
public import Proven.Setup.Native.MulDiv.Columns
public import Proven.Setup.Native.WordMemory.Columns
public import Proven.Setup.Native.JumpBranch.Columns
public import Proven.Setup.Native.SubwordMemory.Columns
public import Proven.Setup.Native.Unified.Columns
public import Proven.Setup.Native.AddSub.Columns
public import Proven.Setup.Native.ShiftBinop.Columns

@[expose] public section

namespace Airbender.Compiler
open Import.Setup Import.Setup.Scan NativeSetups.Proofs

open NativeFixedRows.MulDivSetupProofs in
/-- Column `k` of the imported setup is its column formula (kernel scans). -/
private theorem mul_div_columns (index : Nat) (bound : index < 8388608) (k : Nat) (inside : k < formulas.length) :
    decode (NativeSetups.mulDivSetup.columns.getD k []) index = (formulas[k] index : Int) := by
  have inside : k < 9 := inside
  interval_cases k
  · exact column0_rows index bound
  · exact column1_rows index bound
  · exact column2_rows index bound
  · exact column3_rows index bound
  · exact column4_rows index bound
  · exact column5_rows index bound
  · exact column6_rows index bound
  · exact column7_rows index bound
  · exact column8_rows index bound

open NativeFixedRows.MulDivSetupProofs in
/-- The public generic rows of the setup fixture program are the column formulas: on the fixed region by `column_eq`,
    on the first four decoder slots by kernel evaluation, on the later rows by the row lemmas; and each imported column
    is its column formula. -/
theorem NativeFixedRows.mul_div_import : NativeFixedRows.MulDivImportClaim := by
  refine ⟨by decide +kernel, fun index bound => ?_⟩
  replace bound : index < 8388608 := bound
  rw [importedRows_formulas formulas rfl (mul_div_columns index bound)]
  refine genericRow_fixture (.pooled .mulDiv) .unrolledFullUnsigned formulas (fun n fixed => ?_) (fun slot early => ?_)
    (fun n low high => (row_decoder n low high).trans (by decide +kernel))
    (fun n low => (row_padding n low).trans (by decide +kernel)) index
  · obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩ := column_eq n fixed
    change ((NativeFixedRows.mulDiv (Fin.ofNat 270336 n)).toList).map _ = _
    rw [show Fin.ofNat 270336 n = ⟨n, fixed⟩ from Fin.ext (Nat.mod_eq_of_lt fixed)]
    refine fixed_formulas _ formulas n rfl fun k inside => ?_
    simp only [fixedRow, Vector.getElem_map] at c0 c1 c2 c3 c4 c5 c6 c7 c8
    interval_cases k
    exacts [c0, c1, c2, c3, c4, c5, c6, c7, c8]
  · interval_cases slot <;> decide +kernel

open NativeFixedRows.MulDivSetupProofs in
/-- The rows of table 26 are rows of the multiply/divide fixed region. -/
theorem NativeSetups.range13_import : NativeSetups.Range13ImportClaim := by
  intro index bound column
  rw [mul_div_columns (196608 + index) (by omega) column.val column.isLt]
  fin_cases column <;>
  simp (disch := omega) [formulas, column0, column1, column2, column3, column4, column5, column6, column7, column8,
    byRegion, nat_blt, pick_true, pick_false]

/-- Each CPU setup imports its range columns as the identity run, then zero padding to its trace length. -/
theorem NativeSetups.cpu_ranges_import : NativeSetups.CPURangesImportClaim := by
  intro data member index _
  simp only [NativeSetups.cpuSetups, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  exact ⟨Import.Setup.Proofs.decode_identity_padding _ _ index, Import.Setup.Proofs.decode_identity_padding _ _ index⟩

open NativeFixedRows.WordMemorySetupProofs in
/-- Column `k` of the imported setup is its column formula (kernel scans). -/
private theorem word_memory_columns (index : Nat) (bound : index < 16777216) (k : Nat) (inside : k < formulas.length) :
    decode (NativeSetups.wordMemorySetup.columns.getD k []) index = (formulas[k] index : Int) := by
  have inside : k < 9 := inside
  interval_cases k
  · exact column0_rows index bound
  · exact column1_rows index bound
  · exact column2_rows index bound
  · exact column3_rows index bound
  · exact column4_rows index bound
  · exact column5_rows index bound
  · exact column6_rows index bound
  · exact column7_rows index bound
  · exact column8_rows index bound

open NativeFixedRows.WordMemorySetupProofs in
/-- The public generic rows of the setup fixture program are the column formulas: on the fixed region by `column_eq`,
    on the first four decoder slots by kernel evaluation, on the later rows by the row lemmas; and each imported column
    is its column formula. -/
theorem NativeFixedRows.word_memory_import : NativeFixedRows.WordMemoryImportClaim := by
  refine ⟨by decide +kernel, fun index bound => ?_⟩
  replace bound : index < 16777216 := bound
  rw [importedRows_formulas formulas rfl (word_memory_columns index bound)]
  refine genericRow_fixture (.pooled .wordMemory) .unrolledFullUnsigned formulas
    (fun n fixed => ?_) (fun slot early => ?_)
    (fun n low high => (row_decoder n low high).trans (by decide +kernel))
    (fun n low => (row_padding n low).trans (by decide +kernel)) index
  · obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩ := column_eq n fixed
    change ((NativeFixedRows.wordMemory NativeSetups.fixtureWords (Fin.ofNat 1048577 n)).toList).map _ = _
    rw [show Fin.ofNat 1048577 n = ⟨n, fixed⟩ from Fin.ext (Nat.mod_eq_of_lt fixed)]
    refine fixed_formulas _ formulas n rfl fun k inside => ?_
    simp only [fixedRow, Vector.getElem_map] at c0 c1 c2 c3 c4 c5 c6 c7 c8
    interval_cases k
    exacts [c0, c1, c2, c3, c4, c5, c6, c7, c8]
  · interval_cases slot <;> decide +kernel

open NativeFixedRows.JumpBranchSetupProofs in
/-- Column `k` of the imported setup is its column formula (kernel scans). -/
private theorem jump_branch_columns (index : Nat) (bound : index < 16777216) (k : Nat) (inside : k < formulas.length) :
    decode (NativeSetups.jumpBranchSetup.columns.getD k []) index = (formulas[k] index : Int) := by
  have inside : k < 10 := inside
  interval_cases k
  · exact column0_rows index bound
  · exact column1_rows index bound
  · exact column2_rows index bound
  · exact column3_rows index bound
  · exact column4_rows index bound
  · exact column5_rows index bound
  · exact column6_rows index bound
  · exact column7_rows index bound
  · exact column8_rows index bound
  · exact column9_rows index bound

open NativeFixedRows.JumpBranchSetupProofs in
/-- The public generic rows of the setup fixture program are the column formulas: on the fixed region by `column_eq`,
    on the first four decoder slots by kernel evaluation, on the later rows by the row lemmas; and each imported column
    is its column formula. -/
theorem NativeFixedRows.jump_branch_import : NativeFixedRows.JumpBranchImportClaim := by
  refine ⟨by decide +kernel, fun index bound => ?_⟩
  replace bound : index < 16777216 := bound
  rw [importedRows_formulas formulas rfl (jump_branch_columns index bound)]
  refine genericRow_fixture (.pooled .jumpBranchSlt) .unrolledFullUnsigned formulas
    (fun n fixed => ?_) (fun slot early => ?_)
    (fun n low high => (row_decoder n low high).trans (by decide +kernel))
    (fun n low => (row_padding n low).trans (by decide +kernel)) index
  · obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := column_eq n fixed
    change ((NativeFixedRows.jumpBranch (Fin.ofNat 4456448 n)).toList).map _ = _
    rw [show Fin.ofNat 4456448 n = ⟨n, fixed⟩ from Fin.ext (Nat.mod_eq_of_lt fixed)]
    refine fixed_formulas _ formulas n rfl fun k inside => ?_
    simp only [fixedRow, Vector.getElem_map] at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9
    interval_cases k
    exacts [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9]
  · interval_cases slot <;> decide +kernel

open NativeFixedRows.SubwordMemorySetupProofs in
/-- Column `k` of the imported setup is its column formula (kernel scans). -/
private theorem subword_memory_columns (index : Nat) (bound : index < 16777216) (k : Nat)
    (inside : k < formulas.length) :
    decode (NativeSetups.subwordMemorySetup.columns.getD k []) index = (formulas[k] index : Int) := by
  have inside : k < 9 := inside
  interval_cases k
  · exact column0_rows index bound
  · exact column1_rows index bound
  · exact column2_rows index bound
  · exact column3_rows index bound
  · exact column4_rows index bound
  · exact column5_rows index bound
  · exact column6_rows index bound
  · exact column7_rows index bound
  · exact column8_rows index bound

open NativeFixedRows.SubwordMemorySetupProofs in
/-- The public generic rows of the setup fixture program are the column formulas: on the fixed region by `column_eq`,
    on the first four decoder slots by kernel evaluation, on the later rows by the row lemmas; and each imported column
    is its column formula. -/
theorem NativeFixedRows.subword_memory_import : NativeFixedRows.SubwordMemoryImportClaim := by
  refine ⟨by decide +kernel, fun index bound => ?_⟩
  replace bound : index < 16777216 := bound
  rw [importedRows_formulas formulas rfl (subword_memory_columns index bound)]
  refine genericRow_fixture (.pooled .subwordMemory) .unrolledFullUnsigned formulas
    (fun n fixed => ?_) (fun slot early => ?_)
    (fun n low high => (row_decoder n low high).trans (by decide +kernel))
    (fun n low => (row_padding n low).trans (by decide +kernel)) index
  · obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩ := column_eq n fixed
    change ((Verification.subwordRow NativeSetups.fixtureWords (Fin.ofNat 13238273 n)).toList).map _ = _
    rw [show Fin.ofNat 13238273 n = ⟨n, fixed⟩ from Fin.ext (Nat.mod_eq_of_lt fixed)]
    refine fixed_formulas _ formulas n rfl fun k inside => ?_
    simp only [fixedRow, Vector.getElem_map] at c0 c1 c2 c3 c4 c5 c6 c7 c8
    interval_cases k
    exacts [c0, c1, c2, c3, c4, c5, c6, c7, c8]
  · interval_cases slot <;> decide +kernel

open NativeFixedRows.UnifiedSetupProofs in
/-- Column `k` of the imported setup is its column formula (kernel scans). -/
private theorem unified_columns (index : Nat) (bound : index < 8388608) (k : Nat) (inside : k < formulas.length) :
    decode (NativeSetups.unifiedSetup.columns.getD k []) index = (formulas[k] index : Int) := by
  have inside : k < 10 := inside
  interval_cases k
  · exact column0_rows index bound
  · exact column1_rows index bound
  · exact column2_rows index bound
  · exact column3_rows index bound
  · exact column4_rows index bound
  · exact column5_rows index bound
  · exact column6_rows index bound
  · exact column7_rows index bound
  · exact column8_rows index bound
  · exact column9_rows index bound

open NativeFixedRows.UnifiedSetupProofs in
/-- The public generic rows of the setup fixture program are the column formulas: on the fixed region by `column_eq`,
    on the first four decoder slots by kernel evaluation, on the later rows by the row lemmas; and each imported column
    is its column formula. -/
theorem NativeFixedRows.unified_import : NativeFixedRows.UnifiedImportClaim := by
  refine ⟨by decide +kernel, fun index bound => ?_⟩
  replace bound : index < 8388608 := bound
  rw [importedRows_formulas formulas rfl (unified_columns index bound)]
  refine genericRow_fixture .unified .unified formulas (fun n fixed => ?_) (fun slot early => ?_)
    (fun n low high => (row_decoder n low high).trans (by decide +kernel))
    (fun n low => (row_padding n low).trans (by decide +kernel)) index
  · obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := column_eq n fixed
    change ((NativeFixedRows.unified NativeSetups.fixtureWords (Fin.ofNat 2097537 n)).toList).map _ = _
    rw [show Fin.ofNat 2097537 n = ⟨n, fixed⟩ from Fin.ext (Nat.mod_eq_of_lt fixed)]
    refine fixed_formulas _ formulas n rfl fun k inside => ?_
    simp only [fixedRow, Vector.getElem_map] at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9
    interval_cases k
    exacts [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9]
  · interval_cases slot <;> decide +kernel

open NativeFixedRows.AddSubSetupProofs in
/-- Column `k` of the imported setup is its column formula (kernel scans). -/
private theorem add_sub_columns (index : Nat) (bound : index < 16777216) (k : Nat) (inside : k < formulas.length) :
    decode (NativeSetups.addSubSetup.columns.getD k []) index = (formulas[k] index : Int) := by
  have inside : k < 8 := inside
  interval_cases k
  · exact column0_rows index bound
  · exact column1_rows index bound
  · exact column2_rows index bound
  · exact column3_rows index bound
  · exact column4_rows index bound
  · exact column5_rows index bound
  · exact column6_rows index bound
  · exact column7_rows index bound

open NativeFixedRows.AddSubSetupProofs in
/-- The public generic rows of the setup fixture program are the column formulas: on the first four decoder slots by
    kernel evaluation, on the later rows by `row_after`; and each imported column is its column formula. The add/sub
    setup has no fixed region. -/
theorem NativeFixedRows.add_sub_import : NativeFixedRows.AddSubImportClaim := by
  refine ⟨by decide +kernel, fun index bound => ?_⟩
  replace bound : index < 16777216 := bound
  rw [importedRows_formulas formulas rfl (add_sub_columns index bound)]
  refine genericRow_fixture (.pooled .addSub) .unrolledFullUnsigned formulas
    (fun n fixed => absurd fixed (Nat.not_lt_zero n)) (fun slot early => ?_)
    (fun n low _ => (row_after n low).trans (by decide +kernel))
    (fun n low => (row_after n (Nat.le_trans (by decide) low)).trans (by decide +kernel)) index
  interval_cases slot <;> decide +kernel

end Airbender.Compiler

namespace Airbender.Verification
open Import.Setup Import.Setup.Scan Compiler Compiler.NativeSetups.Proofs

open ShiftBinopSetupProofs in
/-- Column `k` of the imported setup is its column formula (kernel scans). -/
private theorem shift_binop_columns (index : Nat) (bound : index < 16777216) (k : Nat) (inside : k < formulas.length) :
    decode (Compiler.NativeSetups.shiftBinopSetup.columns.getD k []) index = (formulas[k] index : Int) := by
  have inside : k < 10 := inside
  interval_cases k
  · exact column0_rows index bound
  · exact column1_rows index bound
  · exact column2_rows index bound
  · exact column3_rows index bound
  · exact column4_rows index bound
  · exact column5_rows index bound
  · exact column6_rows index bound
  · exact column7_rows index bound
  · exact column8_rows index bound
  · exact column9_rows index bound

open ShiftBinopSetupProofs in
/-- The public generic rows of the setup fixture program are the column formulas: on the fixed region by `column_eq`,
    on the first four decoder slots by kernel evaluation, on the later rows by the row lemmas; and each imported column
    is its column formula. -/
theorem shift_binop_import : ShiftBinopImportClaim := by
  refine ⟨by decide +kernel, fun index bound => ?_⟩
  replace bound : index < 16777216 := bound
  rw [importedRows_formulas formulas rfl (shift_binop_columns index bound)]
  refine genericRow_fixture (.pooled .shiftBinop) .unrolledFullUnsigned formulas
    (fun n fixed => ?_) (fun slot early => ?_)
    (fun n low high => (row_decoder n low high).trans (by decide +kernel))
    (fun n low => (row_padding n low).trans (by decide +kernel)) index
  · obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := column_eq n fixed
    change ((Verification.shiftBinopRow (Fin.ofNat 524545 n)).toList).map _ = _
    rw [show Fin.ofNat 524545 n = ⟨n, fixed⟩ from Fin.ext (Nat.mod_eq_of_lt fixed)]
    refine fixed_formulas _ formulas n rfl fun k inside => ?_
    simp only [fixedRow, Vector.getElem_map] at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9
    interval_cases k
    exacts [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9]
  · interval_cases slot <;> decide +kernel

end Airbender.Verification
