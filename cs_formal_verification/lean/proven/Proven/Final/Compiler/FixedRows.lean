module
public import Human.Compiler.NativeSetups.Ranges
public import Proven.Setup.Native.MulDiv.Columns
public import Proven.Setup.Native.WordMemory.Columns
public import Proven.Setup.Native.JumpBranch.Columns
public import Proven.Setup.Native.AddSub.Columns

@[expose] public section

namespace Airbender.Compiler
open Import.Setup

open NativeFixedRows.MulDivSetupProofs in
/-- Column `position` of the imported multiply/divide setup is its column formula. -/
private theorem mul_div_columns (index : Nat) (bound : index < 8388608) (position : Fin 9) :
    decode (NativeSetups.mulDivSetup.columns.getD position.val []) index =
      (![column0, column1, column2, column3, column4, column5, column6, column7, column8] position index : Int) := by
  fin_cases position
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
/-- Each column of the imported setup is the column formula (kernel scans), and the column formula is the reviewed
    row formula on the fixed rows and the fixture decoder rows. -/
theorem NativeFixedRows.mul_div_import : NativeFixedRows.MulDivImportClaim := by
  refine ⟨rfl, rfl, fun index bound position => ?_⟩
  rw [mul_div_columns index bound position]
  dsimp only
  split
  · rename_i fixed
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩ := column_eq index fixed
    fin_cases position
    · exact c0.symm
    · exact c1.symm
    · exact c2.symm
    · exact c3.symm
    · exact c4.symm
    · exact c5.symm
    · exact c6.symm
    · exact c7.symm
    · exact c8.symm
  · exact (column_after index (by omega) position).symm

/-- The rows of table 26 are rows of the multiply/divide fixed region. -/
theorem NativeSetups.range13_import : NativeSetups.Range13ImportClaim := by
  intro index bound position
  have length : NativeSetups.mulDivSetup.traceLen = 8388608 := rfl
  rw [NativeFixedRows.mul_div_import.2.2 (196608 + index) (by omega) position]
  dsimp only
  simp only [show 196608 + index < 270336 by omega, ↓reduceDIte, NativeFixedRows.mulDiv,
    show ¬196608 + index < 131072 by omega, show ¬196608 + index < 196608 by omega,
    show 196608 + index < 204800 by omega, ↓reduceIte, Nat.add_sub_cancel_left]
  fin_cases position <;> simp

open NativeFixedRows.WordMemorySetupProofs in
/-- Each column of the imported setup is the column formula (kernel scans), and the column formula is the reviewed
    row formula on the ROM rows of the fixture and the fixture decoder rows. -/
theorem NativeFixedRows.word_memory_import : NativeFixedRows.WordMemoryImportClaim := by
  refine ⟨rfl, rfl, fun index bound position => ?_⟩
  replace bound : index < 16777216 := bound
  have rows : decode (NativeSetups.wordMemorySetup.columns.getD position.val []) index =
      (![column0, column1, column2, column3, column4, column5, column6, column7, column8] position index : Int) := by
    fin_cases position
    · exact column0_rows index bound
    · exact column1_rows index bound
    · exact column2_rows index bound
    · exact column3_rows index bound
    · exact column4_rows index bound
    · exact column5_rows index bound
    · exact column6_rows index bound
    · exact column7_rows index bound
    · exact column8_rows index bound
  rw [rows]
  dsimp only
  split
  · rename_i fixed
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8⟩ := column_eq index fixed
    fin_cases position
    · exact c0.symm
    · exact c1.symm
    · exact c2.symm
    · exact c3.symm
    · exact c4.symm
    · exact c5.symm
    · exact c6.symm
    · exact c7.symm
    · exact c8.symm
  · exact (column_after index (by omega) position).symm

open NativeFixedRows.JumpBranchSetupProofs in
/-- Each column of the imported setup is the column formula (kernel scans), and the column formula is the reviewed
    row formula on the fixed rows and the fixture decoder rows. -/
theorem NativeFixedRows.jump_branch_import : NativeFixedRows.JumpBranchImportClaim := by
  refine ⟨rfl, rfl, fun index bound position => ?_⟩
  replace bound : index < 16777216 := bound
  have rows : decode (NativeSetups.jumpBranchSetup.columns.getD position.val []) index =
      (![column0, column1, column2, column3, column4, column5, column6, column7, column8, column9] position index :
        Int) := by
    fin_cases position
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
  rw [rows]
  dsimp only
  split
  · rename_i fixed
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := column_eq index fixed
    fin_cases position
    · exact c0.symm
    · exact c1.symm
    · exact c2.symm
    · exact c3.symm
    · exact c4.symm
    · exact c5.symm
    · exact c6.symm
    · exact c7.symm
    · exact c8.symm
    · exact c9.symm
  · exact (column_after index (by omega) position).symm

open NativeFixedRows.AddSubSetupProofs in
/-- Each column of the imported setup is the column formula (kernel scans), and the column formula is the claimed
    decoder row of the fixture. -/
theorem NativeFixedRows.add_sub_import : NativeFixedRows.AddSubImportClaim := by
  refine ⟨rfl, rfl, fun index bound position => ?_⟩
  replace bound : index < 16777216 := bound
  have rows : decode (NativeSetups.addSubSetup.columns.getD position.val []) index =
      (![column0, column1, column2, column3, column4, column5, column6, column7] position index : Int) := by
    fin_cases position
    · exact column0_rows index bound
    · exact column1_rows index bound
    · exact column2_rows index bound
    · exact column3_rows index bound
    · exact column4_rows index bound
    · exact column5_rows index bound
    · exact column6_rows index bound
    · exact column7_rows index bound
  rw [rows]
  exact (column_eq index position).symm

end Airbender.Compiler
