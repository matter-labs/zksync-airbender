module
public import Proven.Setup.Native.ShiftBinop.Columns
public import Human.Compiler.NativeSetups.Claims

@[expose] public section

namespace Airbender.Verification
open Import.Setup ShiftBinopSetupProofs

/-- Each column of the imported setup is the column formula (kernel scans), and the column formula is the reviewed
    row formula on the fixed rows and the fixture decoder rows. -/
theorem shift_binop_import : ShiftBinopImportClaim := by
  refine ⟨rfl, rfl, fun index bound position => ?_⟩
  replace bound : index < 16777216 := bound
  have rows : decode (Compiler.NativeSetups.shiftBinopSetup.columns.getD position.val []) index =
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

end Airbender.Verification
