module
public import Proven.Compiler.PrimitiveRows
public import Proven.Compiler.TaggedMembership

@[expose] public section
namespace Airbender.Compiler.NativePrimitiveMembership
open Airbender Trace NativeArithmetic NativePublicSetup NativePublicSetup.Proofs NativePublicSetup.Metadata
set_option warningAsError true

namespace JumpBranch
/-- The selected native region supplies its retained logical primitive. -/
theorem tag1_contains (initial : RV.State) (program : List RVMachineProgramEntry)
    (row : NativeSetupIndex (.pooled .jumpBranchSlt)) (selected : genericCell initial program (.pooled .jumpBranchSlt) row 9 = 1) (provided : Array (F × F)) :
    (Verification.regIsZeroTable (p := babyBearModulus)).Contains provided (genericCell initial program (.pooled .jumpBranchSlt) row 0, genericCell initial program (.pooled .jumpBranchSlt) row 1) := by
  obtain ⟨position, _, equal⟩ := fixed_of_tag initial program (.pooled .jumpBranchSlt) rfl row 1
    (by decide +kernel) (by decide +kernel) selected
  let native := Fin.ofNat 4456448 position
  have fields : rows initial program (.pooled .jumpBranchSlt) 0 row =
      (NativeFixedRows.jumpBranch native).toList.map (fun (n : Nat) => (n : F)) := by
    simpa only [NativePublicSetup.fixedRow] using equal
  have cell0 : genericCell initial program (.pooled .jumpBranchSlt) row 0 = ((NativeFixedRows.jumpBranch native)[0] : F) := by
    unfold genericCell
    rw [fields]
    simp
  have cell1 : genericCell initial program (.pooled .jumpBranchSlt) row 1 = ((NativeFixedRows.jumpBranch native)[1] : F) := by
    unfold genericCell
    rw [fields]
    simp
  have cell9 : genericCell initial program (.pooled .jumpBranchSlt) row 9 = ((NativeFixedRows.jumpBranch native)[9] : F) := by
    unfold genericCell
    rw [fields]
    simp
  have selectedNative : ((NativeFixedRows.jumpBranch native)[9] : F) = 1 := cell9.symm.trans selected
  rw [cell0, cell1]
  exact NativePrimitiveRows.jump1 native selectedNative provided

end JumpBranch

namespace JumpBranch
/-- The selected native region supplies its retained logical primitive. -/
theorem tag2_contains (initial : RV.State) (program : List RVMachineProgramEntry)
    (row : NativeSetupIndex (.pooled .jumpBranchSlt)) (selected : genericCell initial program (.pooled .jumpBranchSlt) row 9 = 2) (provided : Array (F × F × F)) :
    (Verification.jumpCleanupTable (p := babyBearModulus)).Contains provided (genericCell initial program (.pooled .jumpBranchSlt) row 0, genericCell initial program (.pooled .jumpBranchSlt) row 1, genericCell initial program (.pooled .jumpBranchSlt) row 2) := by
  obtain ⟨position, _, equal⟩ := fixed_of_tag initial program (.pooled .jumpBranchSlt) rfl row 2
    (by decide +kernel) (by decide +kernel) selected
  let native := Fin.ofNat 4456448 position
  have fields : rows initial program (.pooled .jumpBranchSlt) 0 row =
      (NativeFixedRows.jumpBranch native).toList.map (fun (n : Nat) => (n : F)) := by
    simpa only [NativePublicSetup.fixedRow] using equal
  have cell0 : genericCell initial program (.pooled .jumpBranchSlt) row 0 = ((NativeFixedRows.jumpBranch native)[0] : F) := by
    unfold genericCell
    rw [fields]
    simp
  have cell1 : genericCell initial program (.pooled .jumpBranchSlt) row 1 = ((NativeFixedRows.jumpBranch native)[1] : F) := by
    unfold genericCell
    rw [fields]
    simp
  have cell2 : genericCell initial program (.pooled .jumpBranchSlt) row 2 = ((NativeFixedRows.jumpBranch native)[2] : F) := by
    unfold genericCell
    rw [fields]
    simp
  have cell9 : genericCell initial program (.pooled .jumpBranchSlt) row 9 = ((NativeFixedRows.jumpBranch native)[9] : F) := by
    unfold genericCell
    rw [fields]
    simp
  have selectedNative : ((NativeFixedRows.jumpBranch native)[9] : F) = 2 := cell9.symm.trans selected
  rw [cell0, cell1, cell2]
  exact NativePrimitiveRows.jump2 native selectedNative provided

end JumpBranch

namespace JumpBranch
/-- The selected native region supplies its retained logical primitive. -/
theorem tag5_contains (initial : RV.State) (program : List RVMachineProgramEntry)
    (row : NativeSetupIndex (.pooled .jumpBranchSlt)) (selected : genericCell initial program (.pooled .jumpBranchSlt) row 9 = 5) (provided : Array (F × F)) :
    (Verification.u16SignTable (p := babyBearModulus)).Contains provided (genericCell initial program (.pooled .jumpBranchSlt) row 0, genericCell initial program (.pooled .jumpBranchSlt) row 1) := by
  obtain ⟨position, _, equal⟩ := fixed_of_tag initial program (.pooled .jumpBranchSlt) rfl row 5
    (by decide +kernel) (by decide +kernel) selected
  let native := Fin.ofNat 4456448 position
  have fields : rows initial program (.pooled .jumpBranchSlt) 0 row =
      (NativeFixedRows.jumpBranch native).toList.map (fun (n : Nat) => (n : F)) := by
    simpa only [NativePublicSetup.fixedRow] using equal
  have cell0 : genericCell initial program (.pooled .jumpBranchSlt) row 0 = ((NativeFixedRows.jumpBranch native)[0] : F) := by
    unfold genericCell
    rw [fields]
    simp
  have cell1 : genericCell initial program (.pooled .jumpBranchSlt) row 1 = ((NativeFixedRows.jumpBranch native)[1] : F) := by
    unfold genericCell
    rw [fields]
    simp
  have cell9 : genericCell initial program (.pooled .jumpBranchSlt) row 9 = ((NativeFixedRows.jumpBranch native)[9] : F) := by
    unfold genericCell
    rw [fields]
    simp
  have selectedNative : ((NativeFixedRows.jumpBranch native)[9] : F) = 5 := cell9.symm.trans selected
  rw [cell0, cell1]
  exact NativePrimitiveRows.jump5 native selectedNative provided

end JumpBranch

namespace JumpBranch
/-- The selected native region supplies its retained logical primitive. -/
theorem tag31_contains (initial : RV.State) (program : List RVMachineProgramEntry)
    (row : NativeSetupIndex (.pooled .jumpBranchSlt)) (selected : genericCell initial program (.pooled .jumpBranchSlt) row 9 = 31) (provided : Array (F × F)) :
    (Verification.conditionalTable (p := babyBearModulus)).Contains provided (genericCell initial program (.pooled .jumpBranchSlt) row 0, genericCell initial program (.pooled .jumpBranchSlt) row 1) := by
  obtain ⟨position, _, equal⟩ := fixed_of_tag initial program (.pooled .jumpBranchSlt) rfl row 31
    (by decide +kernel) (by decide +kernel) selected
  let native := Fin.ofNat 4456448 position
  have fields : rows initial program (.pooled .jumpBranchSlt) 0 row =
      (NativeFixedRows.jumpBranch native).toList.map (fun (n : Nat) => (n : F)) := by
    simpa only [NativePublicSetup.fixedRow] using equal
  have cell0 : genericCell initial program (.pooled .jumpBranchSlt) row 0 = ((NativeFixedRows.jumpBranch native)[0] : F) := by
    unfold genericCell
    rw [fields]
    simp
  have cell1 : genericCell initial program (.pooled .jumpBranchSlt) row 1 = ((NativeFixedRows.jumpBranch native)[1] : F) := by
    unfold genericCell
    rw [fields]
    simp
  have cell9 : genericCell initial program (.pooled .jumpBranchSlt) row 9 = ((NativeFixedRows.jumpBranch native)[9] : F) := by
    unfold genericCell
    rw [fields]
    simp
  have selectedNative : ((NativeFixedRows.jumpBranch native)[9] : F) = 31 := cell9.symm.trans selected
  rw [cell0, cell1]
  exact NativePrimitiveRows.jump31 native selectedNative provided

end JumpBranch

namespace MulDiv
/-- The selected native region supplies its retained logical primitive. -/
theorem tag1_contains (initial : RV.State) (program : List RVMachineProgramEntry)
    (row : NativeSetupIndex (.pooled .mulDiv)) (selected : genericCell initial program (.pooled .mulDiv) row 8 = 1) (provided : Array (F × F)) :
    (Verification.regIsZeroTable (p := babyBearModulus)).Contains provided (genericCell initial program (.pooled .mulDiv) row 0, genericCell initial program (.pooled .mulDiv) row 1) := by
  obtain ⟨position, _, equal⟩ := fixed_of_tag initial program (.pooled .mulDiv) rfl row 1
    (by decide +kernel) (by decide +kernel) selected
  let native := Fin.ofNat 270336 position
  have fields : rows initial program (.pooled .mulDiv) 0 row =
      (NativeFixedRows.mulDiv native).toList.map (fun (n : Nat) => (n : F)) := by
    simpa only [NativePublicSetup.fixedRow] using equal
  have cell0 : genericCell initial program (.pooled .mulDiv) row 0 = ((NativeFixedRows.mulDiv native)[0] : F) := by
    unfold genericCell
    rw [fields]
    simp
  have cell1 : genericCell initial program (.pooled .mulDiv) row 1 = ((NativeFixedRows.mulDiv native)[1] : F) := by
    unfold genericCell
    rw [fields]
    simp
  have cell8 : genericCell initial program (.pooled .mulDiv) row 8 = ((NativeFixedRows.mulDiv native)[8] : F) := by
    unfold genericCell
    rw [fields]
    simp
  have selectedNative : ((NativeFixedRows.mulDiv native)[8] : F) = 1 := cell8.symm.trans selected
  rw [cell0, cell1]
  exact NativePrimitiveRows.mul1 native selectedNative provided

end MulDiv

namespace MulDiv
/-- The selected native region supplies its retained logical primitive. -/
theorem tag41_contains (initial : RV.State) (program : List RVMachineProgramEntry)
    (row : NativeSetupIndex (.pooled .mulDiv)) (selected : genericCell initial program (.pooled .mulDiv) row 8 = 41) (provided : Array (F × F)) :
    (Verification.u16LowByteTable (p := babyBearModulus)).Contains provided (genericCell initial program (.pooled .mulDiv) row 0, genericCell initial program (.pooled .mulDiv) row 1) := by
  obtain ⟨position, _, equal⟩ := fixed_of_tag initial program (.pooled .mulDiv) rfl row 41
    (by decide +kernel) (by decide +kernel) selected
  let native := Fin.ofNat 270336 position
  have fields : rows initial program (.pooled .mulDiv) 0 row =
      (NativeFixedRows.mulDiv native).toList.map (fun (n : Nat) => (n : F)) := by
    simpa only [NativePublicSetup.fixedRow] using equal
  have cell0 : genericCell initial program (.pooled .mulDiv) row 0 = ((NativeFixedRows.mulDiv native)[0] : F) := by
    unfold genericCell
    rw [fields]
    simp
  have cell1 : genericCell initial program (.pooled .mulDiv) row 1 = ((NativeFixedRows.mulDiv native)[1] : F) := by
    unfold genericCell
    rw [fields]
    simp
  have cell8 : genericCell initial program (.pooled .mulDiv) row 8 = ((NativeFixedRows.mulDiv native)[8] : F) := by
    unfold genericCell
    rw [fields]
    simp
  have selectedNative : ((NativeFixedRows.mulDiv native)[8] : F) = 41 := cell8.symm.trans selected
  rw [cell0, cell1]
  exact NativePrimitiveRows.mul41 native selectedNative provided

end MulDiv

namespace MulDiv
/-- The selected native region supplies its retained logical primitive. -/
theorem tag26_contains (initial : RV.State) (program : List RVMachineProgramEntry)
    (row : NativeSetupIndex (.pooled .mulDiv)) (selected : genericCell initial program (.pooled .mulDiv) row 8 = 26) :
    (genericCell initial program (.pooled .mulDiv) row 0).val < 8192 := by
  obtain ⟨position, _, equal⟩ := fixed_of_tag initial program (.pooled .mulDiv) rfl row 26
    (by decide +kernel) (by decide +kernel) selected
  let native := Fin.ofNat 270336 position
  have fields : rows initial program (.pooled .mulDiv) 0 row =
      (NativeFixedRows.mulDiv native).toList.map (fun (n : Nat) => (n : F)) := by
    simpa only [NativePublicSetup.fixedRow] using equal
  have cell0 : genericCell initial program (.pooled .mulDiv) row 0 = ((NativeFixedRows.mulDiv native)[0] : F) := by
    unfold genericCell
    rw [fields]
    simp
  have cell8 : genericCell initial program (.pooled .mulDiv) row 8 = ((NativeFixedRows.mulDiv native)[8] : F) := by
    unfold genericCell
    rw [fields]
    simp
  have selectedNative : ((NativeFixedRows.mulDiv native)[8] : F) = 26 := cell8.symm.trans selected
  rw [cell0]
  exact NativePrimitiveRows.mul26 native selectedNative

end MulDiv

end Airbender.Compiler.NativePrimitiveMembership
