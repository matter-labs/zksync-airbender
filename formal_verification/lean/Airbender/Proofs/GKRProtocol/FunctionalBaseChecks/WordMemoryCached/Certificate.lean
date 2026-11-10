import Airbender.Proofs.GKRProtocol.FunctionalBaseChecks.WordMemoryCached.Bindings

namespace Airbender.Compiler.FunctionalBaseChecks.WordMemoryCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=
  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked

theorem baseFacts0 : Airbender.Compiler.FunctionalNative.WordMemoryCached.native.basePorts0 = true ∧ Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRelation0 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRecipe0 Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseOutput0 Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank Airbender.Compiler.FunctionalNative.WordMemoryCached.native.isBase Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate0.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨0, by decide +kernel⟩) (List.get_mem originalEntries ⟨0, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.basePorts0, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRelation0] using item

theorem baseFacts1 : Airbender.Compiler.FunctionalNative.WordMemoryCached.native.basePorts1 = true ∧ Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRelation1 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRecipe1 Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseOutput1 Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank Airbender.Compiler.FunctionalNative.WordMemoryCached.native.isBase Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate1.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨1, by decide +kernel⟩) (List.get_mem originalEntries ⟨1, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.basePorts1, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRelation1] using item

theorem baseFacts2 : Airbender.Compiler.FunctionalNative.WordMemoryCached.native.basePorts2 = true ∧ Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRelation2 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRecipe2 Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseOutput2 Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank Airbender.Compiler.FunctionalNative.WordMemoryCached.native.isBase Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate2.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨2, by decide +kernel⟩) (List.get_mem originalEntries ⟨2, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.basePorts2, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRelation2] using item

theorem baseFacts3 : Airbender.Compiler.FunctionalNative.WordMemoryCached.native.basePorts3 = true ∧ Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRelation3 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRecipe3 Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseOutput3 Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank Airbender.Compiler.FunctionalNative.WordMemoryCached.native.isBase Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate3.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨3, by decide +kernel⟩) (List.get_mem originalEntries ⟨3, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.basePorts3, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRelation3] using item

theorem baseFacts4 : Airbender.Compiler.FunctionalNative.WordMemoryCached.native.basePorts4 = true ∧ Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRelation4 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRecipe4 Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseOutput4 Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank Airbender.Compiler.FunctionalNative.WordMemoryCached.native.isBase Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate4.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨4, by decide +kernel⟩) (List.get_mem originalEntries ⟨4, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.basePorts4, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRelation4] using item

theorem baseFacts5 : Airbender.Compiler.FunctionalNative.WordMemoryCached.native.basePorts5 = true ∧ Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRelation5 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRecipe5 Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseOutput5 Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank Airbender.Compiler.FunctionalNative.WordMemoryCached.native.isBase Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate5.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨5, by decide +kernel⟩) (List.get_mem originalEntries ⟨5, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.basePorts5, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRelation5] using item

theorem baseFacts6 : Airbender.Compiler.FunctionalNative.WordMemoryCached.native.basePorts6 = true ∧ Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRelation6 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRecipe6 Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseOutput6 Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank Airbender.Compiler.FunctionalNative.WordMemoryCached.native.isBase Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate6.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨6, by decide +kernel⟩) (List.get_mem originalEntries ⟨6, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.basePorts6, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRelation6] using item

theorem baseFacts7 : Airbender.Compiler.FunctionalNative.WordMemoryCached.native.basePorts7 = true ∧ Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRelation7 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRecipe7 Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseOutput7 Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank Airbender.Compiler.FunctionalNative.WordMemoryCached.native.isBase Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate10.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨7, by decide +kernel⟩) (List.get_mem originalEntries ⟨7, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.basePorts7, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRelation7] using item

theorem baseFacts8 : Airbender.Compiler.FunctionalNative.WordMemoryCached.native.basePorts8 = true ∧ Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRelation8 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRecipe8 Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseOutput8 Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank Airbender.Compiler.FunctionalNative.WordMemoryCached.native.isBase Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate14.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨8, by decide +kernel⟩) (List.get_mem originalEntries ⟨8, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.basePorts8, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRelation8] using item

theorem baseFacts9 : Airbender.Compiler.FunctionalNative.WordMemoryCached.native.basePorts9 = true ∧ Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRelation9 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRecipe9 Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseOutput9 Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank Airbender.Compiler.FunctionalNative.WordMemoryCached.native.isBase Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate15.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨9, by decide +kernel⟩) (List.get_mem originalEntries ⟨9, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.basePorts9, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRelation9] using item

theorem baseFacts10 : Airbender.Compiler.FunctionalNative.WordMemoryCached.native.basePorts10 = true ∧ Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRelation10 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRecipe10 Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseOutput10 Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank Airbender.Compiler.FunctionalNative.WordMemoryCached.native.isBase Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate16.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨10, by decide +kernel⟩) (List.get_mem originalEntries ⟨10, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.basePorts10, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRelation10] using item

theorem baseFacts11 : Airbender.Compiler.FunctionalNative.WordMemoryCached.native.basePorts11 = true ∧ Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRelation11 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRecipe11 Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseOutput11 Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank Airbender.Compiler.FunctionalNative.WordMemoryCached.native.isBase Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate31.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨11, by decide +kernel⟩) (List.get_mem originalEntries ⟨11, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.basePorts11, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRelation11] using item

theorem baseFacts12 : Airbender.Compiler.FunctionalNative.WordMemoryCached.native.basePorts12 = true ∧ Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRelation12 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRecipe12 Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseOutput12 Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank Airbender.Compiler.FunctionalNative.WordMemoryCached.native.isBase Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate32.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨12, by decide +kernel⟩) (List.get_mem originalEntries ⟨12, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.basePorts12, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRelation12] using item

theorem baseFacts13 : Airbender.Compiler.FunctionalNative.WordMemoryCached.native.basePorts13 = true ∧ Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRelation13 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRecipe13 Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseOutput13 Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank Airbender.Compiler.FunctionalNative.WordMemoryCached.native.isBase Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate34.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨13, by decide +kernel⟩) (List.get_mem originalEntries ⟨13, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.basePorts13, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRelation13] using item

theorem baseFacts14 : Airbender.Compiler.FunctionalNative.WordMemoryCached.native.basePorts14 = true ∧ Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRelation14 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRecipe14 Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseOutput14 Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.bank Airbender.Compiler.FunctionalNative.WordMemoryCached.native.isBase Airbender.Compiler.FullArithmeticNative.WordMemoryCached.native.gate35.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨14, by decide +kernel⟩) (List.get_mem originalEntries ⟨14, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.basePorts14, Airbender.Compiler.FunctionalNative.WordMemoryCached.native.baseRelation14] using item

end Airbender.Compiler.FunctionalBaseChecks.WordMemoryCached
