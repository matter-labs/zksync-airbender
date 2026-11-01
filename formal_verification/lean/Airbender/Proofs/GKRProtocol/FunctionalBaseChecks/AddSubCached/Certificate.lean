import Airbender.Proofs.GKRProtocol.FunctionalBaseChecks.AddSubCached.Bindings

namespace Airbender.Compiler.FunctionalBaseChecks.AddSubCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=
  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked

theorem baseFacts0 : Airbender.Compiler.FunctionalNative.AddSubCached.native.basePorts0 = true ∧ Airbender.Compiler.FunctionalNative.AddSubCached.native.baseRelation0 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.AddSubCached.native.baseRecipe0 Airbender.Compiler.FunctionalNative.AddSubCached.native.baseOutput0 Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank Airbender.Compiler.FunctionalNative.AddSubCached.native.isBase Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate0.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨0, by decide +kernel⟩) (List.get_mem originalEntries ⟨0, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.AddSubCached.native.basePorts0, Airbender.Compiler.FunctionalNative.AddSubCached.native.baseRelation0] using item

theorem baseFacts1 : Airbender.Compiler.FunctionalNative.AddSubCached.native.basePorts1 = true ∧ Airbender.Compiler.FunctionalNative.AddSubCached.native.baseRelation1 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.AddSubCached.native.baseRecipe1 Airbender.Compiler.FunctionalNative.AddSubCached.native.baseOutput1 Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank Airbender.Compiler.FunctionalNative.AddSubCached.native.isBase Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate1.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨1, by decide +kernel⟩) (List.get_mem originalEntries ⟨1, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.AddSubCached.native.basePorts1, Airbender.Compiler.FunctionalNative.AddSubCached.native.baseRelation1] using item

theorem baseFacts2 : Airbender.Compiler.FunctionalNative.AddSubCached.native.basePorts2 = true ∧ Airbender.Compiler.FunctionalNative.AddSubCached.native.baseRelation2 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.AddSubCached.native.baseRecipe2 Airbender.Compiler.FunctionalNative.AddSubCached.native.baseOutput2 Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank Airbender.Compiler.FunctionalNative.AddSubCached.native.isBase Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate2.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨2, by decide +kernel⟩) (List.get_mem originalEntries ⟨2, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.AddSubCached.native.basePorts2, Airbender.Compiler.FunctionalNative.AddSubCached.native.baseRelation2] using item

theorem baseFacts3 : Airbender.Compiler.FunctionalNative.AddSubCached.native.basePorts3 = true ∧ Airbender.Compiler.FunctionalNative.AddSubCached.native.baseRelation3 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.AddSubCached.native.baseRecipe3 Airbender.Compiler.FunctionalNative.AddSubCached.native.baseOutput3 Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank Airbender.Compiler.FunctionalNative.AddSubCached.native.isBase Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate3.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨3, by decide +kernel⟩) (List.get_mem originalEntries ⟨3, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.AddSubCached.native.basePorts3, Airbender.Compiler.FunctionalNative.AddSubCached.native.baseRelation3] using item

theorem baseFacts4 : Airbender.Compiler.FunctionalNative.AddSubCached.native.basePorts4 = true ∧ Airbender.Compiler.FunctionalNative.AddSubCached.native.baseRelation4 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.AddSubCached.native.baseRecipe4 Airbender.Compiler.FunctionalNative.AddSubCached.native.baseOutput4 Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank Airbender.Compiler.FunctionalNative.AddSubCached.native.isBase Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate4.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨4, by decide +kernel⟩) (List.get_mem originalEntries ⟨4, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.AddSubCached.native.basePorts4, Airbender.Compiler.FunctionalNative.AddSubCached.native.baseRelation4] using item

theorem baseFacts5 : Airbender.Compiler.FunctionalNative.AddSubCached.native.basePorts5 = true ∧ Airbender.Compiler.FunctionalNative.AddSubCached.native.baseRelation5 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.AddSubCached.native.baseRecipe5 Airbender.Compiler.FunctionalNative.AddSubCached.native.baseOutput5 Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank Airbender.Compiler.FunctionalNative.AddSubCached.native.isBase Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate5.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨5, by decide +kernel⟩) (List.get_mem originalEntries ⟨5, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.AddSubCached.native.basePorts5, Airbender.Compiler.FunctionalNative.AddSubCached.native.baseRelation5] using item

theorem baseFacts6 : Airbender.Compiler.FunctionalNative.AddSubCached.native.basePorts6 = true ∧ Airbender.Compiler.FunctionalNative.AddSubCached.native.baseRelation6 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.AddSubCached.native.baseRecipe6 Airbender.Compiler.FunctionalNative.AddSubCached.native.baseOutput6 Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank Airbender.Compiler.FunctionalNative.AddSubCached.native.isBase Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate6.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨6, by decide +kernel⟩) (List.get_mem originalEntries ⟨6, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.AddSubCached.native.basePorts6, Airbender.Compiler.FunctionalNative.AddSubCached.native.baseRelation6] using item

theorem baseFacts7 : Airbender.Compiler.FunctionalNative.AddSubCached.native.basePorts7 = true ∧ Airbender.Compiler.FunctionalNative.AddSubCached.native.baseRelation7 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.AddSubCached.native.baseRecipe7 Airbender.Compiler.FunctionalNative.AddSubCached.native.baseOutput7 Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank Airbender.Compiler.FunctionalNative.AddSubCached.native.isBase Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate7.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨7, by decide +kernel⟩) (List.get_mem originalEntries ⟨7, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.AddSubCached.native.basePorts7, Airbender.Compiler.FunctionalNative.AddSubCached.native.baseRelation7] using item

theorem baseFacts8 : Airbender.Compiler.FunctionalNative.AddSubCached.native.basePorts8 = true ∧ Airbender.Compiler.FunctionalNative.AddSubCached.native.baseRelation8 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.AddSubCached.native.baseRecipe8 Airbender.Compiler.FunctionalNative.AddSubCached.native.baseOutput8 Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank Airbender.Compiler.FunctionalNative.AddSubCached.native.isBase Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate8.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨8, by decide +kernel⟩) (List.get_mem originalEntries ⟨8, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.AddSubCached.native.basePorts8, Airbender.Compiler.FunctionalNative.AddSubCached.native.baseRelation8] using item

theorem baseFacts9 : Airbender.Compiler.FunctionalNative.AddSubCached.native.basePorts9 = true ∧ Airbender.Compiler.FunctionalNative.AddSubCached.native.baseRelation9 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.AddSubCached.native.baseRecipe9 Airbender.Compiler.FunctionalNative.AddSubCached.native.baseOutput9 Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank Airbender.Compiler.FunctionalNative.AddSubCached.native.isBase Airbender.Compiler.FullArithmeticNative.AddSubCached.native.gate39.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨9, by decide +kernel⟩) (List.get_mem originalEntries ⟨9, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.AddSubCached.native.basePorts9, Airbender.Compiler.FunctionalNative.AddSubCached.native.baseRelation9] using item

end Airbender.Compiler.FunctionalBaseChecks.AddSubCached
