import Airbender.Proofs.GKRProtocol.FunctionalBaseChecks.BigintUncached.Bindings

namespace Airbender.Compiler.FunctionalBaseChecks.BigintUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=
  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked

theorem baseFacts0 : Airbender.Compiler.FunctionalNative.BigintUncached.native.basePorts0 = true ∧ Airbender.Compiler.FunctionalNative.BigintUncached.native.baseRelation0 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintUncached.native.baseRecipe0 Airbender.Compiler.FunctionalNative.BigintUncached.native.baseOutput0 Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.FunctionalNative.BigintUncached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintUncached.native.gate0.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨0, by decide +kernel⟩) (List.get_mem originalEntries ⟨0, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintUncached.native.basePorts0, Airbender.Compiler.FunctionalNative.BigintUncached.native.baseRelation0] using item

theorem baseFacts1 : Airbender.Compiler.FunctionalNative.BigintUncached.native.basePorts1 = true ∧ Airbender.Compiler.FunctionalNative.BigintUncached.native.baseRelation1 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintUncached.native.baseRecipe1 Airbender.Compiler.FunctionalNative.BigintUncached.native.baseOutput1 Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.FunctionalNative.BigintUncached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintUncached.native.gate18.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨1, by decide +kernel⟩) (List.get_mem originalEntries ⟨1, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintUncached.native.basePorts1, Airbender.Compiler.FunctionalNative.BigintUncached.native.baseRelation1] using item

theorem baseFacts2 : Airbender.Compiler.FunctionalNative.BigintUncached.native.basePorts2 = true ∧ Airbender.Compiler.FunctionalNative.BigintUncached.native.baseRelation2 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintUncached.native.baseRecipe2 Airbender.Compiler.FunctionalNative.BigintUncached.native.baseOutput2 Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.FunctionalNative.BigintUncached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintUncached.native.gate19.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨2, by decide +kernel⟩) (List.get_mem originalEntries ⟨2, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintUncached.native.basePorts2, Airbender.Compiler.FunctionalNative.BigintUncached.native.baseRelation2] using item

theorem baseFacts3 : Airbender.Compiler.FunctionalNative.BigintUncached.native.basePorts3 = true ∧ Airbender.Compiler.FunctionalNative.BigintUncached.native.baseRelation3 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintUncached.native.baseRecipe3 Airbender.Compiler.FunctionalNative.BigintUncached.native.baseOutput3 Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.FunctionalNative.BigintUncached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintUncached.native.gate20.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨3, by decide +kernel⟩) (List.get_mem originalEntries ⟨3, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintUncached.native.basePorts3, Airbender.Compiler.FunctionalNative.BigintUncached.native.baseRelation3] using item

theorem baseFacts4 : Airbender.Compiler.FunctionalNative.BigintUncached.native.basePorts4 = true ∧ Airbender.Compiler.FunctionalNative.BigintUncached.native.baseRelation4 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintUncached.native.baseRecipe4 Airbender.Compiler.FunctionalNative.BigintUncached.native.baseOutput4 Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.FunctionalNative.BigintUncached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintUncached.native.gate135.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨4, by decide +kernel⟩) (List.get_mem originalEntries ⟨4, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintUncached.native.basePorts4, Airbender.Compiler.FunctionalNative.BigintUncached.native.baseRelation4] using item

theorem baseFacts5 : Airbender.Compiler.FunctionalNative.BigintUncached.native.basePorts5 = true ∧ Airbender.Compiler.FunctionalNative.BigintUncached.native.baseRelation5 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintUncached.native.baseRecipe5 Airbender.Compiler.FunctionalNative.BigintUncached.native.baseOutput5 Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.FunctionalNative.BigintUncached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintUncached.native.gate138.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨5, by decide +kernel⟩) (List.get_mem originalEntries ⟨5, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintUncached.native.basePorts5, Airbender.Compiler.FunctionalNative.BigintUncached.native.baseRelation5] using item

theorem baseFacts6 : Airbender.Compiler.FunctionalNative.BigintUncached.native.basePorts6 = true ∧ Airbender.Compiler.FunctionalNative.BigintUncached.native.baseRelation6 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintUncached.native.baseRecipe6 Airbender.Compiler.FunctionalNative.BigintUncached.native.baseOutput6 Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.FunctionalNative.BigintUncached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintUncached.native.gate139.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨6, by decide +kernel⟩) (List.get_mem originalEntries ⟨6, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintUncached.native.basePorts6, Airbender.Compiler.FunctionalNative.BigintUncached.native.baseRelation6] using item

theorem baseFacts7 : Airbender.Compiler.FunctionalNative.BigintUncached.native.basePorts7 = true ∧ Airbender.Compiler.FunctionalNative.BigintUncached.native.baseRelation7 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintUncached.native.baseRecipe7 Airbender.Compiler.FunctionalNative.BigintUncached.native.baseOutput7 Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.FunctionalNative.BigintUncached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintUncached.native.gate140.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨7, by decide +kernel⟩) (List.get_mem originalEntries ⟨7, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintUncached.native.basePorts7, Airbender.Compiler.FunctionalNative.BigintUncached.native.baseRelation7] using item

end Airbender.Compiler.FunctionalBaseChecks.BigintUncached
