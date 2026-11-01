import Airbender.Proofs.GKRProtocol.FunctionalBaseChecks.MulDivUncached.Bindings

namespace Airbender.Compiler.FunctionalBaseChecks.MulDivUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=
  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked

theorem baseFacts0 : Airbender.Compiler.FunctionalNative.MulDivUncached.native.basePorts0 = true ∧ Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRelation0 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRecipe0 Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseOutput0 Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank Airbender.Compiler.FunctionalNative.MulDivUncached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.gate0.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨0, by decide +kernel⟩) (List.get_mem originalEntries ⟨0, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivUncached.native.basePorts0, Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRelation0] using item

theorem baseFacts1 : Airbender.Compiler.FunctionalNative.MulDivUncached.native.basePorts1 = true ∧ Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRelation1 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRecipe1 Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseOutput1 Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank Airbender.Compiler.FunctionalNative.MulDivUncached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.gate13.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨1, by decide +kernel⟩) (List.get_mem originalEntries ⟨1, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivUncached.native.basePorts1, Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRelation1] using item

theorem baseFacts2 : Airbender.Compiler.FunctionalNative.MulDivUncached.native.basePorts2 = true ∧ Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRelation2 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRecipe2 Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseOutput2 Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank Airbender.Compiler.FunctionalNative.MulDivUncached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.gate14.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨2, by decide +kernel⟩) (List.get_mem originalEntries ⟨2, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivUncached.native.basePorts2, Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRelation2] using item

theorem baseFacts3 : Airbender.Compiler.FunctionalNative.MulDivUncached.native.basePorts3 = true ∧ Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRelation3 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRecipe3 Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseOutput3 Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank Airbender.Compiler.FunctionalNative.MulDivUncached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.gate15.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨3, by decide +kernel⟩) (List.get_mem originalEntries ⟨3, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivUncached.native.basePorts3, Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRelation3] using item

theorem baseFacts4 : Airbender.Compiler.FunctionalNative.MulDivUncached.native.basePorts4 = true ∧ Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRelation4 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRecipe4 Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseOutput4 Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank Airbender.Compiler.FunctionalNative.MulDivUncached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.gate16.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨4, by decide +kernel⟩) (List.get_mem originalEntries ⟨4, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivUncached.native.basePorts4, Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRelation4] using item

theorem baseFacts5 : Airbender.Compiler.FunctionalNative.MulDivUncached.native.basePorts5 = true ∧ Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRelation5 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRecipe5 Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseOutput5 Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank Airbender.Compiler.FunctionalNative.MulDivUncached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.gate17.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨5, by decide +kernel⟩) (List.get_mem originalEntries ⟨5, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivUncached.native.basePorts5, Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRelation5] using item

theorem baseFacts6 : Airbender.Compiler.FunctionalNative.MulDivUncached.native.basePorts6 = true ∧ Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRelation6 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRecipe6 Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseOutput6 Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank Airbender.Compiler.FunctionalNative.MulDivUncached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.gate18.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨6, by decide +kernel⟩) (List.get_mem originalEntries ⟨6, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivUncached.native.basePorts6, Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRelation6] using item

theorem baseFacts7 : Airbender.Compiler.FunctionalNative.MulDivUncached.native.basePorts7 = true ∧ Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRelation7 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRecipe7 Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseOutput7 Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank Airbender.Compiler.FunctionalNative.MulDivUncached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.gate19.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨7, by decide +kernel⟩) (List.get_mem originalEntries ⟨7, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivUncached.native.basePorts7, Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRelation7] using item

theorem baseFacts8 : Airbender.Compiler.FunctionalNative.MulDivUncached.native.basePorts8 = true ∧ Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRelation8 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRecipe8 Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseOutput8 Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank Airbender.Compiler.FunctionalNative.MulDivUncached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.gate20.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨8, by decide +kernel⟩) (List.get_mem originalEntries ⟨8, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivUncached.native.basePorts8, Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRelation8] using item

theorem baseFacts9 : Airbender.Compiler.FunctionalNative.MulDivUncached.native.basePorts9 = true ∧ Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRelation9 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRecipe9 Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseOutput9 Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank Airbender.Compiler.FunctionalNative.MulDivUncached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.gate21.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨9, by decide +kernel⟩) (List.get_mem originalEntries ⟨9, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivUncached.native.basePorts9, Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRelation9] using item

theorem baseFacts10 : Airbender.Compiler.FunctionalNative.MulDivUncached.native.basePorts10 = true ∧ Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRelation10 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRecipe10 Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseOutput10 Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank Airbender.Compiler.FunctionalNative.MulDivUncached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.gate22.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨10, by decide +kernel⟩) (List.get_mem originalEntries ⟨10, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivUncached.native.basePorts10, Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRelation10] using item

theorem baseFacts11 : Airbender.Compiler.FunctionalNative.MulDivUncached.native.basePorts11 = true ∧ Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRelation11 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRecipe11 Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseOutput11 Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank Airbender.Compiler.FunctionalNative.MulDivUncached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.gate23.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨11, by decide +kernel⟩) (List.get_mem originalEntries ⟨11, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivUncached.native.basePorts11, Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRelation11] using item

theorem baseFacts12 : Airbender.Compiler.FunctionalNative.MulDivUncached.native.basePorts12 = true ∧ Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRelation12 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRecipe12 Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseOutput12 Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.bank Airbender.Compiler.FunctionalNative.MulDivUncached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivUncached.native.gate36.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨12, by decide +kernel⟩) (List.get_mem originalEntries ⟨12, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivUncached.native.basePorts12, Airbender.Compiler.FunctionalNative.MulDivUncached.native.baseRelation12] using item

end Airbender.Compiler.FunctionalBaseChecks.MulDivUncached
