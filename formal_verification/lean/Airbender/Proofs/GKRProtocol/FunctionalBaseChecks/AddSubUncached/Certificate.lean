import Airbender.Proofs.GKRProtocol.FunctionalBaseChecks.AddSubUncached.Bindings

namespace Airbender.Compiler.FunctionalBaseChecks.AddSubUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=
  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked

theorem baseFacts0 : Airbender.Compiler.FunctionalNative.AddSubUncached.native.basePorts0 = true ∧ Airbender.Compiler.FunctionalNative.AddSubUncached.native.baseRelation0 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.AddSubUncached.native.baseRecipe0 Airbender.Compiler.FunctionalNative.AddSubUncached.native.baseOutput0 Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank Airbender.Compiler.FunctionalNative.AddSubUncached.native.isBase Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.gate0.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨0, by decide +kernel⟩) (List.get_mem originalEntries ⟨0, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.AddSubUncached.native.basePorts0, Airbender.Compiler.FunctionalNative.AddSubUncached.native.baseRelation0] using item

theorem baseFacts1 : Airbender.Compiler.FunctionalNative.AddSubUncached.native.basePorts1 = true ∧ Airbender.Compiler.FunctionalNative.AddSubUncached.native.baseRelation1 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.AddSubUncached.native.baseRecipe1 Airbender.Compiler.FunctionalNative.AddSubUncached.native.baseOutput1 Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank Airbender.Compiler.FunctionalNative.AddSubUncached.native.isBase Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.gate1.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨1, by decide +kernel⟩) (List.get_mem originalEntries ⟨1, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.AddSubUncached.native.basePorts1, Airbender.Compiler.FunctionalNative.AddSubUncached.native.baseRelation1] using item

theorem baseFacts2 : Airbender.Compiler.FunctionalNative.AddSubUncached.native.basePorts2 = true ∧ Airbender.Compiler.FunctionalNative.AddSubUncached.native.baseRelation2 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.AddSubUncached.native.baseRecipe2 Airbender.Compiler.FunctionalNative.AddSubUncached.native.baseOutput2 Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank Airbender.Compiler.FunctionalNative.AddSubUncached.native.isBase Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.gate2.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨2, by decide +kernel⟩) (List.get_mem originalEntries ⟨2, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.AddSubUncached.native.basePorts2, Airbender.Compiler.FunctionalNative.AddSubUncached.native.baseRelation2] using item

theorem baseFacts3 : Airbender.Compiler.FunctionalNative.AddSubUncached.native.basePorts3 = true ∧ Airbender.Compiler.FunctionalNative.AddSubUncached.native.baseRelation3 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.AddSubUncached.native.baseRecipe3 Airbender.Compiler.FunctionalNative.AddSubUncached.native.baseOutput3 Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank Airbender.Compiler.FunctionalNative.AddSubUncached.native.isBase Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.gate33.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨3, by decide +kernel⟩) (List.get_mem originalEntries ⟨3, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.AddSubUncached.native.basePorts3, Airbender.Compiler.FunctionalNative.AddSubUncached.native.baseRelation3] using item

end Airbender.Compiler.FunctionalBaseChecks.AddSubUncached
