import Airbender.Proofs.GKRProtocol.FunctionalBaseChecks.BlakeGUncached.Bindings

namespace Airbender.Compiler.FunctionalBaseChecks.BlakeGUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=
  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked

theorem baseFacts0 : Airbender.Compiler.FunctionalNative.BlakeGUncached.native.basePorts0 = true ∧ Airbender.Compiler.FunctionalNative.BlakeGUncached.native.baseRelation0 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeGUncached.native.baseRecipe0 Airbender.Compiler.FunctionalNative.BlakeGUncached.native.baseOutput0 Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bank Airbender.Compiler.FunctionalNative.BlakeGUncached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.gate0.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨0, by decide +kernel⟩) (List.get_mem originalEntries ⟨0, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeGUncached.native.basePorts0, Airbender.Compiler.FunctionalNative.BlakeGUncached.native.baseRelation0] using item

theorem baseFacts1 : Airbender.Compiler.FunctionalNative.BlakeGUncached.native.basePorts1 = true ∧ Airbender.Compiler.FunctionalNative.BlakeGUncached.native.baseRelation1 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeGUncached.native.baseRecipe1 Airbender.Compiler.FunctionalNative.BlakeGUncached.native.baseOutput1 Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bank Airbender.Compiler.FunctionalNative.BlakeGUncached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.gate33.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨1, by decide +kernel⟩) (List.get_mem originalEntries ⟨1, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeGUncached.native.basePorts1, Airbender.Compiler.FunctionalNative.BlakeGUncached.native.baseRelation1] using item

theorem baseFacts2 : Airbender.Compiler.FunctionalNative.BlakeGUncached.native.basePorts2 = true ∧ Airbender.Compiler.FunctionalNative.BlakeGUncached.native.baseRelation2 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeGUncached.native.baseRecipe2 Airbender.Compiler.FunctionalNative.BlakeGUncached.native.baseOutput2 Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bank Airbender.Compiler.FunctionalNative.BlakeGUncached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.gate34.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨2, by decide +kernel⟩) (List.get_mem originalEntries ⟨2, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeGUncached.native.basePorts2, Airbender.Compiler.FunctionalNative.BlakeGUncached.native.baseRelation2] using item

theorem baseFacts3 : Airbender.Compiler.FunctionalNative.BlakeGUncached.native.basePorts3 = true ∧ Airbender.Compiler.FunctionalNative.BlakeGUncached.native.baseRelation3 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeGUncached.native.baseRecipe3 Airbender.Compiler.FunctionalNative.BlakeGUncached.native.baseOutput3 Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.bank Airbender.Compiler.FunctionalNative.BlakeGUncached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeGUncached.native.gate35.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨3, by decide +kernel⟩) (List.get_mem originalEntries ⟨3, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeGUncached.native.basePorts3, Airbender.Compiler.FunctionalNative.BlakeGUncached.native.baseRelation3] using item

end Airbender.Compiler.FunctionalBaseChecks.BlakeGUncached
