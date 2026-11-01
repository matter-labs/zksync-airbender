import Airbender.Proofs.GKRProtocol.FunctionalBaseChecks.JumpBranchUncached.Bindings

namespace Airbender.Compiler.FunctionalBaseChecks.JumpBranchUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=
  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked

theorem baseFacts0 : Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.basePorts0 = true ∧ Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.baseRelation0 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.baseRecipe0 Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.baseOutput0 Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.isBase Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.gate0.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨0, by decide +kernel⟩) (List.get_mem originalEntries ⟨0, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.basePorts0, Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.baseRelation0] using item

theorem baseFacts1 : Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.basePorts1 = true ∧ Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.baseRelation1 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.baseRecipe1 Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.baseOutput1 Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.isBase Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.gate1.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨1, by decide +kernel⟩) (List.get_mem originalEntries ⟨1, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.basePorts1, Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.baseRelation1] using item

theorem baseFacts2 : Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.basePorts2 = true ∧ Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.baseRelation2 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.baseRecipe2 Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.baseOutput2 Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.isBase Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.gate2.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨2, by decide +kernel⟩) (List.get_mem originalEntries ⟨2, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.basePorts2, Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.baseRelation2] using item

theorem baseFacts3 : Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.basePorts3 = true ∧ Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.baseRelation3 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.baseRecipe3 Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.baseOutput3 Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.bank Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.isBase Airbender.Compiler.FullArithmeticNative.JumpBranchUncached.native.gate29.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨3, by decide +kernel⟩) (List.get_mem originalEntries ⟨3, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.basePorts3, Airbender.Compiler.FunctionalNative.JumpBranchUncached.native.baseRelation3] using item

end Airbender.Compiler.FunctionalBaseChecks.JumpBranchUncached
