import Airbender.Proofs.GKRProtocol.FunctionalBaseChecks.BlakeRoundUncached.Bindings

namespace Airbender.Compiler.FunctionalBaseChecks.BlakeRoundUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=
  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked

theorem baseFacts0 : Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.basePorts0 = true ∧ Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.baseRelation0 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.baseRecipe0 Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.baseOutput0 Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.gate0.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨0, by decide +kernel⟩) (List.get_mem originalEntries ⟨0, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.basePorts0, Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.baseRelation0] using item

theorem baseFacts1 : Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.basePorts1 = true ∧ Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.baseRelation1 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.baseRecipe1 Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.baseOutput1 Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.gate221.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨1, by decide +kernel⟩) (List.get_mem originalEntries ⟨1, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.basePorts1, Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.baseRelation1] using item

theorem baseFacts2 : Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.basePorts2 = true ∧ Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.baseRelation2 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.baseRecipe2 Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.baseOutput2 Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.gate222.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨2, by decide +kernel⟩) (List.get_mem originalEntries ⟨2, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.basePorts2, Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.baseRelation2] using item

theorem baseFacts3 : Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.basePorts3 = true ∧ Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.baseRelation3 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.baseRecipe3 Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.baseOutput3 Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.gate223.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨3, by decide +kernel⟩) (List.get_mem originalEntries ⟨3, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.basePorts3, Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.baseRelation3] using item

theorem baseFacts4 : Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.basePorts4 = true ∧ Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.baseRelation4 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.baseRecipe4 Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.baseOutput4 Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.gate224.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨4, by decide +kernel⟩) (List.get_mem originalEntries ⟨4, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.basePorts4, Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.baseRelation4] using item

theorem baseFacts5 : Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.basePorts5 = true ∧ Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.baseRelation5 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.baseRecipe5 Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.baseOutput5 Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.gate225.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨5, by decide +kernel⟩) (List.get_mem originalEntries ⟨5, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.basePorts5, Airbender.Compiler.FunctionalNative.BlakeRoundUncached.native.baseRelation5] using item

end Airbender.Compiler.FunctionalBaseChecks.BlakeRoundUncached
