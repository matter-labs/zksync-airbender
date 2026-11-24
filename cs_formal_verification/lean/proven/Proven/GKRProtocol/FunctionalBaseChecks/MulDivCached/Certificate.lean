module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FunctionalBaseChecks.MulDivCached.Bindings

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FunctionalBaseChecks.MulDivCached
open Airbender.Compiler
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=
  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked

theorem baseFacts0 : Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts0 = true ∧ Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation0 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRecipe0 Airbender.Compiler.FunctionalNative.MulDivCached.native.baseOutput0 Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank Airbender.Compiler.FunctionalNative.MulDivCached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate0.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨0, by decide +kernel⟩) (List.get_mem originalEntries ⟨0, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts0, Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation0] using item

theorem baseFacts1 : Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts1 = true ∧ Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation1 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRecipe1 Airbender.Compiler.FunctionalNative.MulDivCached.native.baseOutput1 Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank Airbender.Compiler.FunctionalNative.MulDivCached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate1.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨1, by decide +kernel⟩) (List.get_mem originalEntries ⟨1, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts1, Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation1] using item

theorem baseFacts2 : Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts2 = true ∧ Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation2 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRecipe2 Airbender.Compiler.FunctionalNative.MulDivCached.native.baseOutput2 Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank Airbender.Compiler.FunctionalNative.MulDivCached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate2.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨2, by decide +kernel⟩) (List.get_mem originalEntries ⟨2, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts2, Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation2] using item

theorem baseFacts3 : Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts3 = true ∧ Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation3 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRecipe3 Airbender.Compiler.FunctionalNative.MulDivCached.native.baseOutput3 Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank Airbender.Compiler.FunctionalNative.MulDivCached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate3.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨3, by decide +kernel⟩) (List.get_mem originalEntries ⟨3, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts3, Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation3] using item

theorem baseFacts4 : Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts4 = true ∧ Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation4 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRecipe4 Airbender.Compiler.FunctionalNative.MulDivCached.native.baseOutput4 Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank Airbender.Compiler.FunctionalNative.MulDivCached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate4.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨4, by decide +kernel⟩) (List.get_mem originalEntries ⟨4, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts4, Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation4] using item

theorem baseFacts5 : Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts5 = true ∧ Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation5 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRecipe5 Airbender.Compiler.FunctionalNative.MulDivCached.native.baseOutput5 Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank Airbender.Compiler.FunctionalNative.MulDivCached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate5.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨5, by decide +kernel⟩) (List.get_mem originalEntries ⟨5, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts5, Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation5] using item

theorem baseFacts6 : Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts6 = true ∧ Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation6 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRecipe6 Airbender.Compiler.FunctionalNative.MulDivCached.native.baseOutput6 Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank Airbender.Compiler.FunctionalNative.MulDivCached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate6.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨6, by decide +kernel⟩) (List.get_mem originalEntries ⟨6, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts6, Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation6] using item

theorem baseFacts7 : Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts7 = true ∧ Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation7 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRecipe7 Airbender.Compiler.FunctionalNative.MulDivCached.native.baseOutput7 Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank Airbender.Compiler.FunctionalNative.MulDivCached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate19.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨7, by decide +kernel⟩) (List.get_mem originalEntries ⟨7, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts7, Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation7] using item

theorem baseFacts8 : Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts8 = true ∧ Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation8 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRecipe8 Airbender.Compiler.FunctionalNative.MulDivCached.native.baseOutput8 Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank Airbender.Compiler.FunctionalNative.MulDivCached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate20.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨8, by decide +kernel⟩) (List.get_mem originalEntries ⟨8, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts8, Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation8] using item

theorem baseFacts9 : Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts9 = true ∧ Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation9 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRecipe9 Airbender.Compiler.FunctionalNative.MulDivCached.native.baseOutput9 Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank Airbender.Compiler.FunctionalNative.MulDivCached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate21.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨9, by decide +kernel⟩) (List.get_mem originalEntries ⟨9, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts9, Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation9] using item

theorem baseFacts10 : Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts10 = true ∧ Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation10 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRecipe10 Airbender.Compiler.FunctionalNative.MulDivCached.native.baseOutput10 Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank Airbender.Compiler.FunctionalNative.MulDivCached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate22.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨10, by decide +kernel⟩) (List.get_mem originalEntries ⟨10, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts10, Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation10] using item

theorem baseFacts11 : Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts11 = true ∧ Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation11 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRecipe11 Airbender.Compiler.FunctionalNative.MulDivCached.native.baseOutput11 Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank Airbender.Compiler.FunctionalNative.MulDivCached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate23.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨11, by decide +kernel⟩) (List.get_mem originalEntries ⟨11, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts11, Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation11] using item

theorem baseFacts12 : Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts12 = true ∧ Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation12 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRecipe12 Airbender.Compiler.FunctionalNative.MulDivCached.native.baseOutput12 Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank Airbender.Compiler.FunctionalNative.MulDivCached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate24.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨12, by decide +kernel⟩) (List.get_mem originalEntries ⟨12, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts12, Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation12] using item

theorem baseFacts13 : Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts13 = true ∧ Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation13 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRecipe13 Airbender.Compiler.FunctionalNative.MulDivCached.native.baseOutput13 Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank Airbender.Compiler.FunctionalNative.MulDivCached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate25.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨13, by decide +kernel⟩) (List.get_mem originalEntries ⟨13, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts13, Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation13] using item

theorem baseFacts14 : Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts14 = true ∧ Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation14 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRecipe14 Airbender.Compiler.FunctionalNative.MulDivCached.native.baseOutput14 Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank Airbender.Compiler.FunctionalNative.MulDivCached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate26.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨14, by decide +kernel⟩) (List.get_mem originalEntries ⟨14, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts14, Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation14] using item

theorem baseFacts15 : Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts15 = true ∧ Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation15 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRecipe15 Airbender.Compiler.FunctionalNative.MulDivCached.native.baseOutput15 Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank Airbender.Compiler.FunctionalNative.MulDivCached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate27.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨15, by decide +kernel⟩) (List.get_mem originalEntries ⟨15, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts15, Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation15] using item

theorem baseFacts16 : Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts16 = true ∧ Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation16 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRecipe16 Airbender.Compiler.FunctionalNative.MulDivCached.native.baseOutput16 Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank Airbender.Compiler.FunctionalNative.MulDivCached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate28.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨16, by decide +kernel⟩) (List.get_mem originalEntries ⟨16, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts16, Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation16] using item

theorem baseFacts17 : Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts17 = true ∧ Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation17 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRecipe17 Airbender.Compiler.FunctionalNative.MulDivCached.native.baseOutput17 Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank Airbender.Compiler.FunctionalNative.MulDivCached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate29.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨17, by decide +kernel⟩) (List.get_mem originalEntries ⟨17, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts17, Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation17] using item

theorem baseFacts18 : Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts18 = true ∧ Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation18 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRecipe18 Airbender.Compiler.FunctionalNative.MulDivCached.native.baseOutput18 Airbender.Compiler.FullArithmeticNative.MulDivCached.native.bank Airbender.Compiler.FunctionalNative.MulDivCached.native.isBase Airbender.Compiler.FullArithmeticNative.MulDivCached.native.gate42.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨18, by decide +kernel⟩) (List.get_mem originalEntries ⟨18, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.MulDivCached.native.basePorts18, Airbender.Compiler.FunctionalNative.MulDivCached.native.baseRelation18] using item

end Airbender.Compiler.FunctionalBaseChecks.MulDivCached
