module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FunctionalBaseChecks.SubwordMemoryCached.Bindings

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FunctionalBaseChecks.SubwordMemoryCached
open Airbender.Compiler
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=
  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked

theorem baseFacts0 : Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.basePorts0 = true ∧ Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRelation0 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRecipe0 Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseOutput0 Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.isBase Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate0.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨0, by decide +kernel⟩) (List.get_mem originalEntries ⟨0, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.basePorts0, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRelation0] using item

theorem baseFacts1 : Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.basePorts1 = true ∧ Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRelation1 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRecipe1 Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseOutput1 Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.isBase Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate1.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨1, by decide +kernel⟩) (List.get_mem originalEntries ⟨1, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.basePorts1, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRelation1] using item

theorem baseFacts2 : Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.basePorts2 = true ∧ Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRelation2 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRecipe2 Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseOutput2 Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.isBase Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate2.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨2, by decide +kernel⟩) (List.get_mem originalEntries ⟨2, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.basePorts2, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRelation2] using item

theorem baseFacts3 : Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.basePorts3 = true ∧ Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRelation3 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRecipe3 Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseOutput3 Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.isBase Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate3.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨3, by decide +kernel⟩) (List.get_mem originalEntries ⟨3, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.basePorts3, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRelation3] using item

theorem baseFacts4 : Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.basePorts4 = true ∧ Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRelation4 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRecipe4 Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseOutput4 Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.isBase Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate4.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨4, by decide +kernel⟩) (List.get_mem originalEntries ⟨4, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.basePorts4, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRelation4] using item

theorem baseFacts5 : Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.basePorts5 = true ∧ Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRelation5 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRecipe5 Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseOutput5 Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.isBase Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate5.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨5, by decide +kernel⟩) (List.get_mem originalEntries ⟨5, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.basePorts5, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRelation5] using item

theorem baseFacts6 : Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.basePorts6 = true ∧ Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRelation6 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRecipe6 Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseOutput6 Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.isBase Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate6.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨6, by decide +kernel⟩) (List.get_mem originalEntries ⟨6, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.basePorts6, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRelation6] using item

theorem baseFacts7 : Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.basePorts7 = true ∧ Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRelation7 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRecipe7 Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseOutput7 Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.isBase Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate12.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨7, by decide +kernel⟩) (List.get_mem originalEntries ⟨7, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.basePorts7, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRelation7] using item

theorem baseFacts8 : Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.basePorts8 = true ∧ Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRelation8 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRecipe8 Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseOutput8 Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.isBase Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate13.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨8, by decide +kernel⟩) (List.get_mem originalEntries ⟨8, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.basePorts8, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRelation8] using item

theorem baseFacts9 : Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.basePorts9 = true ∧ Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRelation9 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRecipe9 Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseOutput9 Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.isBase Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate15.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨9, by decide +kernel⟩) (List.get_mem originalEntries ⟨9, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.basePorts9, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRelation9] using item

theorem baseFacts10 : Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.basePorts10 = true ∧ Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRelation10 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRecipe10 Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseOutput10 Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.isBase Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate19.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨10, by decide +kernel⟩) (List.get_mem originalEntries ⟨10, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.basePorts10, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRelation10] using item

theorem baseFacts11 : Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.basePorts11 = true ∧ Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRelation11 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRecipe11 Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseOutput11 Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.isBase Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate21.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨11, by decide +kernel⟩) (List.get_mem originalEntries ⟨11, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.basePorts11, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRelation11] using item

theorem baseFacts12 : Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.basePorts12 = true ∧ Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRelation12 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRecipe12 Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseOutput12 Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.isBase Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate24.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨12, by decide +kernel⟩) (List.get_mem originalEntries ⟨12, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.basePorts12, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRelation12] using item

theorem baseFacts13 : Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.basePorts13 = true ∧ Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRelation13 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRecipe13 Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseOutput13 Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.isBase Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate25.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨13, by decide +kernel⟩) (List.get_mem originalEntries ⟨13, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.basePorts13, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRelation13] using item

theorem baseFacts14 : Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.basePorts14 = true ∧ Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRelation14 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRecipe14 Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseOutput14 Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.bank Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.isBase Airbender.Compiler.FullArithmeticNative.SubwordMemoryCached.native.gate49.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨14, by decide +kernel⟩) (List.get_mem originalEntries ⟨14, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.basePorts14, Airbender.Compiler.FunctionalNative.SubwordMemoryCached.native.baseRelation14] using item

end Airbender.Compiler.FunctionalBaseChecks.SubwordMemoryCached
