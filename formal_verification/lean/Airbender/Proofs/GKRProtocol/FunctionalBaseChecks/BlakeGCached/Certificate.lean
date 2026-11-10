import Airbender.Proofs.GKRProtocol.FunctionalBaseChecks.BlakeGCached.Bindings

namespace Airbender.Compiler.FunctionalBaseChecks.BlakeGCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=
  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked

theorem baseFacts0 : Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts0 = true ∧ Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation0 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRecipe0 Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseOutput0 Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.FunctionalNative.BlakeGCached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate0.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨0, by decide +kernel⟩) (List.get_mem originalEntries ⟨0, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts0, Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation0] using item

theorem baseFacts1 : Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts1 = true ∧ Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation1 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRecipe1 Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseOutput1 Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.FunctionalNative.BlakeGCached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate1.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨1, by decide +kernel⟩) (List.get_mem originalEntries ⟨1, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts1, Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation1] using item

theorem baseFacts2 : Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts2 = true ∧ Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation2 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRecipe2 Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseOutput2 Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.FunctionalNative.BlakeGCached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate2.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨2, by decide +kernel⟩) (List.get_mem originalEntries ⟨2, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts2, Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation2] using item

theorem baseFacts3 : Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts3 = true ∧ Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation3 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRecipe3 Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseOutput3 Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.FunctionalNative.BlakeGCached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate3.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨3, by decide +kernel⟩) (List.get_mem originalEntries ⟨3, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts3, Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation3] using item

theorem baseFacts4 : Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts4 = true ∧ Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation4 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRecipe4 Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseOutput4 Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.FunctionalNative.BlakeGCached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate4.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨4, by decide +kernel⟩) (List.get_mem originalEntries ⟨4, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts4, Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation4] using item

theorem baseFacts5 : Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts5 = true ∧ Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation5 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRecipe5 Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseOutput5 Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.FunctionalNative.BlakeGCached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate5.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨5, by decide +kernel⟩) (List.get_mem originalEntries ⟨5, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts5, Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation5] using item

theorem baseFacts6 : Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts6 = true ∧ Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation6 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRecipe6 Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseOutput6 Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.FunctionalNative.BlakeGCached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate6.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨6, by decide +kernel⟩) (List.get_mem originalEntries ⟨6, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts6, Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation6] using item

theorem baseFacts7 : Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts7 = true ∧ Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation7 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRecipe7 Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseOutput7 Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.FunctionalNative.BlakeGCached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate7.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨7, by decide +kernel⟩) (List.get_mem originalEntries ⟨7, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts7, Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation7] using item

theorem baseFacts8 : Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts8 = true ∧ Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation8 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRecipe8 Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseOutput8 Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.FunctionalNative.BlakeGCached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate8.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨8, by decide +kernel⟩) (List.get_mem originalEntries ⟨8, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts8, Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation8] using item

theorem baseFacts9 : Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts9 = true ∧ Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation9 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRecipe9 Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseOutput9 Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.FunctionalNative.BlakeGCached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate9.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨9, by decide +kernel⟩) (List.get_mem originalEntries ⟨9, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts9, Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation9] using item

theorem baseFacts10 : Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts10 = true ∧ Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation10 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRecipe10 Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseOutput10 Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.FunctionalNative.BlakeGCached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate10.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨10, by decide +kernel⟩) (List.get_mem originalEntries ⟨10, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts10, Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation10] using item

theorem baseFacts11 : Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts11 = true ∧ Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation11 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRecipe11 Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseOutput11 Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.FunctionalNative.BlakeGCached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate11.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨11, by decide +kernel⟩) (List.get_mem originalEntries ⟨11, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts11, Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation11] using item

theorem baseFacts12 : Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts12 = true ∧ Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation12 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRecipe12 Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseOutput12 Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.FunctionalNative.BlakeGCached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate12.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨12, by decide +kernel⟩) (List.get_mem originalEntries ⟨12, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts12, Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation12] using item

theorem baseFacts13 : Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts13 = true ∧ Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation13 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRecipe13 Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseOutput13 Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.FunctionalNative.BlakeGCached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate13.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨13, by decide +kernel⟩) (List.get_mem originalEntries ⟨13, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts13, Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation13] using item

theorem baseFacts14 : Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts14 = true ∧ Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation14 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRecipe14 Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseOutput14 Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.FunctionalNative.BlakeGCached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate14.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨14, by decide +kernel⟩) (List.get_mem originalEntries ⟨14, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts14, Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation14] using item

theorem baseFacts15 : Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts15 = true ∧ Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation15 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRecipe15 Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseOutput15 Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.FunctionalNative.BlakeGCached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate15.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨15, by decide +kernel⟩) (List.get_mem originalEntries ⟨15, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts15, Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation15] using item

theorem baseFacts16 : Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts16 = true ∧ Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation16 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRecipe16 Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseOutput16 Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.FunctionalNative.BlakeGCached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate16.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨16, by decide +kernel⟩) (List.get_mem originalEntries ⟨16, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts16, Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation16] using item

theorem baseFacts17 : Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts17 = true ∧ Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation17 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRecipe17 Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseOutput17 Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.FunctionalNative.BlakeGCached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate17.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨17, by decide +kernel⟩) (List.get_mem originalEntries ⟨17, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts17, Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation17] using item

theorem baseFacts18 : Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts18 = true ∧ Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation18 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRecipe18 Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseOutput18 Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.FunctionalNative.BlakeGCached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate18.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨18, by decide +kernel⟩) (List.get_mem originalEntries ⟨18, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts18, Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation18] using item

theorem baseFacts19 : Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts19 = true ∧ Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation19 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRecipe19 Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseOutput19 Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.FunctionalNative.BlakeGCached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate19.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨19, by decide +kernel⟩) (List.get_mem originalEntries ⟨19, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts19, Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation19] using item

theorem baseFacts20 : Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts20 = true ∧ Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation20 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRecipe20 Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseOutput20 Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.FunctionalNative.BlakeGCached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate20.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨20, by decide +kernel⟩) (List.get_mem originalEntries ⟨20, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts20, Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation20] using item

theorem baseFacts21 : Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts21 = true ∧ Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation21 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRecipe21 Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseOutput21 Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.FunctionalNative.BlakeGCached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate21.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨21, by decide +kernel⟩) (List.get_mem originalEntries ⟨21, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts21, Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation21] using item

theorem baseFacts22 : Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts22 = true ∧ Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation22 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRecipe22 Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseOutput22 Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.FunctionalNative.BlakeGCached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate54.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨22, by decide +kernel⟩) (List.get_mem originalEntries ⟨22, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts22, Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation22] using item

theorem baseFacts23 : Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts23 = true ∧ Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation23 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRecipe23 Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseOutput23 Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.FunctionalNative.BlakeGCached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate55.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨23, by decide +kernel⟩) (List.get_mem originalEntries ⟨23, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts23, Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation23] using item

theorem baseFacts24 : Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts24 = true ∧ Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation24 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRecipe24 Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseOutput24 Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.FunctionalNative.BlakeGCached.native.isBase Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.gate56.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨24, by decide +kernel⟩) (List.get_mem originalEntries ⟨24, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BlakeGCached.native.basePorts24, Airbender.Compiler.FunctionalNative.BlakeGCached.native.baseRelation24] using item

end Airbender.Compiler.FunctionalBaseChecks.BlakeGCached
