import Airbender.Proofs.GKRProtocol.FunctionalBaseChecks.BigintCached.Bindings

namespace Airbender.Compiler.FunctionalBaseChecks.BigintCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=
  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked

theorem baseFacts0 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts0 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation0 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe0 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput0 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate0.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨0, by decide +kernel⟩) (List.get_mem originalEntries ⟨0, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts0, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation0] using item

theorem baseFacts1 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts1 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation1 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe1 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput1 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate1.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨1, by decide +kernel⟩) (List.get_mem originalEntries ⟨1, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts1, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation1] using item

theorem baseFacts2 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts2 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation2 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe2 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput2 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate2.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨2, by decide +kernel⟩) (List.get_mem originalEntries ⟨2, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts2, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation2] using item

theorem baseFacts3 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts3 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation3 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe3 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput3 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate3.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨3, by decide +kernel⟩) (List.get_mem originalEntries ⟨3, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts3, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation3] using item

theorem baseFacts4 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts4 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation4 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe4 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput4 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate4.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨4, by decide +kernel⟩) (List.get_mem originalEntries ⟨4, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts4, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation4] using item

theorem baseFacts5 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts5 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation5 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe5 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput5 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate5.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨5, by decide +kernel⟩) (List.get_mem originalEntries ⟨5, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts5, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation5] using item

theorem baseFacts6 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts6 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation6 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe6 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput6 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate6.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨6, by decide +kernel⟩) (List.get_mem originalEntries ⟨6, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts6, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation6] using item

theorem baseFacts7 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts7 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation7 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe7 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput7 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate7.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨7, by decide +kernel⟩) (List.get_mem originalEntries ⟨7, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts7, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation7] using item

theorem baseFacts8 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts8 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation8 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe8 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput8 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate8.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨8, by decide +kernel⟩) (List.get_mem originalEntries ⟨8, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts8, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation8] using item

theorem baseFacts9 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts9 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation9 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe9 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput9 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate9.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨9, by decide +kernel⟩) (List.get_mem originalEntries ⟨9, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts9, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation9] using item

theorem baseFacts10 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts10 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation10 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe10 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput10 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate10.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨10, by decide +kernel⟩) (List.get_mem originalEntries ⟨10, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts10, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation10] using item

theorem baseFacts11 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts11 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation11 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe11 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput11 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate11.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨11, by decide +kernel⟩) (List.get_mem originalEntries ⟨11, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts11, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation11] using item

theorem baseFacts12 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts12 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation12 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe12 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput12 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate12.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨12, by decide +kernel⟩) (List.get_mem originalEntries ⟨12, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts12, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation12] using item

theorem baseFacts13 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts13 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation13 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe13 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput13 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate13.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨13, by decide +kernel⟩) (List.get_mem originalEntries ⟨13, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts13, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation13] using item

theorem baseFacts14 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts14 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation14 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe14 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput14 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate14.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨14, by decide +kernel⟩) (List.get_mem originalEntries ⟨14, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts14, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation14] using item

theorem baseFacts15 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts15 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation15 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe15 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput15 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate15.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨15, by decide +kernel⟩) (List.get_mem originalEntries ⟨15, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts15, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation15] using item

theorem baseFacts16 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts16 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation16 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe16 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput16 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate16.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨16, by decide +kernel⟩) (List.get_mem originalEntries ⟨16, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts16, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation16] using item

theorem baseFacts17 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts17 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation17 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe17 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput17 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate17.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨17, by decide +kernel⟩) (List.get_mem originalEntries ⟨17, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts17, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation17] using item

theorem baseFacts18 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts18 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation18 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe18 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput18 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate18.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨18, by decide +kernel⟩) (List.get_mem originalEntries ⟨18, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts18, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation18] using item

theorem baseFacts19 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts19 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation19 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe19 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput19 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate19.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨19, by decide +kernel⟩) (List.get_mem originalEntries ⟨19, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts19, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation19] using item

theorem baseFacts20 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts20 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation20 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe20 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput20 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate20.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨20, by decide +kernel⟩) (List.get_mem originalEntries ⟨20, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts20, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation20] using item

theorem baseFacts21 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts21 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation21 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe21 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput21 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate21.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨21, by decide +kernel⟩) (List.get_mem originalEntries ⟨21, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts21, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation21] using item

theorem baseFacts22 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts22 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation22 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe22 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput22 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate22.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨22, by decide +kernel⟩) (List.get_mem originalEntries ⟨22, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts22, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation22] using item

theorem baseFacts23 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts23 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation23 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe23 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput23 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate23.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨23, by decide +kernel⟩) (List.get_mem originalEntries ⟨23, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts23, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation23] using item

theorem baseFacts24 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts24 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation24 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe24 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput24 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate24.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨24, by decide +kernel⟩) (List.get_mem originalEntries ⟨24, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts24, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation24] using item

theorem baseFacts25 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts25 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation25 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe25 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput25 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate25.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨25, by decide +kernel⟩) (List.get_mem originalEntries ⟨25, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts25, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation25] using item

theorem baseFacts26 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts26 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation26 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe26 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput26 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate26.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨26, by decide +kernel⟩) (List.get_mem originalEntries ⟨26, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts26, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation26] using item

theorem baseFacts27 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts27 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation27 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe27 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput27 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate27.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨27, by decide +kernel⟩) (List.get_mem originalEntries ⟨27, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts27, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation27] using item

theorem baseFacts28 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts28 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation28 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe28 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput28 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate28.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨28, by decide +kernel⟩) (List.get_mem originalEntries ⟨28, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts28, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation28] using item

theorem baseFacts29 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts29 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation29 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe29 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput29 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate29.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨29, by decide +kernel⟩) (List.get_mem originalEntries ⟨29, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts29, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation29] using item

theorem baseFacts30 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts30 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation30 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe30 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput30 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate30.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨30, by decide +kernel⟩) (List.get_mem originalEntries ⟨30, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts30, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation30] using item

theorem baseFacts31 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts31 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation31 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe31 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput31 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate31.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨31, by decide +kernel⟩) (List.get_mem originalEntries ⟨31, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts31, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation31] using item

theorem baseFacts32 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts32 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation32 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe32 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput32 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate32.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨32, by decide +kernel⟩) (List.get_mem originalEntries ⟨32, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts32, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation32] using item

theorem baseFacts33 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts33 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation33 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe33 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput33 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate33.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨33, by decide +kernel⟩) (List.get_mem originalEntries ⟨33, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts33, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation33] using item

theorem baseFacts34 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts34 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation34 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe34 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput34 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate34.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨34, by decide +kernel⟩) (List.get_mem originalEntries ⟨34, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts34, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation34] using item

theorem baseFacts35 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts35 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation35 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe35 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput35 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate35.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨35, by decide +kernel⟩) (List.get_mem originalEntries ⟨35, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts35, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation35] using item

theorem baseFacts36 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts36 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation36 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe36 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput36 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate36.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨36, by decide +kernel⟩) (List.get_mem originalEntries ⟨36, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts36, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation36] using item

theorem baseFacts37 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts37 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation37 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe37 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput37 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate37.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨37, by decide +kernel⟩) (List.get_mem originalEntries ⟨37, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts37, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation37] using item

theorem baseFacts38 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts38 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation38 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe38 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput38 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate38.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨38, by decide +kernel⟩) (List.get_mem originalEntries ⟨38, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts38, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation38] using item

theorem baseFacts39 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts39 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation39 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe39 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput39 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate39.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨39, by decide +kernel⟩) (List.get_mem originalEntries ⟨39, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts39, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation39] using item

theorem baseFacts40 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts40 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation40 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe40 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput40 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate40.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨40, by decide +kernel⟩) (List.get_mem originalEntries ⟨40, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts40, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation40] using item

theorem baseFacts41 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts41 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation41 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe41 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput41 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate41.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨41, by decide +kernel⟩) (List.get_mem originalEntries ⟨41, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts41, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation41] using item

theorem baseFacts42 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts42 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation42 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe42 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput42 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate59.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨42, by decide +kernel⟩) (List.get_mem originalEntries ⟨42, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts42, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation42] using item

theorem baseFacts43 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts43 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation43 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe43 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput43 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate60.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨43, by decide +kernel⟩) (List.get_mem originalEntries ⟨43, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts43, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation43] using item

theorem baseFacts44 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts44 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation44 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe44 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput44 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate61.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨44, by decide +kernel⟩) (List.get_mem originalEntries ⟨44, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts44, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation44] using item

theorem baseFacts45 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts45 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation45 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe45 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput45 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate176.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨45, by decide +kernel⟩) (List.get_mem originalEntries ⟨45, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts45, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation45] using item

theorem baseFacts46 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts46 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation46 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe46 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput46 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate179.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨46, by decide +kernel⟩) (List.get_mem originalEntries ⟨46, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts46, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation46] using item

theorem baseFacts47 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts47 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation47 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe47 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput47 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate180.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨47, by decide +kernel⟩) (List.get_mem originalEntries ⟨47, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts47, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation47] using item

theorem baseFacts48 : Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts48 = true ∧ Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation48 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.BigintCached.native.baseRecipe48 Airbender.Compiler.FunctionalNative.BigintCached.native.baseOutput48 Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FullArithmeticNative.BigintCached.native.gate181.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨48, by decide +kernel⟩) (List.get_mem originalEntries ⟨48, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.BigintCached.native.basePorts48, Airbender.Compiler.FunctionalNative.BigintCached.native.baseRelation48] using item

end Airbender.Compiler.FunctionalBaseChecks.BigintCached
