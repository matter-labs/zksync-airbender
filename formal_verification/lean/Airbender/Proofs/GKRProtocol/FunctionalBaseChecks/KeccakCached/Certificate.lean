import Airbender.Proofs.GKRProtocol.FunctionalBaseChecks.KeccakCached.Bindings

namespace Airbender.Compiler.FunctionalBaseChecks.KeccakCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=
  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked

theorem baseFacts0 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts0 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation0 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe0 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput0 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate0.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨0, by decide +kernel⟩) (List.get_mem originalEntries ⟨0, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts0, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation0] using item

theorem baseFacts1 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts1 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation1 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe1 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput1 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate1.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨1, by decide +kernel⟩) (List.get_mem originalEntries ⟨1, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts1, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation1] using item

theorem baseFacts2 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts2 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation2 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe2 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput2 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate2.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨2, by decide +kernel⟩) (List.get_mem originalEntries ⟨2, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts2, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation2] using item

theorem baseFacts3 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts3 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation3 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe3 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput3 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate3.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨3, by decide +kernel⟩) (List.get_mem originalEntries ⟨3, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts3, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation3] using item

theorem baseFacts4 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts4 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation4 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe4 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput4 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate4.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨4, by decide +kernel⟩) (List.get_mem originalEntries ⟨4, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts4, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation4] using item

theorem baseFacts5 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts5 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation5 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe5 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput5 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate5.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨5, by decide +kernel⟩) (List.get_mem originalEntries ⟨5, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts5, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation5] using item

theorem baseFacts6 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts6 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation6 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe6 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput6 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate6.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨6, by decide +kernel⟩) (List.get_mem originalEntries ⟨6, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts6, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation6] using item

theorem baseFacts7 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts7 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation7 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe7 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput7 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate7.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨7, by decide +kernel⟩) (List.get_mem originalEntries ⟨7, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts7, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation7] using item

theorem baseFacts8 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts8 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation8 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe8 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput8 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate8.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨8, by decide +kernel⟩) (List.get_mem originalEntries ⟨8, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts8, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation8] using item

theorem baseFacts9 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts9 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation9 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe9 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput9 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate9.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨9, by decide +kernel⟩) (List.get_mem originalEntries ⟨9, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts9, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation9] using item

theorem baseFacts10 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts10 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation10 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe10 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput10 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate10.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨10, by decide +kernel⟩) (List.get_mem originalEntries ⟨10, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts10, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation10] using item

theorem baseFacts11 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts11 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation11 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe11 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput11 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate11.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨11, by decide +kernel⟩) (List.get_mem originalEntries ⟨11, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts11, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation11] using item

theorem baseFacts12 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts12 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation12 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe12 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput12 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate12.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨12, by decide +kernel⟩) (List.get_mem originalEntries ⟨12, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts12, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation12] using item

theorem baseFacts13 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts13 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation13 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe13 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput13 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate13.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨13, by decide +kernel⟩) (List.get_mem originalEntries ⟨13, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts13, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation13] using item

theorem baseFacts14 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts14 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation14 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe14 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput14 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate14.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨14, by decide +kernel⟩) (List.get_mem originalEntries ⟨14, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts14, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation14] using item

theorem baseFacts15 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts15 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation15 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe15 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput15 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate15.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨15, by decide +kernel⟩) (List.get_mem originalEntries ⟨15, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts15, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation15] using item

theorem baseFacts16 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts16 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation16 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe16 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput16 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate16.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨16, by decide +kernel⟩) (List.get_mem originalEntries ⟨16, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts16, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation16] using item

theorem baseFacts17 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts17 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation17 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe17 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput17 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate17.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨17, by decide +kernel⟩) (List.get_mem originalEntries ⟨17, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts17, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation17] using item

theorem baseFacts18 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts18 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation18 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe18 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput18 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate18.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨18, by decide +kernel⟩) (List.get_mem originalEntries ⟨18, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts18, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation18] using item

theorem baseFacts19 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts19 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation19 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe19 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput19 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate19.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨19, by decide +kernel⟩) (List.get_mem originalEntries ⟨19, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts19, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation19] using item

theorem baseFacts20 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts20 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation20 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe20 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput20 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate20.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨20, by decide +kernel⟩) (List.get_mem originalEntries ⟨20, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts20, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation20] using item

theorem baseFacts21 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts21 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation21 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe21 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput21 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate21.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨21, by decide +kernel⟩) (List.get_mem originalEntries ⟨21, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts21, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation21] using item

theorem baseFacts22 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts22 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation22 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe22 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput22 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate22.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨22, by decide +kernel⟩) (List.get_mem originalEntries ⟨22, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts22, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation22] using item

theorem baseFacts23 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts23 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation23 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe23 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput23 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate23.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨23, by decide +kernel⟩) (List.get_mem originalEntries ⟨23, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts23, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation23] using item

theorem baseFacts24 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts24 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation24 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe24 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput24 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate24.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨24, by decide +kernel⟩) (List.get_mem originalEntries ⟨24, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts24, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation24] using item

theorem baseFacts25 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts25 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation25 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe25 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput25 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate25.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨25, by decide +kernel⟩) (List.get_mem originalEntries ⟨25, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts25, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation25] using item

theorem baseFacts26 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts26 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation26 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe26 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput26 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate26.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨26, by decide +kernel⟩) (List.get_mem originalEntries ⟨26, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts26, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation26] using item

theorem baseFacts27 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts27 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation27 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe27 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput27 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate27.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨27, by decide +kernel⟩) (List.get_mem originalEntries ⟨27, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts27, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation27] using item

theorem baseFacts28 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts28 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation28 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe28 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput28 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate28.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨28, by decide +kernel⟩) (List.get_mem originalEntries ⟨28, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts28, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation28] using item

theorem baseFacts29 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts29 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation29 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe29 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput29 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate29.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨29, by decide +kernel⟩) (List.get_mem originalEntries ⟨29, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts29, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation29] using item

theorem baseFacts30 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts30 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation30 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe30 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput30 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate30.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨30, by decide +kernel⟩) (List.get_mem originalEntries ⟨30, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts30, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation30] using item

theorem baseFacts31 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts31 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation31 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe31 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput31 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate31.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨31, by decide +kernel⟩) (List.get_mem originalEntries ⟨31, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts31, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation31] using item

theorem baseFacts32 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts32 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation32 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe32 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput32 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate219.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨32, by decide +kernel⟩) (List.get_mem originalEntries ⟨32, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts32, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation32] using item

theorem baseFacts33 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts33 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation33 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe33 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput33 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate220.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨33, by decide +kernel⟩) (List.get_mem originalEntries ⟨33, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts33, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation33] using item

theorem baseFacts34 : Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts34 = true ∧ Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation34 = true := by
  have item : (NumericFunctionalBaseChecks.ofBase Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRecipe34 Airbender.Compiler.FunctionalNative.KeccakCached.native.baseOutput34 Airbender.Compiler.FullArithmeticNative.KeccakCached.native.bank Airbender.Compiler.FunctionalNative.KeccakCached.native.isBase Airbender.Compiler.FullArithmeticNative.KeccakCached.native.gate221.inputResidual).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨34, by decide +kernel⟩) (List.get_mem originalEntries ⟨34, by decide +kernel⟩)
  rw [NumericFunctionalBaseChecks.ofBase_check] at item
  simpa only [Bool.and_eq_true, Airbender.Compiler.FunctionalNative.KeccakCached.native.basePorts34, Airbender.Compiler.FunctionalNative.KeccakCached.native.baseRelation34] using item

end Airbender.Compiler.FunctionalBaseChecks.KeccakCached
