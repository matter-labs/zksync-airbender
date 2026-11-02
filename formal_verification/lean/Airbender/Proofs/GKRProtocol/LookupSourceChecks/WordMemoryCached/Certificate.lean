import Airbender.Proofs.GKRProtocol.LookupSourceChecks.WordMemoryCached.Bindings
import Airbender.Proofs.GKRProtocol.NumericCleanArgumentChecks

namespace Airbender.Compiler.LookupSourceChecks.WordMemoryCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=
  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked

noncomputable def entries0 := [
  NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding0.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field0_0 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding1.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding2.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding3.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding4.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding5.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding6.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)]

theorem entries0_binding : ((originalEntries.drop 0).take 8) = entries0 := by rfl

theorem entries0_checked : entries0.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries0_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 0 8

noncomputable def entries8 := [
  NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding7.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding8.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding9.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding10.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_0 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_1 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_2 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_3 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank]

theorem entries8_binding : ((originalEntries.drop 8).take 8) = entries8 := by rfl

theorem entries8_checked : entries8.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries8_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 8 8

noncomputable def entries16 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_4 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_5 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_6 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_7 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_8 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_9 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing.compatible ((Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe10_0.inputs.headD (.BaseLayerWitness 0)), .base)),
  NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding11.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)]

theorem entries16_binding : ((originalEntries.drop 16).take 8) = entries16 := by rfl

theorem entries16_checked : entries16.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries16_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 16 8

noncomputable def entries24 := [
  NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding12.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field12_0 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding13.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding14.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field14_0 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding15.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_0 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_1 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank]

theorem entries24_binding : ((originalEntries.drop 24).take 8) = entries24 := by rfl

theorem entries24_checked : entries24.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries24_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 24 8

noncomputable def entries32 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_2 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_3 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_4 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_5 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_6 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_7 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_8 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf11.isSetup)]

theorem entries32_binding : ((originalEntries.drop 32).take 8) = entries32 := by rfl

theorem entries32_checked : entries32.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries32_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 32 8

noncomputable def entries40 := [
  NumericLookupSourceChecks.ofFlag (n := 52) (decide (((Airbender.Compiler.LookupNative.WordMemoryCached.native.genericTree).leaves.map Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.genericLabel).Perm (List.range (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.genericQueries.length + 1)))),
  NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf1.isSetup),
  NumericLookupSourceChecks.ofFlag (n := 52) (decide (((Airbender.Compiler.LookupNative.WordMemoryCached.native.range16Tree).leaves.map Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.range16Label).Perm (List.range (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.range16Queries.length + 1))))]

theorem entries40_binding : ((originalEntries.drop 40).take 3) = entries40 := by rfl

theorem entries40_checked : entries40.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries40_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 40 3

theorem baseChecked0 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding0.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding0.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries0 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts0_0 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe0_0 = true ∧ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field0_0.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field0_0 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries0 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank0_0 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe0_0 = true := fieldFacts0_0.1

theorem fieldChecked0_0 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field0_0.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := fieldFacts0_0.2

theorem baseChecked1 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding1.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding1.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries0 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked2 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding2.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding2.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries0 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked3 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding3.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding3.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries0 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked4 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding4.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding4.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries0 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked5 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding5.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding5.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries0 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked6 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding6.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding6.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries0 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked7 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding7.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding7.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries8 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked8 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding8.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding8.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries8 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked9 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding9.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding9.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries8 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked10 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding10.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding10.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries8 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts10_0 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe10_0 = true ∧ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_0.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_0 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries8 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank10_0 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe10_0 = true := fieldFacts10_0.1

theorem fieldChecked10_0 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_0.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := fieldFacts10_0.2

theorem fieldFacts10_1 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe10_1 = true ∧ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_1.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_1 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries8 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank10_1 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe10_1 = true := fieldFacts10_1.1

theorem fieldChecked10_1 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_1.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := fieldFacts10_1.2

theorem fieldFacts10_2 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe10_2 = true ∧ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_2.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_2 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries8 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank10_2 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe10_2 = true := fieldFacts10_2.1

theorem fieldChecked10_2 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_2.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := fieldFacts10_2.2

theorem fieldFacts10_3 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe10_3 = true ∧ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_3.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_3 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries8 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank10_3 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe10_3 = true := fieldFacts10_3.1

theorem fieldChecked10_3 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_3.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := fieldFacts10_3.2

theorem fieldFacts10_4 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe10_4 = true ∧ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_4.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_4 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries16 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank10_4 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe10_4 = true := fieldFacts10_4.1

theorem fieldChecked10_4 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_4.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := fieldFacts10_4.2

theorem fieldFacts10_5 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe10_5 = true ∧ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_5.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_5 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries16 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank10_5 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe10_5 = true := fieldFacts10_5.1

theorem fieldChecked10_5 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_5.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := fieldFacts10_5.2

theorem fieldFacts10_6 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe10_6 = true ∧ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_6.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_6 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries16 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank10_6 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe10_6 = true := fieldFacts10_6.1

theorem fieldChecked10_6 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_6.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := fieldFacts10_6.2

theorem fieldFacts10_7 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe10_7 = true ∧ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_7.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_7 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries16 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank10_7 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe10_7 = true := fieldFacts10_7.1

theorem fieldChecked10_7 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_7.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := fieldFacts10_7.2

theorem fieldFacts10_8 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe10_8 = true ∧ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_8.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_8 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries16 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank10_8 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe10_8 = true := fieldFacts10_8.1

theorem fieldChecked10_8 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_8.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := fieldFacts10_8.2

theorem fieldFacts10_9 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe10_9 = true ∧ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_9.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_9 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries16 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank10_9 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe10_9 = true := fieldFacts10_9.1

theorem fieldChecked10_9 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field10_9.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := fieldFacts10_9.2

theorem maskBase10 : Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing.compatible ((Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe10_0.inputs.headD (.BaseLayerWitness 0)), .base) = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing.compatible ((Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe10_0.inputs.headD (.BaseLayerWitness 0)), .base))).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries16 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked11 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding11.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding11.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries16 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked12 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding12.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding12.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries24 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts12_0 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe12_0 = true ∧ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field12_0.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field12_0 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries24 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank12_0 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe12_0 = true := fieldFacts12_0.1

theorem fieldChecked12_0 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field12_0.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := fieldFacts12_0.2

theorem baseChecked13 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding13.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding13.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries24 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked14 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding14.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding14.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries24 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts14_0 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe14_0 = true ∧ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field14_0.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field14_0 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries24 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank14_0 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe14_0 = true := fieldFacts14_0.1

theorem fieldChecked14_0 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field14_0.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := fieldFacts14_0.2

theorem baseChecked15 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding15.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.encoding15.baseCheck Airbender.Compiler.ConsumerNative.WordMemoryCached.native.typing)).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries24 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts15_0 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe15_0 = true ∧ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_0.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_0 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries24 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank15_0 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe15_0 = true := fieldFacts15_0.1

theorem fieldChecked15_0 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_0.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := fieldFacts15_0.2

theorem fieldFacts15_1 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe15_1 = true ∧ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_1.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_1 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries24 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank15_1 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe15_1 = true := fieldFacts15_1.1

theorem fieldChecked15_1 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_1.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := fieldFacts15_1.2

theorem fieldFacts15_2 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe15_2 = true ∧ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_2.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_2 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries32 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank15_2 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe15_2 = true := fieldFacts15_2.1

theorem fieldChecked15_2 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_2.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := fieldFacts15_2.2

theorem fieldFacts15_3 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe15_3 = true ∧ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_3.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_3 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries32 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank15_3 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe15_3 = true := fieldFacts15_3.1

theorem fieldChecked15_3 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_3.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := fieldFacts15_3.2

theorem fieldFacts15_4 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe15_4 = true ∧ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_4.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_4 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries32 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank15_4 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe15_4 = true := fieldFacts15_4.1

theorem fieldChecked15_4 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_4.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := fieldFacts15_4.2

theorem fieldFacts15_5 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe15_5 = true ∧ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_5.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_5 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries32 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank15_5 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe15_5 = true := fieldFacts15_5.1

theorem fieldChecked15_5 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_5.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := fieldFacts15_5.2

theorem fieldFacts15_6 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe15_6 = true ∧ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_6.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_6 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries32 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank15_6 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe15_6 = true := fieldFacts15_6.1

theorem fieldChecked15_6 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_6.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := fieldFacts15_6.2

theorem fieldFacts15_7 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe15_7 = true ∧ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_7.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_7 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries32 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank15_7 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe15_7 = true := fieldFacts15_7.1

theorem fieldChecked15_7 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_7.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := fieldFacts15_7.2

theorem fieldFacts15_8 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe15_8 = true ∧ Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_8.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_8 Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries32 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank15_8 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.check Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.recipe15_8 = true := fieldFacts15_8.1

theorem fieldChecked15_8 : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.field15_8.check Airbender.Compiler.LookupNative.WordMemoryCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.bank.placement = true := fieldFacts15_8.2

theorem genericSetupChecked : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf11.isSetup = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf11.isSetup)).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries32 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem genericSourceCoverage : decide (((Airbender.Compiler.LookupNative.WordMemoryCached.native.genericTree).leaves.map Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.genericLabel).Perm (List.range (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.genericQueries.length + 1))) = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 52) (decide (((Airbender.Compiler.LookupNative.WordMemoryCached.native.genericTree).leaves.map Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.genericLabel).Perm (List.range (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.genericQueries.length + 1))))).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries40 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem range16SetupChecked : Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf1.isSetup = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 52) (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.leaf1.isSetup)).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries40 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem range16SourceCoverage : decide (((Airbender.Compiler.LookupNative.WordMemoryCached.native.range16Tree).leaves.map Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.range16Label).Perm (List.range (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.range16Queries.length + 1))) = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 52) (decide (((Airbender.Compiler.LookupNative.WordMemoryCached.native.range16Tree).leaves.map Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.range16Label).Perm (List.range (Airbender.Compiler.LookupSourceNative.WordMemoryCached.native.range16Queries.length + 1))))).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries40 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

end Airbender.Compiler.LookupSourceChecks.WordMemoryCached
