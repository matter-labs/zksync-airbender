module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.LookupSourceChecks.AddSubCached.Bindings
public import Proven.GKRProtocol.NumericCleanArgumentChecks

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.LookupSourceChecks.AddSubCached
open Airbender.Compiler
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=
  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked

noncomputable def entries0 := [
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding0.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field0_0 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding1.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding2.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field2_0 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding3.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field3_0 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding4.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)]

theorem entries0_binding : ((originalEntries.drop 0).take 8) = entries0 := by rfl

theorem entries0_checked : entries0.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries0_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 0 8

noncomputable def entries8 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field4_0 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding5.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field5_0 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding6.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding7.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding8.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding9.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding10.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)]

theorem entries8_binding : ((originalEntries.drop 8).take 8) = entries8 := by rfl

theorem entries8_checked : entries8.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries8_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 8 8

noncomputable def entries16 := [
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding11.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding12.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding13.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding14.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_0 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_1 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_2 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_3 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank]

theorem entries16_binding : ((originalEntries.drop 16).take 8) = entries16 := by rfl

theorem entries16_checked : entries16.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries16_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 16 8

noncomputable def entries24 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_4 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_5 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_6 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_7 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_8 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.ConsumerNative.AddSubCached.native.typing.compatible ((Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe14_0.inputs.headD (.BaseLayerWitness 0)), .base)),
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding15.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding16.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)]

theorem entries24_binding : ((originalEntries.drop 24).take 8) = entries24 := by rfl

theorem entries24_checked : entries24.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries24_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 24 8

noncomputable def entries32 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field16_0 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding17.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf15.isSetup),
  NumericLookupSourceChecks.ofFlag (n := 47) (decide (((Airbender.Compiler.LookupNative.AddSubCached.native.genericTree).leaves.map Airbender.Compiler.LookupSourceNative.AddSubCached.native.genericLabel).Perm (List.range (Airbender.Compiler.LookupSourceNative.AddSubCached.native.genericQueries.length + 1)))),
  NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf1.isSetup),
  NumericLookupSourceChecks.ofFlag (n := 47) (decide (((Airbender.Compiler.LookupNative.AddSubCached.native.range16Tree).leaves.map Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Label).Perm (List.range (Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries.length + 1))))]

theorem entries32_binding : ((originalEntries.drop 32).take 6) = entries32 := by rfl

theorem entries32_checked : entries32.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries32_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 32 6

theorem baseChecked0 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding0.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding0.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries0 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts0_0 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.check Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe0_0 = true ∧ Airbender.Compiler.LookupSourceNative.AddSubCached.native.field0_0.check Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field0_0 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries0 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank0_0 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.check Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe0_0 = true := fieldFacts0_0.1

theorem fieldChecked0_0 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.field0_0.check Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.placement = true := fieldFacts0_0.2

theorem baseChecked1 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding1.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding1.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries0 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked2 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding2.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding2.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries0 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts2_0 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.check Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe2_0 = true ∧ Airbender.Compiler.LookupSourceNative.AddSubCached.native.field2_0.check Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field2_0 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries0 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank2_0 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.check Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe2_0 = true := fieldFacts2_0.1

theorem fieldChecked2_0 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.field2_0.check Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.placement = true := fieldFacts2_0.2

theorem baseChecked3 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding3.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding3.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries0 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts3_0 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.check Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe3_0 = true ∧ Airbender.Compiler.LookupSourceNative.AddSubCached.native.field3_0.check Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field3_0 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries0 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank3_0 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.check Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe3_0 = true := fieldFacts3_0.1

theorem fieldChecked3_0 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.field3_0.check Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.placement = true := fieldFacts3_0.2

theorem baseChecked4 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding4.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding4.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries0 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts4_0 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.check Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe4_0 = true ∧ Airbender.Compiler.LookupSourceNative.AddSubCached.native.field4_0.check Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field4_0 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries8 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank4_0 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.check Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe4_0 = true := fieldFacts4_0.1

theorem fieldChecked4_0 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.field4_0.check Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.placement = true := fieldFacts4_0.2

theorem baseChecked5 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding5.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding5.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries8 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts5_0 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.check Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe5_0 = true ∧ Airbender.Compiler.LookupSourceNative.AddSubCached.native.field5_0.check Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field5_0 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries8 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank5_0 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.check Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe5_0 = true := fieldFacts5_0.1

theorem fieldChecked5_0 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.field5_0.check Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.placement = true := fieldFacts5_0.2

theorem baseChecked6 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding6.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding6.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries8 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked7 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding7.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding7.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries8 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked8 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding8.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding8.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries8 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked9 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding9.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding9.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries8 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked10 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding10.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding10.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries8 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked11 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding11.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding11.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries16 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked12 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding12.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding12.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries16 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked13 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding13.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding13.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries16 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked14 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding14.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding14.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries16 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts14_0 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.check Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe14_0 = true ∧ Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_0.check Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_0 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries16 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank14_0 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.check Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe14_0 = true := fieldFacts14_0.1

theorem fieldChecked14_0 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_0.check Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.placement = true := fieldFacts14_0.2

theorem fieldFacts14_1 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.check Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe14_1 = true ∧ Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_1.check Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_1 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries16 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank14_1 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.check Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe14_1 = true := fieldFacts14_1.1

theorem fieldChecked14_1 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_1.check Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.placement = true := fieldFacts14_1.2

theorem fieldFacts14_2 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.check Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe14_2 = true ∧ Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_2.check Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_2 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries16 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank14_2 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.check Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe14_2 = true := fieldFacts14_2.1

theorem fieldChecked14_2 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_2.check Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.placement = true := fieldFacts14_2.2

theorem fieldFacts14_3 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.check Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe14_3 = true ∧ Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_3.check Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_3 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries16 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank14_3 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.check Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe14_3 = true := fieldFacts14_3.1

theorem fieldChecked14_3 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_3.check Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.placement = true := fieldFacts14_3.2

theorem fieldFacts14_4 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.check Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe14_4 = true ∧ Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_4.check Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_4 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries24 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank14_4 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.check Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe14_4 = true := fieldFacts14_4.1

theorem fieldChecked14_4 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_4.check Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.placement = true := fieldFacts14_4.2

theorem fieldFacts14_5 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.check Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe14_5 = true ∧ Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_5.check Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_5 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries24 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank14_5 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.check Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe14_5 = true := fieldFacts14_5.1

theorem fieldChecked14_5 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_5.check Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.placement = true := fieldFacts14_5.2

theorem fieldFacts14_6 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.check Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe14_6 = true ∧ Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_6.check Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_6 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries24 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank14_6 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.check Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe14_6 = true := fieldFacts14_6.1

theorem fieldChecked14_6 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_6.check Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.placement = true := fieldFacts14_6.2

theorem fieldFacts14_7 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.check Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe14_7 = true ∧ Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_7.check Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_7 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries24 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank14_7 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.check Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe14_7 = true := fieldFacts14_7.1

theorem fieldChecked14_7 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_7.check Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.placement = true := fieldFacts14_7.2

theorem fieldFacts14_8 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.check Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe14_8 = true ∧ Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_8.check Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_8 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries24 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank14_8 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.check Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe14_8 = true := fieldFacts14_8.1

theorem fieldChecked14_8 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.field14_8.check Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.placement = true := fieldFacts14_8.2

theorem maskBase14 : Airbender.Compiler.ConsumerNative.AddSubCached.native.typing.compatible ((Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe14_0.inputs.headD (.BaseLayerWitness 0)), .base) = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.ConsumerNative.AddSubCached.native.typing.compatible ((Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe14_0.inputs.headD (.BaseLayerWitness 0)), .base))).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries24 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked15 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding15.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding15.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries24 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked16 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding16.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding16.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries24 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts16_0 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.check Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe16_0 = true ∧ Airbender.Compiler.LookupSourceNative.AddSubCached.native.field16_0.check Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.AddSubCached.native.field16_0 Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries32 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank16_0 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.check Airbender.Compiler.LookupSourceNative.AddSubCached.native.recipe16_0 = true := fieldFacts16_0.1

theorem fieldChecked16_0 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.field16_0.check Airbender.Compiler.LookupNative.AddSubCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank.placement = true := fieldFacts16_0.2

theorem baseChecked17 : Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding17.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.encoding17.baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing)).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries32 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem genericSetupChecked : Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf15.isSetup = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf15.isSetup)).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries32 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem genericSourceCoverage : decide (((Airbender.Compiler.LookupNative.AddSubCached.native.genericTree).leaves.map Airbender.Compiler.LookupSourceNative.AddSubCached.native.genericLabel).Perm (List.range (Airbender.Compiler.LookupSourceNative.AddSubCached.native.genericQueries.length + 1))) = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 47) (decide (((Airbender.Compiler.LookupNative.AddSubCached.native.genericTree).leaves.map Airbender.Compiler.LookupSourceNative.AddSubCached.native.genericLabel).Perm (List.range (Airbender.Compiler.LookupSourceNative.AddSubCached.native.genericQueries.length + 1))))).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries32 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem range16SetupChecked : Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf1.isSetup = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 47) (Airbender.Compiler.LookupSourceNative.AddSubCached.native.leaf1.isSetup)).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries32 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem range16SourceCoverage : decide (((Airbender.Compiler.LookupNative.AddSubCached.native.range16Tree).leaves.map Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Label).Perm (List.range (Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries.length + 1))) = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 47) (decide (((Airbender.Compiler.LookupNative.AddSubCached.native.range16Tree).leaves.map Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Label).Perm (List.range (Airbender.Compiler.LookupSourceNative.AddSubCached.native.range16Queries.length + 1))))).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries32 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

end Airbender.Compiler.LookupSourceChecks.AddSubCached
