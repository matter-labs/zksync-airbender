import Airbender.Proofs.GKRProtocol.LookupSourceChecks.SubwordMemoryUncached.Bindings
import Airbender.Proofs.GKRProtocol.NumericCleanArgumentChecks

namespace Airbender.Compiler.LookupSourceChecks.SubwordMemoryUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=
  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked

noncomputable def entries0 := [
  NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding0.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field0_0 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding1.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding2.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field2_0 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding3.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field3_0 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding4.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)]

theorem entries0_binding : ((originalEntries.drop 0).take 8) = entries0 := by rfl

theorem entries0_checked : entries0.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries0_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 0 8

noncomputable def entries8 := [
  NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding5.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding6.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding7.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding8.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding9.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding10.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding11.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding12.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)]

theorem entries8_binding : ((originalEntries.drop 8).take 8) = entries8 := by rfl

theorem entries8_checked : entries8.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries8_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 8 8

noncomputable def entries16 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_0 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_1 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_2 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_3 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_4 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_5 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_6 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_7 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank]

theorem entries16_binding : ((originalEntries.drop 16).take 8) = entries16 := by rfl

theorem entries16_checked : entries16.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries16_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 16 8

noncomputable def entries24 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_8 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_9 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing.compatible ((Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe12_0.inputs.headD (.BaseLayerWitness 0)), .base)),
  NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding13.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding14.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field14_0 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding15.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field15_0 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank]

theorem entries24_binding : ((originalEntries.drop 24).take 8) = entries24 := by rfl

theorem entries24_checked : entries24.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries24_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 24 8

noncomputable def entries32 := [
  NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding16.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding17.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_0 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_1 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_2 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_3 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_4 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_5 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank]

theorem entries32_binding : ((originalEntries.drop 32).take 8) = entries32 := by rfl

theorem entries32_checked : entries32.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries32_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 32 8

noncomputable def entries40 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_6 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_7 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_8 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding18.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_0 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_1 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_2 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_3 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank]

theorem entries40_binding : ((originalEntries.drop 40).take 8) = entries40 := by rfl

theorem entries40_checked : entries40.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries40_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 40 8

noncomputable def entries48 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_4 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_5 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_6 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_7 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_8 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf13.isSetup),
  NumericLookupSourceChecks.ofFlag (n := 64) (decide (((Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.genericTree).leaves.map Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.genericLabel).Perm (List.range (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.genericQueries.length + 1)))),
  NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf1.isSetup)]

theorem entries48_binding : ((originalEntries.drop 48).take 8) = entries48 := by rfl

theorem entries48_checked : entries48.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries48_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 48 8

noncomputable def entries56 := [
  NumericLookupSourceChecks.ofFlag (n := 64) (decide (((Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.range16Tree).leaves.map Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Label).Perm (List.range (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Queries.length + 1))))]

theorem entries56_binding : ((originalEntries.drop 56).take 1) = entries56 := by rfl

theorem entries56_checked : entries56.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries56_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 56 1

theorem baseChecked0 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding0.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding0.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries0 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts0_0 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe0_0 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field0_0.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field0_0 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries0 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank0_0 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe0_0 = true := fieldFacts0_0.1

theorem fieldChecked0_0 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field0_0.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts0_0.2

theorem baseChecked1 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding1.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding1.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries0 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked2 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding2.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding2.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries0 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts2_0 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe2_0 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field2_0.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field2_0 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries0 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank2_0 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe2_0 = true := fieldFacts2_0.1

theorem fieldChecked2_0 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field2_0.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts2_0.2

theorem baseChecked3 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding3.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding3.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries0 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts3_0 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe3_0 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field3_0.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field3_0 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries0 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank3_0 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe3_0 = true := fieldFacts3_0.1

theorem fieldChecked3_0 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field3_0.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts3_0.2

theorem baseChecked4 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding4.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding4.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries0 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked5 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding5.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding5.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries8 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked6 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding6.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding6.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries8 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked7 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding7.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding7.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries8 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked8 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding8.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding8.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries8 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked9 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding9.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding9.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries8 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked10 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding10.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding10.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries8 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked11 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding11.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding11.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries8 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked12 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding12.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding12.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries8 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts12_0 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe12_0 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_0.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_0 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries16 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank12_0 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe12_0 = true := fieldFacts12_0.1

theorem fieldChecked12_0 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_0.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts12_0.2

theorem fieldFacts12_1 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe12_1 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_1.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_1 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries16 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank12_1 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe12_1 = true := fieldFacts12_1.1

theorem fieldChecked12_1 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_1.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts12_1.2

theorem fieldFacts12_2 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe12_2 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_2.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_2 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries16 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank12_2 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe12_2 = true := fieldFacts12_2.1

theorem fieldChecked12_2 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_2.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts12_2.2

theorem fieldFacts12_3 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe12_3 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_3.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_3 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries16 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank12_3 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe12_3 = true := fieldFacts12_3.1

theorem fieldChecked12_3 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_3.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts12_3.2

theorem fieldFacts12_4 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe12_4 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_4.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_4 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries16 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank12_4 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe12_4 = true := fieldFacts12_4.1

theorem fieldChecked12_4 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_4.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts12_4.2

theorem fieldFacts12_5 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe12_5 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_5.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_5 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries16 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank12_5 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe12_5 = true := fieldFacts12_5.1

theorem fieldChecked12_5 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_5.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts12_5.2

theorem fieldFacts12_6 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe12_6 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_6.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_6 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries16 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank12_6 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe12_6 = true := fieldFacts12_6.1

theorem fieldChecked12_6 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_6.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts12_6.2

theorem fieldFacts12_7 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe12_7 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_7.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_7 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries16 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank12_7 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe12_7 = true := fieldFacts12_7.1

theorem fieldChecked12_7 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_7.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts12_7.2

theorem fieldFacts12_8 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe12_8 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_8.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_8 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries24 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank12_8 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe12_8 = true := fieldFacts12_8.1

theorem fieldChecked12_8 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_8.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts12_8.2

theorem fieldFacts12_9 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe12_9 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_9.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_9 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries24 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank12_9 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe12_9 = true := fieldFacts12_9.1

theorem fieldChecked12_9 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field12_9.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts12_9.2

theorem maskBase12 : Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing.compatible ((Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe12_0.inputs.headD (.BaseLayerWitness 0)), .base) = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing.compatible ((Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe12_0.inputs.headD (.BaseLayerWitness 0)), .base))).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries24 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked13 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding13.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding13.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries24 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked14 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding14.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding14.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries24 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts14_0 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe14_0 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field14_0.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field14_0 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries24 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank14_0 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe14_0 = true := fieldFacts14_0.1

theorem fieldChecked14_0 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field14_0.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts14_0.2

theorem baseChecked15 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding15.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding15.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries24 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts15_0 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe15_0 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field15_0.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field15_0 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries24 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank15_0 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe15_0 = true := fieldFacts15_0.1

theorem fieldChecked15_0 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field15_0.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts15_0.2

theorem baseChecked16 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding16.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding16.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries32 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked17 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding17.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding17.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries32 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts17_0 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe17_0 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_0.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_0 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries32 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank17_0 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe17_0 = true := fieldFacts17_0.1

theorem fieldChecked17_0 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_0.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts17_0.2

theorem fieldFacts17_1 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe17_1 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_1.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_1 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries32 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank17_1 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe17_1 = true := fieldFacts17_1.1

theorem fieldChecked17_1 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_1.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts17_1.2

theorem fieldFacts17_2 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe17_2 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_2.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_2 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries32 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank17_2 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe17_2 = true := fieldFacts17_2.1

theorem fieldChecked17_2 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_2.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts17_2.2

theorem fieldFacts17_3 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe17_3 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_3.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_3 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries32 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank17_3 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe17_3 = true := fieldFacts17_3.1

theorem fieldChecked17_3 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_3.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts17_3.2

theorem fieldFacts17_4 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe17_4 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_4.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_4 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries32 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank17_4 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe17_4 = true := fieldFacts17_4.1

theorem fieldChecked17_4 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_4.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts17_4.2

theorem fieldFacts17_5 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe17_5 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_5.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_5 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries32 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank17_5 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe17_5 = true := fieldFacts17_5.1

theorem fieldChecked17_5 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_5.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts17_5.2

theorem fieldFacts17_6 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe17_6 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_6.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_6 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries40 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank17_6 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe17_6 = true := fieldFacts17_6.1

theorem fieldChecked17_6 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_6.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts17_6.2

theorem fieldFacts17_7 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe17_7 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_7.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_7 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries40 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank17_7 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe17_7 = true := fieldFacts17_7.1

theorem fieldChecked17_7 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_7.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts17_7.2

theorem fieldFacts17_8 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe17_8 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_8.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_8 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries40 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank17_8 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe17_8 = true := fieldFacts17_8.1

theorem fieldChecked17_8 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field17_8.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts17_8.2

theorem baseChecked18 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding18.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.encoding18.baseCheck Airbender.Compiler.ConsumerNative.SubwordMemoryUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries40 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts18_0 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe18_0 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_0.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_0 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries40 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank18_0 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe18_0 = true := fieldFacts18_0.1

theorem fieldChecked18_0 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_0.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts18_0.2

theorem fieldFacts18_1 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe18_1 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_1.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_1 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries40 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank18_1 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe18_1 = true := fieldFacts18_1.1

theorem fieldChecked18_1 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_1.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts18_1.2

theorem fieldFacts18_2 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe18_2 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_2.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_2 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries40 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank18_2 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe18_2 = true := fieldFacts18_2.1

theorem fieldChecked18_2 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_2.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts18_2.2

theorem fieldFacts18_3 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe18_3 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_3.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_3 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries40 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank18_3 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe18_3 = true := fieldFacts18_3.1

theorem fieldChecked18_3 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_3.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts18_3.2

theorem fieldFacts18_4 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe18_4 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_4.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_4 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries48 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank18_4 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe18_4 = true := fieldFacts18_4.1

theorem fieldChecked18_4 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_4.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts18_4.2

theorem fieldFacts18_5 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe18_5 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_5.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_5 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries48 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank18_5 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe18_5 = true := fieldFacts18_5.1

theorem fieldChecked18_5 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_5.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts18_5.2

theorem fieldFacts18_6 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe18_6 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_6.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_6 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries48 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank18_6 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe18_6 = true := fieldFacts18_6.1

theorem fieldChecked18_6 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_6.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts18_6.2

theorem fieldFacts18_7 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe18_7 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_7.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_7 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries48 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank18_7 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe18_7 = true := fieldFacts18_7.1

theorem fieldChecked18_7 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_7.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts18_7.2

theorem fieldFacts18_8 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe18_8 = true ∧ Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_8.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_8 Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries48 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank18_8 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.check Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.recipe18_8 = true := fieldFacts18_8.1

theorem fieldChecked18_8 : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.field18_8.check Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.bank.placement = true := fieldFacts18_8.2

theorem genericSetupChecked : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf13.isSetup = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf13.isSetup)).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries48 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem genericSourceCoverage : decide (((Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.genericTree).leaves.map Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.genericLabel).Perm (List.range (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.genericQueries.length + 1))) = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 64) (decide (((Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.genericTree).leaves.map Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.genericLabel).Perm (List.range (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.genericQueries.length + 1))))).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries48 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem range16SetupChecked : Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf1.isSetup = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 64) (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.leaf1.isSetup)).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries48 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem range16SourceCoverage : decide (((Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.range16Tree).leaves.map Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Label).Perm (List.range (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Queries.length + 1))) = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 64) (decide (((Airbender.Compiler.LookupNative.SubwordMemoryUncached.native.range16Tree).leaves.map Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Label).Perm (List.range (Airbender.Compiler.LookupSourceNative.SubwordMemoryUncached.native.range16Queries.length + 1))))).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries56 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

end Airbender.Compiler.LookupSourceChecks.SubwordMemoryUncached
