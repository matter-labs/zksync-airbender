import Airbender.Proofs.GKRProtocol.LookupSourceChecks.MulDivCached.Bindings
import Airbender.Proofs.GKRProtocol.NumericCleanArgumentChecks

namespace Airbender.Compiler.LookupSourceChecks.MulDivCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=
  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked

noncomputable def entries0 := [
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding0.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field0_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding1.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding2.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field2_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding3.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field3_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding4.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)]

theorem entries0_binding : ((originalEntries.drop 0).take 8) = entries0 := by rfl

theorem entries0_checked : entries0.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries0_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 0 8

noncomputable def entries8 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field4_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding5.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field5_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding6.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field6_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding7.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field7_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding8.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)]

theorem entries8_binding : ((originalEntries.drop 8).take 8) = entries8 := by rfl

theorem entries8_checked : entries8.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries8_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 8 8

noncomputable def entries16 := [
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding9.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding10.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding11.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding12.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding13.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding14.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding15.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding16.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)]

theorem entries16_binding : ((originalEntries.drop 16).take 8) = entries16 := by rfl

theorem entries16_checked : entries16.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries16_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 16 8

noncomputable def entries24 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_1 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_2 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_3 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_4 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_5 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_6 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_7 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank]

theorem entries24_binding : ((originalEntries.drop 24).take 8) = entries24 := by rfl

theorem entries24_checked : entries24.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries24_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 24 8

noncomputable def entries32 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_8 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_9 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.ConsumerNative.MulDivCached.native.typing.compatible ((Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe16_0.inputs.headD (.BaseLayerWitness 0)), .base)),
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding17.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding18.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_1 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_2 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank]

theorem entries32_binding : ((originalEntries.drop 32).take 8) = entries32 := by rfl

theorem entries32_checked : entries32.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries32_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 32 8

noncomputable def entries40 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_3 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_4 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_5 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_6 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_7 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_8 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding19.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank]

theorem entries40_binding : ((originalEntries.drop 40).take 8) = entries40 := by rfl

theorem entries40_checked : entries40.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries40_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 40 8

noncomputable def entries48 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_1 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_2 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_3 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_4 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_5 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_6 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_7 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_8 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank]

theorem entries48_binding : ((originalEntries.drop 48).take 8) = entries48 := by rfl

theorem entries48_checked : entries48.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries48_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 48 8

noncomputable def entries56 := [
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding20.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_1 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_2 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_3 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_4 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_5 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_6 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank]

theorem entries56_binding : ((originalEntries.drop 56).take 8) = entries56 := by rfl

theorem entries56_checked : entries56.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries56_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 56 8

noncomputable def entries64 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_7 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_8 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding21.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_1 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_2 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_3 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_4 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank]

theorem entries64_binding : ((originalEntries.drop 64).take 8) = entries64 := by rfl

theorem entries64_checked : entries64.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries64_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 64 8

noncomputable def entries72 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_5 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_6 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_7 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_8 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding22.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_1 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_2 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank]

theorem entries72_binding : ((originalEntries.drop 72).take 8) = entries72 := by rfl

theorem entries72_checked : entries72.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries72_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 72 8

noncomputable def entries80 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_3 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_4 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_5 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_6 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_7 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_8 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding23.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank]

theorem entries80_binding : ((originalEntries.drop 80).take 8) = entries80 := by rfl

theorem entries80_checked : entries80.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries80_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 80 8

noncomputable def entries88 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_1 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_2 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_3 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_4 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_5 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_6 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_7 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_8 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank]

theorem entries88_binding : ((originalEntries.drop 88).take 8) = entries88 := by rfl

theorem entries88_checked : entries88.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries88_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 88 8

noncomputable def entries96 := [
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding24.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field24_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding25.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding26.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_1 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_2 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_3 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank]

theorem entries96_binding : ((originalEntries.drop 96).take 8) = entries96 := by rfl

theorem entries96_checked : entries96.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries96_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 96 8

noncomputable def entries104 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_4 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_5 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_6 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_7 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_8 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding27.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_1 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank]

theorem entries104_binding : ((originalEntries.drop 104).take 8) = entries104 := by rfl

theorem entries104_checked : entries104.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries104_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 104 8

noncomputable def entries112 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_2 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_3 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_4 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_5 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_6 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_7 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_8 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf17.isSetup)]

theorem entries112_binding : ((originalEntries.drop 112).take 8) = entries112 := by rfl

theorem entries112_checked : entries112.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries112_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 112 8

noncomputable def entries120 := [
  NumericLookupSourceChecks.ofFlag (n := 70) (decide (((Airbender.Compiler.LookupNative.MulDivCached.native.genericTree).leaves.map Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericLabel).Perm (List.range (Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries.length + 1)))),
  NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf1.isSetup),
  NumericLookupSourceChecks.ofFlag (n := 70) (decide (((Airbender.Compiler.LookupNative.MulDivCached.native.range16Tree).leaves.map Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Label).Perm (List.range (Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries.length + 1))))]

theorem entries120_binding : ((originalEntries.drop 120).take 3) = entries120 := by rfl

theorem entries120_checked : entries120.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries120_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 120 3

theorem baseChecked0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding0.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding0.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries0 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts0_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe0_0 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field0_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field0_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries0 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank0_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe0_0 = true := fieldFacts0_0.1

theorem fieldChecked0_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field0_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts0_0.2

theorem baseChecked1 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding1.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding1.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries0 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked2 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding2.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding2.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries0 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts2_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe2_0 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field2_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field2_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries0 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank2_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe2_0 = true := fieldFacts2_0.1

theorem fieldChecked2_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field2_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts2_0.2

theorem baseChecked3 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding3.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding3.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries0 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts3_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe3_0 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field3_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field3_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries0 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank3_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe3_0 = true := fieldFacts3_0.1

theorem fieldChecked3_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field3_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts3_0.2

theorem baseChecked4 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding4.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding4.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries0 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts4_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe4_0 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field4_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field4_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries8 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank4_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe4_0 = true := fieldFacts4_0.1

theorem fieldChecked4_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field4_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts4_0.2

theorem baseChecked5 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding5.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding5.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries8 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts5_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe5_0 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field5_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field5_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries8 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank5_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe5_0 = true := fieldFacts5_0.1

theorem fieldChecked5_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field5_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts5_0.2

theorem baseChecked6 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding6.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding6.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries8 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts6_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe6_0 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field6_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field6_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries8 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank6_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe6_0 = true := fieldFacts6_0.1

theorem fieldChecked6_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field6_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts6_0.2

theorem baseChecked7 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding7.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding7.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries8 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts7_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe7_0 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field7_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field7_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries8 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank7_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe7_0 = true := fieldFacts7_0.1

theorem fieldChecked7_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field7_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts7_0.2

theorem baseChecked8 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding8.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding8.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries8 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked9 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding9.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding9.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries16 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked10 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding10.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding10.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries16 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked11 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding11.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding11.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries16 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked12 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding12.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding12.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries16 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked13 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding13.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding13.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries16 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked14 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding14.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding14.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries16 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked15 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding15.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding15.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries16 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked16 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding16.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding16.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries16 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts16_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe16_0 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries24 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank16_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe16_0 = true := fieldFacts16_0.1

theorem fieldChecked16_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts16_0.2

theorem fieldFacts16_1 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe16_1 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_1.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_1 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries24 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank16_1 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe16_1 = true := fieldFacts16_1.1

theorem fieldChecked16_1 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_1.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts16_1.2

theorem fieldFacts16_2 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe16_2 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_2.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_2 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries24 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank16_2 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe16_2 = true := fieldFacts16_2.1

theorem fieldChecked16_2 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_2.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts16_2.2

theorem fieldFacts16_3 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe16_3 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_3.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_3 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries24 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank16_3 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe16_3 = true := fieldFacts16_3.1

theorem fieldChecked16_3 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_3.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts16_3.2

theorem fieldFacts16_4 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe16_4 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_4.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_4 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries24 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank16_4 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe16_4 = true := fieldFacts16_4.1

theorem fieldChecked16_4 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_4.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts16_4.2

theorem fieldFacts16_5 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe16_5 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_5.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_5 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries24 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank16_5 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe16_5 = true := fieldFacts16_5.1

theorem fieldChecked16_5 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_5.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts16_5.2

theorem fieldFacts16_6 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe16_6 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_6.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_6 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries24 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank16_6 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe16_6 = true := fieldFacts16_6.1

theorem fieldChecked16_6 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_6.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts16_6.2

theorem fieldFacts16_7 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe16_7 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_7.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_7 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries24 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank16_7 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe16_7 = true := fieldFacts16_7.1

theorem fieldChecked16_7 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_7.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts16_7.2

theorem fieldFacts16_8 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe16_8 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_8.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_8 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries32 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank16_8 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe16_8 = true := fieldFacts16_8.1

theorem fieldChecked16_8 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_8.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts16_8.2

theorem fieldFacts16_9 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe16_9 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_9.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_9 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries32 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank16_9 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe16_9 = true := fieldFacts16_9.1

theorem fieldChecked16_9 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field16_9.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts16_9.2

theorem maskBase16 : Airbender.Compiler.ConsumerNative.MulDivCached.native.typing.compatible ((Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe16_0.inputs.headD (.BaseLayerWitness 0)), .base) = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.ConsumerNative.MulDivCached.native.typing.compatible ((Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe16_0.inputs.headD (.BaseLayerWitness 0)), .base))).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries32 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked17 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding17.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding17.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries32 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked18 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding18.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding18.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries32 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts18_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe18_0 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries32 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank18_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe18_0 = true := fieldFacts18_0.1

theorem fieldChecked18_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts18_0.2

theorem fieldFacts18_1 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe18_1 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_1.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_1 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries32 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank18_1 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe18_1 = true := fieldFacts18_1.1

theorem fieldChecked18_1 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_1.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts18_1.2

theorem fieldFacts18_2 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe18_2 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_2.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_2 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries32 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank18_2 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe18_2 = true := fieldFacts18_2.1

theorem fieldChecked18_2 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_2.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts18_2.2

theorem fieldFacts18_3 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe18_3 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_3.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_3 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries40 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank18_3 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe18_3 = true := fieldFacts18_3.1

theorem fieldChecked18_3 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_3.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts18_3.2

theorem fieldFacts18_4 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe18_4 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_4.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_4 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries40 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank18_4 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe18_4 = true := fieldFacts18_4.1

theorem fieldChecked18_4 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_4.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts18_4.2

theorem fieldFacts18_5 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe18_5 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_5.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_5 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries40 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank18_5 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe18_5 = true := fieldFacts18_5.1

theorem fieldChecked18_5 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_5.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts18_5.2

theorem fieldFacts18_6 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe18_6 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_6.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_6 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries40 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank18_6 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe18_6 = true := fieldFacts18_6.1

theorem fieldChecked18_6 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_6.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts18_6.2

theorem fieldFacts18_7 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe18_7 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_7.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_7 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries40 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank18_7 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe18_7 = true := fieldFacts18_7.1

theorem fieldChecked18_7 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_7.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts18_7.2

theorem fieldFacts18_8 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe18_8 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_8.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_8 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries40 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank18_8 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe18_8 = true := fieldFacts18_8.1

theorem fieldChecked18_8 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field18_8.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts18_8.2

theorem baseChecked19 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding19.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding19.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries40 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts19_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe19_0 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries40 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank19_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe19_0 = true := fieldFacts19_0.1

theorem fieldChecked19_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts19_0.2

theorem fieldFacts19_1 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe19_1 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_1.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_1 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries48 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank19_1 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe19_1 = true := fieldFacts19_1.1

theorem fieldChecked19_1 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_1.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts19_1.2

theorem fieldFacts19_2 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe19_2 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_2.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_2 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries48 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank19_2 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe19_2 = true := fieldFacts19_2.1

theorem fieldChecked19_2 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_2.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts19_2.2

theorem fieldFacts19_3 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe19_3 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_3.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_3 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries48 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank19_3 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe19_3 = true := fieldFacts19_3.1

theorem fieldChecked19_3 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_3.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts19_3.2

theorem fieldFacts19_4 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe19_4 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_4.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_4 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries48 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank19_4 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe19_4 = true := fieldFacts19_4.1

theorem fieldChecked19_4 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_4.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts19_4.2

theorem fieldFacts19_5 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe19_5 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_5.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_5 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries48 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank19_5 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe19_5 = true := fieldFacts19_5.1

theorem fieldChecked19_5 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_5.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts19_5.2

theorem fieldFacts19_6 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe19_6 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_6.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_6 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries48 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank19_6 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe19_6 = true := fieldFacts19_6.1

theorem fieldChecked19_6 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_6.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts19_6.2

theorem fieldFacts19_7 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe19_7 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_7.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_7 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries48 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank19_7 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe19_7 = true := fieldFacts19_7.1

theorem fieldChecked19_7 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_7.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts19_7.2

theorem fieldFacts19_8 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe19_8 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_8.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_8 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries48 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank19_8 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe19_8 = true := fieldFacts19_8.1

theorem fieldChecked19_8 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field19_8.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts19_8.2

theorem baseChecked20 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding20.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding20.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries56 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts20_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe20_0 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries56 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank20_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe20_0 = true := fieldFacts20_0.1

theorem fieldChecked20_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts20_0.2

theorem fieldFacts20_1 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe20_1 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_1.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_1 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries56 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank20_1 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe20_1 = true := fieldFacts20_1.1

theorem fieldChecked20_1 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_1.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts20_1.2

theorem fieldFacts20_2 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe20_2 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_2.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_2 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries56 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank20_2 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe20_2 = true := fieldFacts20_2.1

theorem fieldChecked20_2 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_2.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts20_2.2

theorem fieldFacts20_3 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe20_3 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_3.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_3 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries56 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank20_3 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe20_3 = true := fieldFacts20_3.1

theorem fieldChecked20_3 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_3.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts20_3.2

theorem fieldFacts20_4 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe20_4 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_4.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_4 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries56 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank20_4 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe20_4 = true := fieldFacts20_4.1

theorem fieldChecked20_4 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_4.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts20_4.2

theorem fieldFacts20_5 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe20_5 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_5.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_5 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries56 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank20_5 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe20_5 = true := fieldFacts20_5.1

theorem fieldChecked20_5 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_5.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts20_5.2

theorem fieldFacts20_6 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe20_6 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_6.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_6 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries56 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank20_6 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe20_6 = true := fieldFacts20_6.1

theorem fieldChecked20_6 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_6.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts20_6.2

theorem fieldFacts20_7 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe20_7 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_7.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_7 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries64 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank20_7 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe20_7 = true := fieldFacts20_7.1

theorem fieldChecked20_7 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_7.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts20_7.2

theorem fieldFacts20_8 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe20_8 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_8.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_8 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries64 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank20_8 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe20_8 = true := fieldFacts20_8.1

theorem fieldChecked20_8 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field20_8.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts20_8.2

theorem baseChecked21 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding21.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding21.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries64 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts21_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe21_0 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries64 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank21_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe21_0 = true := fieldFacts21_0.1

theorem fieldChecked21_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts21_0.2

theorem fieldFacts21_1 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe21_1 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_1.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_1 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries64 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank21_1 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe21_1 = true := fieldFacts21_1.1

theorem fieldChecked21_1 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_1.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts21_1.2

theorem fieldFacts21_2 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe21_2 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_2.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_2 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries64 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank21_2 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe21_2 = true := fieldFacts21_2.1

theorem fieldChecked21_2 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_2.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts21_2.2

theorem fieldFacts21_3 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe21_3 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_3.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_3 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries64 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank21_3 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe21_3 = true := fieldFacts21_3.1

theorem fieldChecked21_3 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_3.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts21_3.2

theorem fieldFacts21_4 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe21_4 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_4.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_4 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries64 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank21_4 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe21_4 = true := fieldFacts21_4.1

theorem fieldChecked21_4 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_4.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts21_4.2

theorem fieldFacts21_5 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe21_5 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_5.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_5 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries72 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank21_5 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe21_5 = true := fieldFacts21_5.1

theorem fieldChecked21_5 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_5.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts21_5.2

theorem fieldFacts21_6 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe21_6 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_6.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_6 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries72 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank21_6 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe21_6 = true := fieldFacts21_6.1

theorem fieldChecked21_6 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_6.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts21_6.2

theorem fieldFacts21_7 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe21_7 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_7.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_7 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries72 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank21_7 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe21_7 = true := fieldFacts21_7.1

theorem fieldChecked21_7 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_7.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts21_7.2

theorem fieldFacts21_8 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe21_8 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_8.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_8 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries72 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank21_8 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe21_8 = true := fieldFacts21_8.1

theorem fieldChecked21_8 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field21_8.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts21_8.2

theorem baseChecked22 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding22.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding22.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries72 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts22_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe22_0 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries72 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank22_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe22_0 = true := fieldFacts22_0.1

theorem fieldChecked22_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts22_0.2

theorem fieldFacts22_1 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe22_1 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_1.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_1 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries72 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank22_1 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe22_1 = true := fieldFacts22_1.1

theorem fieldChecked22_1 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_1.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts22_1.2

theorem fieldFacts22_2 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe22_2 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_2.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_2 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries72 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank22_2 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe22_2 = true := fieldFacts22_2.1

theorem fieldChecked22_2 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_2.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts22_2.2

theorem fieldFacts22_3 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe22_3 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_3.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_3 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries80 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank22_3 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe22_3 = true := fieldFacts22_3.1

theorem fieldChecked22_3 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_3.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts22_3.2

theorem fieldFacts22_4 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe22_4 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_4.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_4 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries80 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank22_4 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe22_4 = true := fieldFacts22_4.1

theorem fieldChecked22_4 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_4.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts22_4.2

theorem fieldFacts22_5 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe22_5 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_5.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_5 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries80 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank22_5 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe22_5 = true := fieldFacts22_5.1

theorem fieldChecked22_5 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_5.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts22_5.2

theorem fieldFacts22_6 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe22_6 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_6.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_6 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries80 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank22_6 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe22_6 = true := fieldFacts22_6.1

theorem fieldChecked22_6 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_6.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts22_6.2

theorem fieldFacts22_7 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe22_7 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_7.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_7 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries80 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank22_7 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe22_7 = true := fieldFacts22_7.1

theorem fieldChecked22_7 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_7.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts22_7.2

theorem fieldFacts22_8 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe22_8 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_8.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_8 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries80 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank22_8 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe22_8 = true := fieldFacts22_8.1

theorem fieldChecked22_8 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field22_8.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts22_8.2

theorem baseChecked23 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding23.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding23.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries80 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts23_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe23_0 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries80 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank23_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe23_0 = true := fieldFacts23_0.1

theorem fieldChecked23_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts23_0.2

theorem fieldFacts23_1 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe23_1 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_1.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_1 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries88 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank23_1 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe23_1 = true := fieldFacts23_1.1

theorem fieldChecked23_1 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_1.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts23_1.2

theorem fieldFacts23_2 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe23_2 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_2.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_2 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries88 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank23_2 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe23_2 = true := fieldFacts23_2.1

theorem fieldChecked23_2 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_2.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts23_2.2

theorem fieldFacts23_3 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe23_3 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_3.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_3 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries88 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank23_3 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe23_3 = true := fieldFacts23_3.1

theorem fieldChecked23_3 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_3.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts23_3.2

theorem fieldFacts23_4 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe23_4 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_4.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_4 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries88 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank23_4 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe23_4 = true := fieldFacts23_4.1

theorem fieldChecked23_4 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_4.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts23_4.2

theorem fieldFacts23_5 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe23_5 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_5.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_5 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries88 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank23_5 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe23_5 = true := fieldFacts23_5.1

theorem fieldChecked23_5 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_5.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts23_5.2

theorem fieldFacts23_6 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe23_6 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_6.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_6 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries88 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank23_6 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe23_6 = true := fieldFacts23_6.1

theorem fieldChecked23_6 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_6.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts23_6.2

theorem fieldFacts23_7 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe23_7 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_7.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_7 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries88 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank23_7 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe23_7 = true := fieldFacts23_7.1

theorem fieldChecked23_7 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_7.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts23_7.2

theorem fieldFacts23_8 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe23_8 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_8.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_8 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries88 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank23_8 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe23_8 = true := fieldFacts23_8.1

theorem fieldChecked23_8 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field23_8.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts23_8.2

theorem baseChecked24 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding24.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding24.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries96 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts24_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe24_0 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field24_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field24_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries96 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank24_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe24_0 = true := fieldFacts24_0.1

theorem fieldChecked24_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field24_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts24_0.2

theorem baseChecked25 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding25.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding25.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries96 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked26 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding26.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding26.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries96 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts26_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe26_0 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries96 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank26_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe26_0 = true := fieldFacts26_0.1

theorem fieldChecked26_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts26_0.2

theorem fieldFacts26_1 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe26_1 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_1.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_1 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries96 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank26_1 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe26_1 = true := fieldFacts26_1.1

theorem fieldChecked26_1 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_1.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts26_1.2

theorem fieldFacts26_2 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe26_2 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_2.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_2 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries96 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank26_2 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe26_2 = true := fieldFacts26_2.1

theorem fieldChecked26_2 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_2.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts26_2.2

theorem fieldFacts26_3 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe26_3 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_3.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_3 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries96 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank26_3 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe26_3 = true := fieldFacts26_3.1

theorem fieldChecked26_3 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_3.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts26_3.2

theorem fieldFacts26_4 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe26_4 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_4.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_4 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries104 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank26_4 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe26_4 = true := fieldFacts26_4.1

theorem fieldChecked26_4 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_4.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts26_4.2

theorem fieldFacts26_5 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe26_5 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_5.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_5 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries104 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank26_5 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe26_5 = true := fieldFacts26_5.1

theorem fieldChecked26_5 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_5.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts26_5.2

theorem fieldFacts26_6 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe26_6 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_6.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_6 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries104 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank26_6 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe26_6 = true := fieldFacts26_6.1

theorem fieldChecked26_6 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_6.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts26_6.2

theorem fieldFacts26_7 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe26_7 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_7.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_7 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries104 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank26_7 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe26_7 = true := fieldFacts26_7.1

theorem fieldChecked26_7 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_7.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts26_7.2

theorem fieldFacts26_8 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe26_8 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_8.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_8 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries104 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank26_8 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe26_8 = true := fieldFacts26_8.1

theorem fieldChecked26_8 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field26_8.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts26_8.2

theorem baseChecked27 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding27.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.encoding27.baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing)).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries104 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts27_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe27_0 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_0 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries104 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank27_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe27_0 = true := fieldFacts27_0.1

theorem fieldChecked27_0 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_0.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts27_0.2

theorem fieldFacts27_1 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe27_1 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_1.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_1 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries104 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank27_1 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe27_1 = true := fieldFacts27_1.1

theorem fieldChecked27_1 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_1.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts27_1.2

theorem fieldFacts27_2 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe27_2 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_2.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_2 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries112 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank27_2 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe27_2 = true := fieldFacts27_2.1

theorem fieldChecked27_2 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_2.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts27_2.2

theorem fieldFacts27_3 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe27_3 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_3.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_3 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries112 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank27_3 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe27_3 = true := fieldFacts27_3.1

theorem fieldChecked27_3 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_3.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts27_3.2

theorem fieldFacts27_4 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe27_4 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_4.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_4 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries112 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank27_4 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe27_4 = true := fieldFacts27_4.1

theorem fieldChecked27_4 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_4.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts27_4.2

theorem fieldFacts27_5 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe27_5 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_5.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_5 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries112 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank27_5 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe27_5 = true := fieldFacts27_5.1

theorem fieldChecked27_5 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_5.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts27_5.2

theorem fieldFacts27_6 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe27_6 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_6.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_6 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries112 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank27_6 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe27_6 = true := fieldFacts27_6.1

theorem fieldChecked27_6 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_6.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts27_6.2

theorem fieldFacts27_7 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe27_7 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_7.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_7 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries112 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank27_7 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe27_7 = true := fieldFacts27_7.1

theorem fieldChecked27_7 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_7.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts27_7.2

theorem fieldFacts27_8 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe27_8 = true ∧ Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_8.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_8 Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries112 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank27_8 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.check Airbender.Compiler.LookupSourceNative.MulDivCached.native.recipe27_8 = true := fieldFacts27_8.1

theorem fieldChecked27_8 : Airbender.Compiler.LookupSourceNative.MulDivCached.native.field27_8.check Airbender.Compiler.LookupNative.MulDivCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.MulDivCached.native.bank.placement = true := fieldFacts27_8.2

theorem genericSetupChecked : Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf17.isSetup = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf17.isSetup)).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries112 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem genericSourceCoverage : decide (((Airbender.Compiler.LookupNative.MulDivCached.native.genericTree).leaves.map Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericLabel).Perm (List.range (Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries.length + 1))) = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (decide (((Airbender.Compiler.LookupNative.MulDivCached.native.genericTree).leaves.map Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericLabel).Perm (List.range (Airbender.Compiler.LookupSourceNative.MulDivCached.native.genericQueries.length + 1))))).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries120 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem range16SetupChecked : Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf1.isSetup = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (Airbender.Compiler.LookupSourceNative.MulDivCached.native.leaf1.isSetup)).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries120 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem range16SourceCoverage : decide (((Airbender.Compiler.LookupNative.MulDivCached.native.range16Tree).leaves.map Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Label).Perm (List.range (Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries.length + 1))) = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 70) (decide (((Airbender.Compiler.LookupNative.MulDivCached.native.range16Tree).leaves.map Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Label).Perm (List.range (Airbender.Compiler.LookupSourceNative.MulDivCached.native.range16Queries.length + 1))))).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries120 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

end Airbender.Compiler.LookupSourceChecks.MulDivCached
