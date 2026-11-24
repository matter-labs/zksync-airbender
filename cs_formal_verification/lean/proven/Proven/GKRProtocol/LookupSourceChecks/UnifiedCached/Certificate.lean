module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.LookupSourceChecks.UnifiedCached.Bindings
public import Proven.GKRProtocol.NumericCleanArgumentChecks

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.LookupSourceChecks.UnifiedCached
open Airbender.Compiler
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=
  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked

noncomputable def entries0 := [
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding0.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field0_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding1.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding2.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field2_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding3.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field3_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding4.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

theorem entries0_binding : ((originalEntries.drop 0).take 8) = entries0 := by rfl

theorem entries0_checked : entries0.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries0_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 0 8

noncomputable def entries8 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field4_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding5.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field5_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding6.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field6_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding7.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field7_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding8.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

theorem entries8_binding : ((originalEntries.drop 8).take 8) = entries8 := by rfl

theorem entries8_checked : entries8.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries8_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 8 8

noncomputable def entries16 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field8_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding9.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field9_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding10.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field10_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding11.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field11_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding12.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

theorem entries16_binding : ((originalEntries.drop 16).take 8) = entries16 := by rfl

theorem entries16_checked : entries16.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries16_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 16 8

noncomputable def entries24 := [
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding13.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding14.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding15.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding16.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding17.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding18.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding19.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding20.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

theorem entries24_binding : ((originalEntries.drop 24).take 8) = entries24 := by rfl

theorem entries24_checked : entries24.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries24_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 24 8

noncomputable def entries32 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_1 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_2 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_3 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_4 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_5 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_6 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_7 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank]

theorem entries32_binding : ((originalEntries.drop 32).take 8) = entries32 := by rfl

theorem entries32_checked : entries32.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries32_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 32 8

noncomputable def entries40 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_8 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_9 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_10 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing.compatible ((Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe20_0.inputs.headD (.BaseLayerWitness 0)), .base)),
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding21.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding22.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field22_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding23.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)]

theorem entries40_binding : ((originalEntries.drop 40).take 8) = entries40 := by rfl

theorem entries40_checked : entries40.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries40_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 40 8

noncomputable def entries48 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field23_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding24.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding25.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_1 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_2 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_3 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_4 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank]

theorem entries48_binding : ((originalEntries.drop 48).take 8) = entries48 := by rfl

theorem entries48_checked : entries48.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries48_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 48 8

noncomputable def entries56 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_5 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_6 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_7 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_8 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_9 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding26.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_1 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank]

theorem entries56_binding : ((originalEntries.drop 56).take 8) = entries56 := by rfl

theorem entries56_checked : entries56.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries56_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 56 8

noncomputable def entries64 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_2 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_3 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_4 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_5 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_6 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_7 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_8 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_9 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank]

theorem entries64_binding : ((originalEntries.drop 64).take 8) = entries64 := by rfl

theorem entries64_checked : entries64.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries64_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 64 8

noncomputable def entries72 := [
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding27.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_1 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_2 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_3 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_4 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_5 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_6 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank]

theorem entries72_binding : ((originalEntries.drop 72).take 8) = entries72 := by rfl

theorem entries72_checked : entries72.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries72_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 72 8

noncomputable def entries80 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_7 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_8 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_9 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding28.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_1 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_2 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_3 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank]

theorem entries80_binding : ((originalEntries.drop 80).take 8) = entries80 := by rfl

theorem entries80_checked : entries80.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries80_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 80 8

noncomputable def entries88 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_4 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_5 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_6 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_7 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_8 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_9 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding29.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank]

theorem entries88_binding : ((originalEntries.drop 88).take 8) = entries88 := by rfl

theorem entries88_checked : entries88.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries88_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 88 8

noncomputable def entries96 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_1 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_2 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_3 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_4 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_5 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_6 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_7 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_8 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank]

theorem entries96_binding : ((originalEntries.drop 96).take 8) = entries96 := by rfl

theorem entries96_checked : entries96.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries96_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 96 8

noncomputable def entries104 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_9 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf21.isSetup),
  NumericLookupSourceChecks.ofFlag (n := 128) (decide (((Airbender.Compiler.LookupNative.UnifiedCached.native.genericTree).leaves.map Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericLabel).Perm (List.range (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries.length + 1)))),
  NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf1.isSetup),
  NumericLookupSourceChecks.ofFlag (n := 128) (decide (((Airbender.Compiler.LookupNative.UnifiedCached.native.range16Tree).leaves.map Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Label).Perm (List.range (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries.length + 1))))]

theorem entries104_binding : ((originalEntries.drop 104).take 5) = entries104 := by rfl

theorem entries104_checked : entries104.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries104_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 104 5

theorem baseChecked0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding0.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding0.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries0 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts0_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe0_0 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field0_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field0_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries0 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank0_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe0_0 = true := fieldFacts0_0.1

theorem fieldChecked0_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field0_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts0_0.2

theorem baseChecked1 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding1.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding1.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries0 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked2 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding2.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding2.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries0 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts2_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe2_0 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field2_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field2_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries0 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank2_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe2_0 = true := fieldFacts2_0.1

theorem fieldChecked2_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field2_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts2_0.2

theorem baseChecked3 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding3.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding3.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries0 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts3_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe3_0 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field3_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field3_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries0 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank3_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe3_0 = true := fieldFacts3_0.1

theorem fieldChecked3_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field3_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts3_0.2

theorem baseChecked4 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding4.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding4.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries0 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts4_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe4_0 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field4_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field4_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries8 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank4_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe4_0 = true := fieldFacts4_0.1

theorem fieldChecked4_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field4_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts4_0.2

theorem baseChecked5 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding5.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding5.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries8 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts5_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe5_0 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field5_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field5_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries8 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank5_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe5_0 = true := fieldFacts5_0.1

theorem fieldChecked5_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field5_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts5_0.2

theorem baseChecked6 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding6.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding6.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries8 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts6_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe6_0 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field6_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field6_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries8 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank6_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe6_0 = true := fieldFacts6_0.1

theorem fieldChecked6_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field6_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts6_0.2

theorem baseChecked7 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding7.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding7.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries8 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts7_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe7_0 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field7_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field7_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries8 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank7_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe7_0 = true := fieldFacts7_0.1

theorem fieldChecked7_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field7_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts7_0.2

theorem baseChecked8 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding8.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding8.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries8 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts8_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe8_0 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field8_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field8_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries16 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank8_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe8_0 = true := fieldFacts8_0.1

theorem fieldChecked8_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field8_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts8_0.2

theorem baseChecked9 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding9.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding9.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries16 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts9_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe9_0 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field9_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field9_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries16 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank9_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe9_0 = true := fieldFacts9_0.1

theorem fieldChecked9_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field9_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts9_0.2

theorem baseChecked10 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding10.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding10.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries16 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts10_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe10_0 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field10_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field10_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries16 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank10_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe10_0 = true := fieldFacts10_0.1

theorem fieldChecked10_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field10_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts10_0.2

theorem baseChecked11 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding11.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding11.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries16 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts11_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe11_0 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field11_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field11_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries16 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank11_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe11_0 = true := fieldFacts11_0.1

theorem fieldChecked11_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field11_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts11_0.2

theorem baseChecked12 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding12.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding12.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries16 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked13 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding13.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding13.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries24 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked14 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding14.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding14.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries24 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked15 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding15.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding15.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries24 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked16 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding16.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding16.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries24 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked17 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding17.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding17.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries24 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked18 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding18.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding18.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries24 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked19 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding19.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding19.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries24 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked20 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding20.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding20.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries24 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts20_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe20_0 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries32 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank20_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe20_0 = true := fieldFacts20_0.1

theorem fieldChecked20_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts20_0.2

theorem fieldFacts20_1 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe20_1 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_1.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_1 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries32 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank20_1 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe20_1 = true := fieldFacts20_1.1

theorem fieldChecked20_1 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_1.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts20_1.2

theorem fieldFacts20_2 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe20_2 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_2.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_2 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries32 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank20_2 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe20_2 = true := fieldFacts20_2.1

theorem fieldChecked20_2 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_2.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts20_2.2

theorem fieldFacts20_3 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe20_3 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_3.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_3 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries32 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank20_3 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe20_3 = true := fieldFacts20_3.1

theorem fieldChecked20_3 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_3.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts20_3.2

theorem fieldFacts20_4 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe20_4 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_4.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_4 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries32 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank20_4 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe20_4 = true := fieldFacts20_4.1

theorem fieldChecked20_4 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_4.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts20_4.2

theorem fieldFacts20_5 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe20_5 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_5.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_5 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries32 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank20_5 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe20_5 = true := fieldFacts20_5.1

theorem fieldChecked20_5 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_5.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts20_5.2

theorem fieldFacts20_6 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe20_6 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_6.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_6 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries32 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank20_6 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe20_6 = true := fieldFacts20_6.1

theorem fieldChecked20_6 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_6.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts20_6.2

theorem fieldFacts20_7 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe20_7 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_7.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_7 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries32 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank20_7 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe20_7 = true := fieldFacts20_7.1

theorem fieldChecked20_7 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_7.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts20_7.2

theorem fieldFacts20_8 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe20_8 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_8.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_8 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries40 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank20_8 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe20_8 = true := fieldFacts20_8.1

theorem fieldChecked20_8 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_8.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts20_8.2

theorem fieldFacts20_9 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe20_9 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_9.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_9 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries40 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank20_9 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe20_9 = true := fieldFacts20_9.1

theorem fieldChecked20_9 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_9.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts20_9.2

theorem fieldFacts20_10 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe20_10 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_10.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_10 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries40 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank20_10 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe20_10 = true := fieldFacts20_10.1

theorem fieldChecked20_10 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field20_10.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts20_10.2

theorem maskBase20 : Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing.compatible ((Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe20_0.inputs.headD (.BaseLayerWitness 0)), .base) = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing.compatible ((Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe20_0.inputs.headD (.BaseLayerWitness 0)), .base))).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries40 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked21 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding21.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding21.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries40 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked22 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding22.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding22.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries40 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts22_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe22_0 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field22_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field22_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries40 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank22_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe22_0 = true := fieldFacts22_0.1

theorem fieldChecked22_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field22_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts22_0.2

theorem baseChecked23 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding23.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding23.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries40 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts23_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe23_0 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field23_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field23_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries48 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank23_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe23_0 = true := fieldFacts23_0.1

theorem fieldChecked23_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field23_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts23_0.2

theorem baseChecked24 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding24.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding24.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries48 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked25 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding25.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding25.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries48 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts25_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe25_0 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries48 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank25_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe25_0 = true := fieldFacts25_0.1

theorem fieldChecked25_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts25_0.2

theorem fieldFacts25_1 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe25_1 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_1.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_1 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries48 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank25_1 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe25_1 = true := fieldFacts25_1.1

theorem fieldChecked25_1 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_1.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts25_1.2

theorem fieldFacts25_2 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe25_2 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_2.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_2 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries48 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank25_2 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe25_2 = true := fieldFacts25_2.1

theorem fieldChecked25_2 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_2.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts25_2.2

theorem fieldFacts25_3 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe25_3 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_3.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_3 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries48 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank25_3 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe25_3 = true := fieldFacts25_3.1

theorem fieldChecked25_3 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_3.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts25_3.2

theorem fieldFacts25_4 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe25_4 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_4.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_4 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries48 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank25_4 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe25_4 = true := fieldFacts25_4.1

theorem fieldChecked25_4 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_4.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts25_4.2

theorem fieldFacts25_5 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe25_5 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_5.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_5 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries56 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank25_5 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe25_5 = true := fieldFacts25_5.1

theorem fieldChecked25_5 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_5.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts25_5.2

theorem fieldFacts25_6 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe25_6 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_6.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_6 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries56 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank25_6 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe25_6 = true := fieldFacts25_6.1

theorem fieldChecked25_6 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_6.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts25_6.2

theorem fieldFacts25_7 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe25_7 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_7.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_7 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries56 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank25_7 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe25_7 = true := fieldFacts25_7.1

theorem fieldChecked25_7 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_7.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts25_7.2

theorem fieldFacts25_8 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe25_8 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_8.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_8 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries56 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank25_8 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe25_8 = true := fieldFacts25_8.1

theorem fieldChecked25_8 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_8.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts25_8.2

theorem fieldFacts25_9 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe25_9 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_9.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_9 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries56 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank25_9 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe25_9 = true := fieldFacts25_9.1

theorem fieldChecked25_9 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field25_9.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts25_9.2

theorem baseChecked26 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding26.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding26.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries56 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts26_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe26_0 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries56 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank26_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe26_0 = true := fieldFacts26_0.1

theorem fieldChecked26_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts26_0.2

theorem fieldFacts26_1 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe26_1 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_1.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_1 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries56 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank26_1 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe26_1 = true := fieldFacts26_1.1

theorem fieldChecked26_1 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_1.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts26_1.2

theorem fieldFacts26_2 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe26_2 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_2.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_2 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries64 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank26_2 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe26_2 = true := fieldFacts26_2.1

theorem fieldChecked26_2 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_2.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts26_2.2

theorem fieldFacts26_3 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe26_3 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_3.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_3 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries64 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank26_3 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe26_3 = true := fieldFacts26_3.1

theorem fieldChecked26_3 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_3.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts26_3.2

theorem fieldFacts26_4 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe26_4 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_4.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_4 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries64 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank26_4 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe26_4 = true := fieldFacts26_4.1

theorem fieldChecked26_4 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_4.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts26_4.2

theorem fieldFacts26_5 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe26_5 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_5.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_5 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries64 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank26_5 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe26_5 = true := fieldFacts26_5.1

theorem fieldChecked26_5 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_5.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts26_5.2

theorem fieldFacts26_6 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe26_6 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_6.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_6 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries64 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank26_6 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe26_6 = true := fieldFacts26_6.1

theorem fieldChecked26_6 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_6.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts26_6.2

theorem fieldFacts26_7 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe26_7 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_7.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_7 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries64 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank26_7 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe26_7 = true := fieldFacts26_7.1

theorem fieldChecked26_7 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_7.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts26_7.2

theorem fieldFacts26_8 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe26_8 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_8.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_8 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries64 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank26_8 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe26_8 = true := fieldFacts26_8.1

theorem fieldChecked26_8 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_8.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts26_8.2

theorem fieldFacts26_9 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe26_9 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_9.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_9 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries64 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank26_9 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe26_9 = true := fieldFacts26_9.1

theorem fieldChecked26_9 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field26_9.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts26_9.2

theorem baseChecked27 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding27.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding27.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries72 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts27_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe27_0 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries72 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank27_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe27_0 = true := fieldFacts27_0.1

theorem fieldChecked27_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts27_0.2

theorem fieldFacts27_1 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe27_1 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_1.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_1 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries72 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank27_1 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe27_1 = true := fieldFacts27_1.1

theorem fieldChecked27_1 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_1.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts27_1.2

theorem fieldFacts27_2 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe27_2 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_2.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_2 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries72 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank27_2 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe27_2 = true := fieldFacts27_2.1

theorem fieldChecked27_2 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_2.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts27_2.2

theorem fieldFacts27_3 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe27_3 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_3.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_3 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries72 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank27_3 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe27_3 = true := fieldFacts27_3.1

theorem fieldChecked27_3 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_3.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts27_3.2

theorem fieldFacts27_4 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe27_4 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_4.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_4 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries72 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank27_4 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe27_4 = true := fieldFacts27_4.1

theorem fieldChecked27_4 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_4.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts27_4.2

theorem fieldFacts27_5 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe27_5 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_5.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_5 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries72 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank27_5 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe27_5 = true := fieldFacts27_5.1

theorem fieldChecked27_5 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_5.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts27_5.2

theorem fieldFacts27_6 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe27_6 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_6.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_6 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries72 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank27_6 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe27_6 = true := fieldFacts27_6.1

theorem fieldChecked27_6 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_6.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts27_6.2

theorem fieldFacts27_7 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe27_7 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_7.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_7 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries80 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank27_7 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe27_7 = true := fieldFacts27_7.1

theorem fieldChecked27_7 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_7.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts27_7.2

theorem fieldFacts27_8 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe27_8 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_8.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_8 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries80 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank27_8 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe27_8 = true := fieldFacts27_8.1

theorem fieldChecked27_8 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_8.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts27_8.2

theorem fieldFacts27_9 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe27_9 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_9.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_9 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries80 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank27_9 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe27_9 = true := fieldFacts27_9.1

theorem fieldChecked27_9 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field27_9.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts27_9.2

theorem baseChecked28 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding28.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding28.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries80 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts28_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe28_0 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries80 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank28_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe28_0 = true := fieldFacts28_0.1

theorem fieldChecked28_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts28_0.2

theorem fieldFacts28_1 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe28_1 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_1.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_1 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries80 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank28_1 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe28_1 = true := fieldFacts28_1.1

theorem fieldChecked28_1 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_1.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts28_1.2

theorem fieldFacts28_2 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe28_2 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_2.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_2 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries80 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank28_2 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe28_2 = true := fieldFacts28_2.1

theorem fieldChecked28_2 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_2.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts28_2.2

theorem fieldFacts28_3 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe28_3 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_3.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_3 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries80 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank28_3 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe28_3 = true := fieldFacts28_3.1

theorem fieldChecked28_3 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_3.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts28_3.2

theorem fieldFacts28_4 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe28_4 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_4.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_4 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries88 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank28_4 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe28_4 = true := fieldFacts28_4.1

theorem fieldChecked28_4 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_4.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts28_4.2

theorem fieldFacts28_5 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe28_5 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_5.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_5 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries88 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank28_5 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe28_5 = true := fieldFacts28_5.1

theorem fieldChecked28_5 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_5.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts28_5.2

theorem fieldFacts28_6 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe28_6 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_6.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_6 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries88 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank28_6 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe28_6 = true := fieldFacts28_6.1

theorem fieldChecked28_6 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_6.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts28_6.2

theorem fieldFacts28_7 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe28_7 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_7.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_7 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries88 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank28_7 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe28_7 = true := fieldFacts28_7.1

theorem fieldChecked28_7 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_7.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts28_7.2

theorem fieldFacts28_8 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe28_8 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_8.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_8 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries88 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank28_8 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe28_8 = true := fieldFacts28_8.1

theorem fieldChecked28_8 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_8.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts28_8.2

theorem fieldFacts28_9 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe28_9 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_9.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_9 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries88 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank28_9 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe28_9 = true := fieldFacts28_9.1

theorem fieldChecked28_9 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field28_9.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts28_9.2

theorem baseChecked29 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding29.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.encoding29.baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing)).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries88 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts29_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe29_0 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_0 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries88 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank29_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe29_0 = true := fieldFacts29_0.1

theorem fieldChecked29_0 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_0.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts29_0.2

theorem fieldFacts29_1 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe29_1 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_1.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_1 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries96 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank29_1 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe29_1 = true := fieldFacts29_1.1

theorem fieldChecked29_1 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_1.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts29_1.2

theorem fieldFacts29_2 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe29_2 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_2.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_2 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries96 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank29_2 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe29_2 = true := fieldFacts29_2.1

theorem fieldChecked29_2 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_2.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts29_2.2

theorem fieldFacts29_3 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe29_3 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_3.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_3 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries96 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank29_3 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe29_3 = true := fieldFacts29_3.1

theorem fieldChecked29_3 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_3.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts29_3.2

theorem fieldFacts29_4 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe29_4 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_4.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_4 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries96 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank29_4 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe29_4 = true := fieldFacts29_4.1

theorem fieldChecked29_4 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_4.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts29_4.2

theorem fieldFacts29_5 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe29_5 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_5.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_5 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries96 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank29_5 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe29_5 = true := fieldFacts29_5.1

theorem fieldChecked29_5 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_5.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts29_5.2

theorem fieldFacts29_6 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe29_6 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_6.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_6 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries96 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank29_6 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe29_6 = true := fieldFacts29_6.1

theorem fieldChecked29_6 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_6.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts29_6.2

theorem fieldFacts29_7 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe29_7 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_7.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_7 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries96 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank29_7 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe29_7 = true := fieldFacts29_7.1

theorem fieldChecked29_7 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_7.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts29_7.2

theorem fieldFacts29_8 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe29_8 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_8.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_8 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries96 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank29_8 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe29_8 = true := fieldFacts29_8.1

theorem fieldChecked29_8 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_8.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts29_8.2

theorem fieldFacts29_9 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe29_9 = true ∧ Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_9.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_9 Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries104 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank29_9 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.check Airbender.Compiler.LookupSourceNative.UnifiedCached.native.recipe29_9 = true := fieldFacts29_9.1

theorem fieldChecked29_9 : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.field29_9.check Airbender.Compiler.LookupNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.UnifiedCached.native.bank.placement = true := fieldFacts29_9.2

theorem genericSetupChecked : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf21.isSetup = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf21.isSetup)).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries104 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem genericSourceCoverage : decide (((Airbender.Compiler.LookupNative.UnifiedCached.native.genericTree).leaves.map Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericLabel).Perm (List.range (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries.length + 1))) = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (decide (((Airbender.Compiler.LookupNative.UnifiedCached.native.genericTree).leaves.map Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericLabel).Perm (List.range (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.genericQueries.length + 1))))).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries104 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem range16SetupChecked : Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf1.isSetup = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.leaf1.isSetup)).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries104 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem range16SourceCoverage : decide (((Airbender.Compiler.LookupNative.UnifiedCached.native.range16Tree).leaves.map Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Label).Perm (List.range (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries.length + 1))) = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 128) (decide (((Airbender.Compiler.LookupNative.UnifiedCached.native.range16Tree).leaves.map Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Label).Perm (List.range (Airbender.Compiler.LookupSourceNative.UnifiedCached.native.range16Queries.length + 1))))).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries104 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

end Airbender.Compiler.LookupSourceChecks.UnifiedCached
