import Airbender.Proofs.GKRProtocol.LookupSourceChecks.BigintCached.Bindings
import Airbender.Proofs.GKRProtocol.NumericCleanArgumentChecks

namespace Airbender.Compiler.LookupSourceChecks.BigintCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=
  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked

noncomputable def entries0 := [
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding0.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field0_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding1.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding2.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field2_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding3.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field3_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding4.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem entries0_binding : ((originalEntries.drop 0).take 8) = entries0 := by rfl

theorem entries0_checked : entries0.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries0_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 0 8

noncomputable def entries8 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field4_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding5.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field5_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding6.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field6_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding7.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field7_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding8.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem entries8_binding : ((originalEntries.drop 8).take 8) = entries8 := by rfl

theorem entries8_checked : entries8.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries8_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 8 8

noncomputable def entries16 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field8_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding9.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field9_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding10.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field10_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding11.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field11_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding12.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem entries16_binding : ((originalEntries.drop 16).take 8) = entries16 := by rfl

theorem entries16_checked : entries16.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries16_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 16 8

noncomputable def entries24 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field12_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding13.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field13_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding14.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field14_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding15.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field15_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding16.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem entries24_binding : ((originalEntries.drop 24).take 8) = entries24 := by rfl

theorem entries24_checked : entries24.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries24_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 24 8

noncomputable def entries32 := [
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding17.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding18.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding19.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding20.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding21.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding22.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding23.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding24.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem entries32_binding : ((originalEntries.drop 32).take 8) = entries32 := by rfl

theorem entries32_checked : entries32.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries32_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 32 8

noncomputable def entries40 := [
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding25.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding26.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding27.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding28.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding29.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding30.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding31.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding32.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem entries40_binding : ((originalEntries.drop 40).take 8) = entries40 := by rfl

theorem entries40_checked : entries40.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries40_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 40 8

noncomputable def entries48 := [
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding33.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding34.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding35.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding36.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding37.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding38.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding39.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding40.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem entries48_binding : ((originalEntries.drop 48).take 8) = entries48 := by rfl

theorem entries48_checked : entries48.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries48_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 48 8

noncomputable def entries56 := [
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding41.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding42.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding43.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding44.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding45.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding46.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding47.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding48.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem entries56_binding : ((originalEntries.drop 56).take 8) = entries56 := by rfl

theorem entries56_checked : entries56.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries56_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 56 8

noncomputable def entries64 := [
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding49.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding50.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding51.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding52.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding53.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding54.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding55.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding56.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)]

theorem entries64_binding : ((originalEntries.drop 64).take 8) = entries64 := by rfl

theorem entries64_checked : entries64.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries64_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 64 8

noncomputable def entries72 := [
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding57.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding58.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field58_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field58_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field58_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding59.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding60.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field60_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries72_binding : ((originalEntries.drop 72).take 8) = entries72 := by rfl

theorem entries72_checked : entries72.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries72_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 72 8

noncomputable def entries80 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field60_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field60_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding61.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field61_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field61_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field61_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding62.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field62_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries80_binding : ((originalEntries.drop 80).take 8) = entries80 := by rfl

theorem entries80_checked : entries80.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries80_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 80 8

noncomputable def entries88 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field62_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field62_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding63.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field63_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field63_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field63_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding64.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field64_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries88_binding : ((originalEntries.drop 88).take 8) = entries88 := by rfl

theorem entries88_checked : entries88.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries88_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 88 8

noncomputable def entries96 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field64_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field64_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding65.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field65_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field65_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field65_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding66.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field66_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries96_binding : ((originalEntries.drop 96).take 8) = entries96 := by rfl

theorem entries96_checked : entries96.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries96_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 96 8

noncomputable def entries104 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field66_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field66_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding67.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field67_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field67_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field67_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding68.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field68_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries104_binding : ((originalEntries.drop 104).take 8) = entries104 := by rfl

theorem entries104_checked : entries104.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries104_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 104 8

noncomputable def entries112 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field68_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field68_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding69.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field69_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field69_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field69_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding70.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field70_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries112_binding : ((originalEntries.drop 112).take 8) = entries112 := by rfl

theorem entries112_checked : entries112.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries112_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 112 8

noncomputable def entries120 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field70_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field70_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding71.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field71_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field71_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field71_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding72.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field72_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries120_binding : ((originalEntries.drop 120).take 8) = entries120 := by rfl

theorem entries120_checked : entries120.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries120_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 120 8

noncomputable def entries128 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field72_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field72_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding73.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field73_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field73_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field73_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding74.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field74_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries128_binding : ((originalEntries.drop 128).take 8) = entries128 := by rfl

theorem entries128_checked : entries128.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries128_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 128 8

noncomputable def entries136 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field74_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field74_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding75.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field75_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field75_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field75_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding76.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field76_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries136_binding : ((originalEntries.drop 136).take 8) = entries136 := by rfl

theorem entries136_checked : entries136.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries136_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 136 8

noncomputable def entries144 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field76_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field76_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding77.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field77_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field77_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field77_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding78.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field78_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries144_binding : ((originalEntries.drop 144).take 8) = entries144 := by rfl

theorem entries144_checked : entries144.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries144_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 144 8

noncomputable def entries152 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field78_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field78_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding79.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field79_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field79_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field79_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding80.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field80_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries152_binding : ((originalEntries.drop 152).take 8) = entries152 := by rfl

theorem entries152_checked : entries152.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries152_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 152 8

noncomputable def entries160 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field80_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field80_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding81.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field81_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field81_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field81_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding82.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field82_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries160_binding : ((originalEntries.drop 160).take 8) = entries160 := by rfl

theorem entries160_checked : entries160.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries160_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 160 8

noncomputable def entries168 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field82_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field82_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding83.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field83_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field83_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field83_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding84.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field84_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries168_binding : ((originalEntries.drop 168).take 8) = entries168 := by rfl

theorem entries168_checked : entries168.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries168_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 168 8

noncomputable def entries176 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field84_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field84_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding85.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field85_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field85_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field85_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding86.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field86_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries176_binding : ((originalEntries.drop 176).take 8) = entries176 := by rfl

theorem entries176_checked : entries176.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries176_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 176 8

noncomputable def entries184 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field86_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field86_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding87.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field87_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field87_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field87_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding88.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field88_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries184_binding : ((originalEntries.drop 184).take 8) = entries184 := by rfl

theorem entries184_checked : entries184.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries184_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 184 8

noncomputable def entries192 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field88_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field88_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding89.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field89_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field89_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field89_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding90.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field90_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries192_binding : ((originalEntries.drop 192).take 8) = entries192 := by rfl

theorem entries192_checked : entries192.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries192_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 192 8

noncomputable def entries200 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field90_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field90_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding91.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field91_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field91_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field91_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding92.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field92_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries200_binding : ((originalEntries.drop 200).take 8) = entries200 := by rfl

theorem entries200_checked : entries200.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries200_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 200 8

noncomputable def entries208 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field92_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field92_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding93.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field93_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field93_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field93_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding94.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field94_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries208_binding : ((originalEntries.drop 208).take 8) = entries208 := by rfl

theorem entries208_checked : entries208.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries208_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 208 8

noncomputable def entries216 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field94_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field94_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding95.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field95_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field95_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field95_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding96.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field96_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries216_binding : ((originalEntries.drop 216).take 8) = entries216 := by rfl

theorem entries216_checked : entries216.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries216_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 216 8

noncomputable def entries224 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field96_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field96_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding97.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field97_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field97_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field97_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding98.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field98_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries224_binding : ((originalEntries.drop 224).take 8) = entries224 := by rfl

theorem entries224_checked : entries224.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries224_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 224 8

noncomputable def entries232 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field98_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field98_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding99.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field99_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field99_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field99_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding100.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field100_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries232_binding : ((originalEntries.drop 232).take 8) = entries232 := by rfl

theorem entries232_checked : entries232.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries232_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 232 8

noncomputable def entries240 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field100_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field100_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding101.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field101_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field101_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field101_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding102.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field102_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries240_binding : ((originalEntries.drop 240).take 8) = entries240 := by rfl

theorem entries240_checked : entries240.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries240_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 240 8

noncomputable def entries248 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field102_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field102_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding103.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field103_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field103_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field103_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding104.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field104_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries248_binding : ((originalEntries.drop 248).take 8) = entries248 := by rfl

theorem entries248_checked : entries248.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries248_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 248 8

noncomputable def entries256 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field104_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field104_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding105.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field105_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field105_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field105_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding106.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field106_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries256_binding : ((originalEntries.drop 256).take 8) = entries256 := by rfl

theorem entries256_checked : entries256.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries256_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 256 8

noncomputable def entries264 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field106_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field106_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding107.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field107_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field107_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field107_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding108.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field108_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries264_binding : ((originalEntries.drop 264).take 8) = entries264 := by rfl

theorem entries264_checked : entries264.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries264_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 264 8

noncomputable def entries272 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field108_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field108_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding109.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field109_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field109_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field109_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding110.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field110_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries272_binding : ((originalEntries.drop 272).take 8) = entries272 := by rfl

theorem entries272_checked : entries272.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries272_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 272 8

noncomputable def entries280 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field110_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field110_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding111.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field111_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field111_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field111_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding112.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field112_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries280_binding : ((originalEntries.drop 280).take 8) = entries280 := by rfl

theorem entries280_checked : entries280.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries280_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 280 8

noncomputable def entries288 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field112_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field112_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding113.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field113_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field113_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field113_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding114.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field114_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries288_binding : ((originalEntries.drop 288).take 8) = entries288 := by rfl

theorem entries288_checked : entries288.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries288_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 288 8

noncomputable def entries296 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field114_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field114_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding115.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field115_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field115_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field115_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding116.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field116_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries296_binding : ((originalEntries.drop 296).take 8) = entries296 := by rfl

theorem entries296_checked : entries296.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries296_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 296 8

noncomputable def entries304 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field116_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field116_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding117.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field117_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field117_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field117_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding118.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field118_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries304_binding : ((originalEntries.drop 304).take 8) = entries304 := by rfl

theorem entries304_checked : entries304.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries304_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 304 8

noncomputable def entries312 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field118_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field118_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding119.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field119_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field119_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field119_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding120.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field120_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries312_binding : ((originalEntries.drop 312).take 8) = entries312 := by rfl

theorem entries312_checked : entries312.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries312_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 312 8

noncomputable def entries320 := [
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding121.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field121_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding122.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field122_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding123.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field123_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding124.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field124_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries320_binding : ((originalEntries.drop 320).take 8) = entries320 := by rfl

theorem entries320_checked : entries320.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries320_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 320 8

noncomputable def entries328 := [
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding125.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field125_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding126.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field126_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding127.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field127_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding128.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field128_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries328_binding : ((originalEntries.drop 328).take 8) = entries328 := by rfl

theorem entries328_checked : entries328.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries328_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 328 8

noncomputable def entries336 := [
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding129.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field129_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding130.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field130_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding131.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field131_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding132.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field132_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries336_binding : ((originalEntries.drop 336).take 8) = entries336 := by rfl

theorem entries336_checked : entries336.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries336_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 336 8

noncomputable def entries344 := [
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding133.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field133_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding134.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field134_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding135.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field135_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding136.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field136_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank]

theorem entries344_binding : ((originalEntries.drop 344).take 8) = entries344 := by rfl

theorem entries344_checked : entries344.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries344_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 344 8

noncomputable def entries352 := [
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.leaf59.isSetup),
  NumericLookupSourceChecks.ofFlag (n := 222) (decide (((Airbender.Compiler.LookupNative.BigintCached.native.genericTree).leaves.map Airbender.Compiler.LookupSourceNative.BigintCached.native.genericLabel).Perm (List.range (Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.length + 1)))),
  NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.leaf1.isSetup),
  NumericLookupSourceChecks.ofFlag (n := 222) (decide (((Airbender.Compiler.LookupNative.BigintCached.native.range16Tree).leaves.map Airbender.Compiler.LookupSourceNative.BigintCached.native.range16Label).Perm (List.range (Airbender.Compiler.LookupSourceNative.BigintCached.native.range16Queries.length + 1))))]

theorem entries352_binding : ((originalEntries.drop 352).take 4) = entries352 := by rfl

theorem entries352_checked : entries352.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries352_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 352 4

theorem baseChecked0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding0.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding0.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries0 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts0_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe0_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field0_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field0_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries0 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank0_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe0_0 = true := fieldFacts0_0.1

theorem fieldChecked0_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field0_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts0_0.2

theorem baseChecked1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding1.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding1.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries0 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding2.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding2.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries0 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts2_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe2_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field2_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field2_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries0 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank2_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe2_0 = true := fieldFacts2_0.1

theorem fieldChecked2_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field2_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts2_0.2

theorem baseChecked3 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding3.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding3.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries0 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts3_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe3_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field3_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field3_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries0 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank3_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe3_0 = true := fieldFacts3_0.1

theorem fieldChecked3_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field3_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts3_0.2

theorem baseChecked4 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding4.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding4.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries0 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts4_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe4_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field4_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field4_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries8 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank4_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe4_0 = true := fieldFacts4_0.1

theorem fieldChecked4_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field4_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts4_0.2

theorem baseChecked5 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding5.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding5.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries8 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts5_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe5_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field5_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field5_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries8 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank5_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe5_0 = true := fieldFacts5_0.1

theorem fieldChecked5_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field5_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts5_0.2

theorem baseChecked6 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding6.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding6.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries8 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts6_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe6_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field6_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field6_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries8 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank6_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe6_0 = true := fieldFacts6_0.1

theorem fieldChecked6_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field6_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts6_0.2

theorem baseChecked7 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding7.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding7.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries8 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts7_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe7_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field7_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field7_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries8 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank7_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe7_0 = true := fieldFacts7_0.1

theorem fieldChecked7_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field7_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts7_0.2

theorem baseChecked8 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding8.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding8.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries8 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts8_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe8_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field8_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field8_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries16 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank8_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe8_0 = true := fieldFacts8_0.1

theorem fieldChecked8_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field8_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts8_0.2

theorem baseChecked9 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding9.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding9.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries16 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts9_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe9_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field9_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field9_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries16 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank9_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe9_0 = true := fieldFacts9_0.1

theorem fieldChecked9_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field9_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts9_0.2

theorem baseChecked10 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding10.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding10.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries16 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts10_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe10_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field10_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field10_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries16 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank10_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe10_0 = true := fieldFacts10_0.1

theorem fieldChecked10_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field10_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts10_0.2

theorem baseChecked11 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding11.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding11.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries16 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts11_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe11_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field11_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field11_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries16 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank11_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe11_0 = true := fieldFacts11_0.1

theorem fieldChecked11_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field11_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts11_0.2

theorem baseChecked12 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding12.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding12.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries16 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts12_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe12_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field12_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field12_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries24 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank12_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe12_0 = true := fieldFacts12_0.1

theorem fieldChecked12_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field12_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts12_0.2

theorem baseChecked13 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding13.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding13.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries24 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts13_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe13_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field13_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field13_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries24 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank13_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe13_0 = true := fieldFacts13_0.1

theorem fieldChecked13_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field13_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts13_0.2

theorem baseChecked14 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding14.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding14.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries24 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts14_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe14_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field14_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field14_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries24 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank14_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe14_0 = true := fieldFacts14_0.1

theorem fieldChecked14_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field14_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts14_0.2

theorem baseChecked15 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding15.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding15.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries24 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts15_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe15_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field15_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field15_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries24 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank15_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe15_0 = true := fieldFacts15_0.1

theorem fieldChecked15_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field15_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts15_0.2

theorem baseChecked16 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding16.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding16.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries24 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked17 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding17.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding17.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries32 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked18 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding18.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding18.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries32 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked19 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding19.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding19.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries32 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked20 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding20.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding20.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries32 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked21 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding21.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding21.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries32 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked22 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding22.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding22.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries32 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked23 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding23.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding23.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries32 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked24 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding24.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding24.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries32 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked25 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding25.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding25.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries40 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked26 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding26.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding26.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries40 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked27 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding27.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding27.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries40 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked28 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding28.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding28.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries40 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked29 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding29.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding29.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries40 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked30 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding30.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding30.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries40 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked31 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding31.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding31.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries40 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked32 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding32.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding32.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries40 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked33 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding33.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding33.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries48 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked34 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding34.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding34.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries48 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked35 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding35.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding35.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries48 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked36 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding36.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding36.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries48 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked37 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding37.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding37.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries48 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked38 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding38.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding38.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries48 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked39 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding39.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding39.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries48 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked40 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding40.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding40.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries48 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked41 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding41.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding41.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries56 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked42 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding42.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding42.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries56 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked43 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding43.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding43.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries56 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked44 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding44.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding44.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries56 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked45 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding45.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding45.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries56 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked46 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding46.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding46.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries56 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked47 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding47.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding47.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries56 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked48 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding48.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding48.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries56 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked49 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding49.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding49.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries64 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked50 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding50.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding50.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries64 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked51 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding51.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding51.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries64 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked52 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding52.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding52.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries64 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked53 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding53.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding53.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries64 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked54 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding54.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding54.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries64 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked55 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding55.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding55.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries64 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked56 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding56.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding56.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries64 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked57 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding57.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding57.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries72 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked58 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding58.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding58.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries72 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts58_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe58_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field58_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field58_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries72 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank58_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe58_0 = true := fieldFacts58_0.1

theorem fieldChecked58_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field58_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts58_0.2

theorem fieldFacts58_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe58_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field58_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field58_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries72 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank58_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe58_1 = true := fieldFacts58_1.1

theorem fieldChecked58_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field58_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts58_1.2

theorem fieldFacts58_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe58_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field58_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field58_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries72 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank58_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe58_2 = true := fieldFacts58_2.1

theorem fieldChecked58_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field58_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts58_2.2

theorem baseChecked59 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding59.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding59.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries72 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked60 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding60.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding60.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries72 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts60_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe60_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field60_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field60_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries72 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank60_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe60_0 = true := fieldFacts60_0.1

theorem fieldChecked60_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field60_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts60_0.2

theorem fieldFacts60_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe60_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field60_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field60_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries80 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank60_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe60_1 = true := fieldFacts60_1.1

theorem fieldChecked60_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field60_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts60_1.2

theorem fieldFacts60_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe60_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field60_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field60_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries80 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank60_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe60_2 = true := fieldFacts60_2.1

theorem fieldChecked60_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field60_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts60_2.2

theorem baseChecked61 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding61.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding61.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries80 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts61_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe61_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field61_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field61_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries80 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank61_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe61_0 = true := fieldFacts61_0.1

theorem fieldChecked61_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field61_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts61_0.2

theorem fieldFacts61_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe61_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field61_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field61_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries80 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank61_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe61_1 = true := fieldFacts61_1.1

theorem fieldChecked61_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field61_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts61_1.2

theorem fieldFacts61_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe61_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field61_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field61_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries80 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank61_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe61_2 = true := fieldFacts61_2.1

theorem fieldChecked61_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field61_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts61_2.2

theorem baseChecked62 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding62.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding62.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries80 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts62_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe62_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field62_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field62_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries80 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank62_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe62_0 = true := fieldFacts62_0.1

theorem fieldChecked62_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field62_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts62_0.2

theorem fieldFacts62_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe62_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field62_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field62_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries88 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank62_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe62_1 = true := fieldFacts62_1.1

theorem fieldChecked62_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field62_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts62_1.2

theorem fieldFacts62_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe62_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field62_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field62_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries88 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank62_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe62_2 = true := fieldFacts62_2.1

theorem fieldChecked62_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field62_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts62_2.2

theorem baseChecked63 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding63.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding63.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries88 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts63_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe63_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field63_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field63_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries88 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank63_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe63_0 = true := fieldFacts63_0.1

theorem fieldChecked63_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field63_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts63_0.2

theorem fieldFacts63_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe63_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field63_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field63_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries88 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank63_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe63_1 = true := fieldFacts63_1.1

theorem fieldChecked63_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field63_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts63_1.2

theorem fieldFacts63_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe63_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field63_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field63_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries88 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank63_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe63_2 = true := fieldFacts63_2.1

theorem fieldChecked63_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field63_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts63_2.2

theorem baseChecked64 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding64.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding64.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries88 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts64_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe64_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field64_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field64_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries88 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank64_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe64_0 = true := fieldFacts64_0.1

theorem fieldChecked64_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field64_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts64_0.2

theorem fieldFacts64_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe64_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field64_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field64_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries96 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank64_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe64_1 = true := fieldFacts64_1.1

theorem fieldChecked64_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field64_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts64_1.2

theorem fieldFacts64_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe64_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field64_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field64_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries96 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank64_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe64_2 = true := fieldFacts64_2.1

theorem fieldChecked64_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field64_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts64_2.2

theorem baseChecked65 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding65.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding65.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries96 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts65_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe65_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field65_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field65_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries96 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank65_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe65_0 = true := fieldFacts65_0.1

theorem fieldChecked65_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field65_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts65_0.2

theorem fieldFacts65_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe65_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field65_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field65_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries96 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank65_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe65_1 = true := fieldFacts65_1.1

theorem fieldChecked65_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field65_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts65_1.2

theorem fieldFacts65_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe65_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field65_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field65_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries96 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank65_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe65_2 = true := fieldFacts65_2.1

theorem fieldChecked65_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field65_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts65_2.2

theorem baseChecked66 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding66.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding66.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries96 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts66_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe66_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field66_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field66_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries96 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank66_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe66_0 = true := fieldFacts66_0.1

theorem fieldChecked66_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field66_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts66_0.2

theorem fieldFacts66_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe66_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field66_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field66_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries104 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank66_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe66_1 = true := fieldFacts66_1.1

theorem fieldChecked66_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field66_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts66_1.2

theorem fieldFacts66_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe66_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field66_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field66_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries104 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank66_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe66_2 = true := fieldFacts66_2.1

theorem fieldChecked66_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field66_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts66_2.2

theorem baseChecked67 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding67.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding67.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries104 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts67_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe67_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field67_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field67_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries104 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank67_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe67_0 = true := fieldFacts67_0.1

theorem fieldChecked67_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field67_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts67_0.2

theorem fieldFacts67_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe67_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field67_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field67_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries104 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank67_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe67_1 = true := fieldFacts67_1.1

theorem fieldChecked67_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field67_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts67_1.2

theorem fieldFacts67_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe67_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field67_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field67_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries104 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank67_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe67_2 = true := fieldFacts67_2.1

theorem fieldChecked67_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field67_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts67_2.2

theorem baseChecked68 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding68.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding68.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries104 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts68_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe68_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field68_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field68_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries104 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank68_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe68_0 = true := fieldFacts68_0.1

theorem fieldChecked68_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field68_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts68_0.2

theorem fieldFacts68_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe68_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field68_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field68_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries112 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank68_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe68_1 = true := fieldFacts68_1.1

theorem fieldChecked68_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field68_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts68_1.2

theorem fieldFacts68_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe68_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field68_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field68_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries112 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank68_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe68_2 = true := fieldFacts68_2.1

theorem fieldChecked68_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field68_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts68_2.2

theorem baseChecked69 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding69.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding69.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries112 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts69_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe69_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field69_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field69_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries112 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank69_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe69_0 = true := fieldFacts69_0.1

theorem fieldChecked69_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field69_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts69_0.2

theorem fieldFacts69_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe69_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field69_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field69_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries112 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank69_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe69_1 = true := fieldFacts69_1.1

theorem fieldChecked69_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field69_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts69_1.2

theorem fieldFacts69_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe69_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field69_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field69_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries112 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank69_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe69_2 = true := fieldFacts69_2.1

theorem fieldChecked69_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field69_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts69_2.2

theorem baseChecked70 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding70.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding70.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries112 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts70_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe70_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field70_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field70_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries112 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank70_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe70_0 = true := fieldFacts70_0.1

theorem fieldChecked70_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field70_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts70_0.2

theorem fieldFacts70_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe70_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field70_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field70_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries120 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank70_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe70_1 = true := fieldFacts70_1.1

theorem fieldChecked70_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field70_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts70_1.2

theorem fieldFacts70_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe70_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field70_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field70_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries120 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank70_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe70_2 = true := fieldFacts70_2.1

theorem fieldChecked70_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field70_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts70_2.2

theorem baseChecked71 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding71.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding71.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries120 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts71_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe71_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field71_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field71_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries120 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank71_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe71_0 = true := fieldFacts71_0.1

theorem fieldChecked71_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field71_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts71_0.2

theorem fieldFacts71_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe71_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field71_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field71_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries120 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank71_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe71_1 = true := fieldFacts71_1.1

theorem fieldChecked71_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field71_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts71_1.2

theorem fieldFacts71_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe71_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field71_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field71_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries120 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank71_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe71_2 = true := fieldFacts71_2.1

theorem fieldChecked71_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field71_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts71_2.2

theorem baseChecked72 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding72.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding72.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries120 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts72_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe72_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field72_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field72_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries120 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank72_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe72_0 = true := fieldFacts72_0.1

theorem fieldChecked72_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field72_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts72_0.2

theorem fieldFacts72_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe72_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field72_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field72_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries128 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank72_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe72_1 = true := fieldFacts72_1.1

theorem fieldChecked72_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field72_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts72_1.2

theorem fieldFacts72_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe72_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field72_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field72_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries128 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank72_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe72_2 = true := fieldFacts72_2.1

theorem fieldChecked72_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field72_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts72_2.2

theorem baseChecked73 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding73.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding73.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries128 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts73_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe73_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field73_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field73_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries128 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank73_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe73_0 = true := fieldFacts73_0.1

theorem fieldChecked73_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field73_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts73_0.2

theorem fieldFacts73_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe73_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field73_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field73_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries128 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank73_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe73_1 = true := fieldFacts73_1.1

theorem fieldChecked73_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field73_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts73_1.2

theorem fieldFacts73_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe73_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field73_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field73_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries128 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank73_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe73_2 = true := fieldFacts73_2.1

theorem fieldChecked73_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field73_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts73_2.2

theorem baseChecked74 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding74.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding74.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries128 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts74_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe74_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field74_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field74_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries128 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank74_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe74_0 = true := fieldFacts74_0.1

theorem fieldChecked74_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field74_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts74_0.2

theorem fieldFacts74_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe74_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field74_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field74_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries136 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank74_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe74_1 = true := fieldFacts74_1.1

theorem fieldChecked74_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field74_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts74_1.2

theorem fieldFacts74_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe74_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field74_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field74_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries136 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank74_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe74_2 = true := fieldFacts74_2.1

theorem fieldChecked74_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field74_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts74_2.2

theorem baseChecked75 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding75.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding75.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries136 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts75_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe75_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field75_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field75_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries136 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank75_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe75_0 = true := fieldFacts75_0.1

theorem fieldChecked75_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field75_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts75_0.2

theorem fieldFacts75_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe75_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field75_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field75_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries136 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank75_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe75_1 = true := fieldFacts75_1.1

theorem fieldChecked75_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field75_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts75_1.2

theorem fieldFacts75_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe75_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field75_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field75_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries136 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank75_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe75_2 = true := fieldFacts75_2.1

theorem fieldChecked75_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field75_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts75_2.2

theorem baseChecked76 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding76.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding76.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries136 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts76_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe76_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field76_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field76_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries136 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank76_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe76_0 = true := fieldFacts76_0.1

theorem fieldChecked76_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field76_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts76_0.2

theorem fieldFacts76_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe76_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field76_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field76_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries144 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank76_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe76_1 = true := fieldFacts76_1.1

theorem fieldChecked76_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field76_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts76_1.2

theorem fieldFacts76_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe76_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field76_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field76_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries144 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank76_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe76_2 = true := fieldFacts76_2.1

theorem fieldChecked76_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field76_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts76_2.2

theorem baseChecked77 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding77.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding77.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries144 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts77_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe77_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field77_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field77_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries144 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank77_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe77_0 = true := fieldFacts77_0.1

theorem fieldChecked77_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field77_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts77_0.2

theorem fieldFacts77_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe77_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field77_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field77_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries144 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank77_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe77_1 = true := fieldFacts77_1.1

theorem fieldChecked77_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field77_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts77_1.2

theorem fieldFacts77_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe77_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field77_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field77_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries144 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank77_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe77_2 = true := fieldFacts77_2.1

theorem fieldChecked77_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field77_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts77_2.2

theorem baseChecked78 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding78.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding78.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries144 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts78_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe78_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field78_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field78_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries144 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank78_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe78_0 = true := fieldFacts78_0.1

theorem fieldChecked78_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field78_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts78_0.2

theorem fieldFacts78_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe78_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field78_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field78_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries152 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank78_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe78_1 = true := fieldFacts78_1.1

theorem fieldChecked78_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field78_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts78_1.2

theorem fieldFacts78_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe78_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field78_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field78_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries152 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank78_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe78_2 = true := fieldFacts78_2.1

theorem fieldChecked78_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field78_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts78_2.2

theorem baseChecked79 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding79.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding79.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries152 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts79_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe79_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field79_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field79_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries152 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank79_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe79_0 = true := fieldFacts79_0.1

theorem fieldChecked79_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field79_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts79_0.2

theorem fieldFacts79_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe79_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field79_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field79_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries152 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank79_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe79_1 = true := fieldFacts79_1.1

theorem fieldChecked79_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field79_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts79_1.2

theorem fieldFacts79_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe79_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field79_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field79_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries152 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank79_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe79_2 = true := fieldFacts79_2.1

theorem fieldChecked79_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field79_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts79_2.2

theorem baseChecked80 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding80.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding80.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries152 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts80_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe80_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field80_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field80_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries152 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank80_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe80_0 = true := fieldFacts80_0.1

theorem fieldChecked80_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field80_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts80_0.2

theorem fieldFacts80_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe80_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field80_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field80_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries160 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank80_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe80_1 = true := fieldFacts80_1.1

theorem fieldChecked80_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field80_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts80_1.2

theorem fieldFacts80_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe80_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field80_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field80_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries160 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank80_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe80_2 = true := fieldFacts80_2.1

theorem fieldChecked80_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field80_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts80_2.2

theorem baseChecked81 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding81.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding81.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries160 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts81_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe81_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field81_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field81_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries160 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank81_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe81_0 = true := fieldFacts81_0.1

theorem fieldChecked81_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field81_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts81_0.2

theorem fieldFacts81_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe81_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field81_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field81_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries160 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank81_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe81_1 = true := fieldFacts81_1.1

theorem fieldChecked81_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field81_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts81_1.2

theorem fieldFacts81_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe81_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field81_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field81_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries160 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank81_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe81_2 = true := fieldFacts81_2.1

theorem fieldChecked81_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field81_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts81_2.2

theorem baseChecked82 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding82.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding82.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries160 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts82_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe82_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field82_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field82_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries160 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank82_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe82_0 = true := fieldFacts82_0.1

theorem fieldChecked82_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field82_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts82_0.2

theorem fieldFacts82_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe82_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field82_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field82_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries168 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank82_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe82_1 = true := fieldFacts82_1.1

theorem fieldChecked82_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field82_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts82_1.2

theorem fieldFacts82_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe82_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field82_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field82_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries168 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank82_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe82_2 = true := fieldFacts82_2.1

theorem fieldChecked82_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field82_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts82_2.2

theorem baseChecked83 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding83.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding83.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries168 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts83_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe83_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field83_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field83_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries168 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank83_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe83_0 = true := fieldFacts83_0.1

theorem fieldChecked83_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field83_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts83_0.2

theorem fieldFacts83_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe83_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field83_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field83_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries168 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank83_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe83_1 = true := fieldFacts83_1.1

theorem fieldChecked83_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field83_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts83_1.2

theorem fieldFacts83_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe83_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field83_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field83_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries168 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank83_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe83_2 = true := fieldFacts83_2.1

theorem fieldChecked83_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field83_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts83_2.2

theorem baseChecked84 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding84.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding84.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries168 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts84_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe84_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field84_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field84_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries168 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank84_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe84_0 = true := fieldFacts84_0.1

theorem fieldChecked84_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field84_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts84_0.2

theorem fieldFacts84_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe84_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field84_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field84_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries176 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank84_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe84_1 = true := fieldFacts84_1.1

theorem fieldChecked84_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field84_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts84_1.2

theorem fieldFacts84_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe84_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field84_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field84_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries176 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank84_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe84_2 = true := fieldFacts84_2.1

theorem fieldChecked84_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field84_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts84_2.2

theorem baseChecked85 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding85.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding85.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries176 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts85_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe85_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field85_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field85_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries176 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank85_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe85_0 = true := fieldFacts85_0.1

theorem fieldChecked85_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field85_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts85_0.2

theorem fieldFacts85_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe85_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field85_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field85_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries176 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank85_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe85_1 = true := fieldFacts85_1.1

theorem fieldChecked85_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field85_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts85_1.2

theorem fieldFacts85_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe85_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field85_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field85_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries176 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank85_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe85_2 = true := fieldFacts85_2.1

theorem fieldChecked85_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field85_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts85_2.2

theorem baseChecked86 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding86.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding86.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries176 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts86_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe86_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field86_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field86_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries176 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank86_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe86_0 = true := fieldFacts86_0.1

theorem fieldChecked86_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field86_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts86_0.2

theorem fieldFacts86_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe86_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field86_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field86_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries184 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank86_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe86_1 = true := fieldFacts86_1.1

theorem fieldChecked86_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field86_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts86_1.2

theorem fieldFacts86_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe86_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field86_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field86_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries184 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank86_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe86_2 = true := fieldFacts86_2.1

theorem fieldChecked86_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field86_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts86_2.2

theorem baseChecked87 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding87.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding87.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries184 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts87_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe87_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field87_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field87_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries184 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank87_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe87_0 = true := fieldFacts87_0.1

theorem fieldChecked87_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field87_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts87_0.2

theorem fieldFacts87_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe87_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field87_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field87_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries184 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank87_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe87_1 = true := fieldFacts87_1.1

theorem fieldChecked87_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field87_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts87_1.2

theorem fieldFacts87_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe87_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field87_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field87_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries184 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank87_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe87_2 = true := fieldFacts87_2.1

theorem fieldChecked87_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field87_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts87_2.2

theorem baseChecked88 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding88.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding88.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries184 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts88_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe88_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field88_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field88_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries184 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank88_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe88_0 = true := fieldFacts88_0.1

theorem fieldChecked88_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field88_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts88_0.2

theorem fieldFacts88_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe88_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field88_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field88_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries192 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank88_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe88_1 = true := fieldFacts88_1.1

theorem fieldChecked88_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field88_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts88_1.2

theorem fieldFacts88_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe88_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field88_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field88_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries192 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank88_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe88_2 = true := fieldFacts88_2.1

theorem fieldChecked88_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field88_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts88_2.2

theorem baseChecked89 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding89.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding89.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries192 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts89_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe89_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field89_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field89_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries192 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank89_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe89_0 = true := fieldFacts89_0.1

theorem fieldChecked89_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field89_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts89_0.2

theorem fieldFacts89_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe89_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field89_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field89_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries192 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank89_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe89_1 = true := fieldFacts89_1.1

theorem fieldChecked89_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field89_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts89_1.2

theorem fieldFacts89_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe89_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field89_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field89_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries192 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank89_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe89_2 = true := fieldFacts89_2.1

theorem fieldChecked89_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field89_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts89_2.2

theorem baseChecked90 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding90.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding90.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries192 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts90_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe90_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field90_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field90_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries192 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank90_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe90_0 = true := fieldFacts90_0.1

theorem fieldChecked90_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field90_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts90_0.2

theorem fieldFacts90_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe90_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field90_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field90_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries200 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank90_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe90_1 = true := fieldFacts90_1.1

theorem fieldChecked90_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field90_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts90_1.2

theorem fieldFacts90_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe90_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field90_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field90_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries200 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank90_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe90_2 = true := fieldFacts90_2.1

theorem fieldChecked90_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field90_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts90_2.2

theorem baseChecked91 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding91.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding91.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries200 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts91_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe91_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field91_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field91_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries200 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank91_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe91_0 = true := fieldFacts91_0.1

theorem fieldChecked91_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field91_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts91_0.2

theorem fieldFacts91_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe91_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field91_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field91_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries200 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank91_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe91_1 = true := fieldFacts91_1.1

theorem fieldChecked91_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field91_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts91_1.2

theorem fieldFacts91_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe91_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field91_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field91_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries200 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank91_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe91_2 = true := fieldFacts91_2.1

theorem fieldChecked91_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field91_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts91_2.2

theorem baseChecked92 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding92.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding92.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries200 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts92_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe92_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field92_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field92_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries200 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank92_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe92_0 = true := fieldFacts92_0.1

theorem fieldChecked92_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field92_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts92_0.2

theorem fieldFacts92_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe92_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field92_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field92_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries208 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank92_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe92_1 = true := fieldFacts92_1.1

theorem fieldChecked92_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field92_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts92_1.2

theorem fieldFacts92_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe92_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field92_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field92_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries208 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank92_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe92_2 = true := fieldFacts92_2.1

theorem fieldChecked92_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field92_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts92_2.2

theorem baseChecked93 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding93.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding93.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries208 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts93_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe93_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field93_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field93_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries208 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank93_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe93_0 = true := fieldFacts93_0.1

theorem fieldChecked93_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field93_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts93_0.2

theorem fieldFacts93_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe93_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field93_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field93_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries208 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank93_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe93_1 = true := fieldFacts93_1.1

theorem fieldChecked93_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field93_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts93_1.2

theorem fieldFacts93_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe93_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field93_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field93_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries208 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank93_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe93_2 = true := fieldFacts93_2.1

theorem fieldChecked93_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field93_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts93_2.2

theorem baseChecked94 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding94.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding94.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries208 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts94_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe94_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field94_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field94_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries208 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank94_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe94_0 = true := fieldFacts94_0.1

theorem fieldChecked94_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field94_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts94_0.2

theorem fieldFacts94_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe94_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field94_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field94_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries216 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank94_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe94_1 = true := fieldFacts94_1.1

theorem fieldChecked94_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field94_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts94_1.2

theorem fieldFacts94_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe94_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field94_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field94_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries216 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank94_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe94_2 = true := fieldFacts94_2.1

theorem fieldChecked94_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field94_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts94_2.2

theorem baseChecked95 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding95.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding95.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries216 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts95_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe95_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field95_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field95_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries216 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank95_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe95_0 = true := fieldFacts95_0.1

theorem fieldChecked95_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field95_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts95_0.2

theorem fieldFacts95_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe95_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field95_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field95_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries216 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank95_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe95_1 = true := fieldFacts95_1.1

theorem fieldChecked95_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field95_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts95_1.2

theorem fieldFacts95_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe95_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field95_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field95_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries216 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank95_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe95_2 = true := fieldFacts95_2.1

theorem fieldChecked95_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field95_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts95_2.2

theorem baseChecked96 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding96.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding96.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries216 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts96_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe96_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field96_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field96_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries216 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank96_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe96_0 = true := fieldFacts96_0.1

theorem fieldChecked96_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field96_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts96_0.2

theorem fieldFacts96_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe96_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field96_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field96_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries224 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank96_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe96_1 = true := fieldFacts96_1.1

theorem fieldChecked96_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field96_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts96_1.2

theorem fieldFacts96_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe96_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field96_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field96_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries224 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank96_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe96_2 = true := fieldFacts96_2.1

theorem fieldChecked96_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field96_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts96_2.2

theorem baseChecked97 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding97.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding97.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries224 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts97_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe97_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field97_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field97_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries224 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank97_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe97_0 = true := fieldFacts97_0.1

theorem fieldChecked97_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field97_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts97_0.2

theorem fieldFacts97_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe97_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field97_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field97_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries224 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank97_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe97_1 = true := fieldFacts97_1.1

theorem fieldChecked97_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field97_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts97_1.2

theorem fieldFacts97_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe97_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field97_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field97_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries224 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank97_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe97_2 = true := fieldFacts97_2.1

theorem fieldChecked97_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field97_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts97_2.2

theorem baseChecked98 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding98.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding98.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries224 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts98_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe98_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field98_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field98_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries224 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank98_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe98_0 = true := fieldFacts98_0.1

theorem fieldChecked98_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field98_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts98_0.2

theorem fieldFacts98_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe98_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field98_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field98_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries232 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank98_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe98_1 = true := fieldFacts98_1.1

theorem fieldChecked98_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field98_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts98_1.2

theorem fieldFacts98_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe98_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field98_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field98_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries232 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank98_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe98_2 = true := fieldFacts98_2.1

theorem fieldChecked98_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field98_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts98_2.2

theorem baseChecked99 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding99.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding99.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries232 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts99_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe99_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field99_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field99_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries232 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank99_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe99_0 = true := fieldFacts99_0.1

theorem fieldChecked99_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field99_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts99_0.2

theorem fieldFacts99_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe99_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field99_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field99_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries232 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank99_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe99_1 = true := fieldFacts99_1.1

theorem fieldChecked99_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field99_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts99_1.2

theorem fieldFacts99_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe99_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field99_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field99_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries232 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank99_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe99_2 = true := fieldFacts99_2.1

theorem fieldChecked99_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field99_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts99_2.2

theorem baseChecked100 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding100.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding100.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries232 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts100_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe100_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field100_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field100_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries232 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank100_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe100_0 = true := fieldFacts100_0.1

theorem fieldChecked100_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field100_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts100_0.2

theorem fieldFacts100_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe100_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field100_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field100_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries240 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank100_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe100_1 = true := fieldFacts100_1.1

theorem fieldChecked100_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field100_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts100_1.2

theorem fieldFacts100_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe100_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field100_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field100_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries240 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank100_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe100_2 = true := fieldFacts100_2.1

theorem fieldChecked100_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field100_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts100_2.2

theorem baseChecked101 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding101.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding101.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries240 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts101_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe101_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field101_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field101_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries240 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank101_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe101_0 = true := fieldFacts101_0.1

theorem fieldChecked101_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field101_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts101_0.2

theorem fieldFacts101_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe101_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field101_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field101_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries240 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank101_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe101_1 = true := fieldFacts101_1.1

theorem fieldChecked101_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field101_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts101_1.2

theorem fieldFacts101_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe101_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field101_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field101_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries240 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank101_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe101_2 = true := fieldFacts101_2.1

theorem fieldChecked101_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field101_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts101_2.2

theorem baseChecked102 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding102.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding102.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries240 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts102_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe102_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field102_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field102_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries240 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank102_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe102_0 = true := fieldFacts102_0.1

theorem fieldChecked102_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field102_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts102_0.2

theorem fieldFacts102_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe102_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field102_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field102_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries248 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank102_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe102_1 = true := fieldFacts102_1.1

theorem fieldChecked102_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field102_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts102_1.2

theorem fieldFacts102_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe102_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field102_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field102_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries248 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank102_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe102_2 = true := fieldFacts102_2.1

theorem fieldChecked102_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field102_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts102_2.2

theorem baseChecked103 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding103.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding103.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries248 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts103_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe103_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field103_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field103_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries248 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank103_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe103_0 = true := fieldFacts103_0.1

theorem fieldChecked103_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field103_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts103_0.2

theorem fieldFacts103_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe103_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field103_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field103_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries248 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank103_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe103_1 = true := fieldFacts103_1.1

theorem fieldChecked103_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field103_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts103_1.2

theorem fieldFacts103_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe103_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field103_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field103_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries248 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank103_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe103_2 = true := fieldFacts103_2.1

theorem fieldChecked103_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field103_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts103_2.2

theorem baseChecked104 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding104.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding104.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries248 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts104_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe104_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field104_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field104_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries248 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank104_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe104_0 = true := fieldFacts104_0.1

theorem fieldChecked104_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field104_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts104_0.2

theorem fieldFacts104_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe104_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field104_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field104_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries256_checked (entries256.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries256 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank104_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe104_1 = true := fieldFacts104_1.1

theorem fieldChecked104_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field104_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts104_1.2

theorem fieldFacts104_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe104_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field104_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field104_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries256_checked (entries256.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries256 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank104_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe104_2 = true := fieldFacts104_2.1

theorem fieldChecked104_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field104_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts104_2.2

theorem baseChecked105 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding105.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding105.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries256_checked (entries256.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries256 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts105_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe105_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field105_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field105_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries256_checked (entries256.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries256 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank105_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe105_0 = true := fieldFacts105_0.1

theorem fieldChecked105_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field105_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts105_0.2

theorem fieldFacts105_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe105_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field105_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field105_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries256_checked (entries256.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries256 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank105_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe105_1 = true := fieldFacts105_1.1

theorem fieldChecked105_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field105_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts105_1.2

theorem fieldFacts105_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe105_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field105_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field105_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries256_checked (entries256.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries256 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank105_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe105_2 = true := fieldFacts105_2.1

theorem fieldChecked105_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field105_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts105_2.2

theorem baseChecked106 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding106.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding106.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries256_checked (entries256.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries256 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts106_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe106_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field106_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field106_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries256_checked (entries256.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries256 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank106_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe106_0 = true := fieldFacts106_0.1

theorem fieldChecked106_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field106_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts106_0.2

theorem fieldFacts106_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe106_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field106_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field106_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries264_checked (entries264.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries264 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank106_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe106_1 = true := fieldFacts106_1.1

theorem fieldChecked106_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field106_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts106_1.2

theorem fieldFacts106_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe106_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field106_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field106_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries264_checked (entries264.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries264 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank106_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe106_2 = true := fieldFacts106_2.1

theorem fieldChecked106_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field106_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts106_2.2

theorem baseChecked107 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding107.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding107.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries264_checked (entries264.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries264 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts107_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe107_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field107_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field107_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries264_checked (entries264.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries264 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank107_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe107_0 = true := fieldFacts107_0.1

theorem fieldChecked107_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field107_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts107_0.2

theorem fieldFacts107_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe107_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field107_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field107_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries264_checked (entries264.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries264 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank107_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe107_1 = true := fieldFacts107_1.1

theorem fieldChecked107_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field107_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts107_1.2

theorem fieldFacts107_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe107_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field107_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field107_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries264_checked (entries264.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries264 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank107_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe107_2 = true := fieldFacts107_2.1

theorem fieldChecked107_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field107_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts107_2.2

theorem baseChecked108 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding108.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding108.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries264_checked (entries264.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries264 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts108_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe108_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field108_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field108_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries264_checked (entries264.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries264 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank108_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe108_0 = true := fieldFacts108_0.1

theorem fieldChecked108_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field108_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts108_0.2

theorem fieldFacts108_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe108_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field108_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field108_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries272_checked (entries272.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries272 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank108_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe108_1 = true := fieldFacts108_1.1

theorem fieldChecked108_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field108_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts108_1.2

theorem fieldFacts108_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe108_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field108_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field108_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries272_checked (entries272.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries272 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank108_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe108_2 = true := fieldFacts108_2.1

theorem fieldChecked108_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field108_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts108_2.2

theorem baseChecked109 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding109.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding109.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries272_checked (entries272.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries272 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts109_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe109_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field109_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field109_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries272_checked (entries272.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries272 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank109_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe109_0 = true := fieldFacts109_0.1

theorem fieldChecked109_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field109_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts109_0.2

theorem fieldFacts109_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe109_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field109_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field109_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries272_checked (entries272.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries272 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank109_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe109_1 = true := fieldFacts109_1.1

theorem fieldChecked109_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field109_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts109_1.2

theorem fieldFacts109_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe109_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field109_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field109_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries272_checked (entries272.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries272 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank109_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe109_2 = true := fieldFacts109_2.1

theorem fieldChecked109_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field109_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts109_2.2

theorem baseChecked110 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding110.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding110.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries272_checked (entries272.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries272 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts110_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe110_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field110_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field110_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries272_checked (entries272.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries272 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank110_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe110_0 = true := fieldFacts110_0.1

theorem fieldChecked110_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field110_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts110_0.2

theorem fieldFacts110_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe110_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field110_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field110_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries280_checked (entries280.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries280 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank110_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe110_1 = true := fieldFacts110_1.1

theorem fieldChecked110_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field110_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts110_1.2

theorem fieldFacts110_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe110_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field110_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field110_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries280_checked (entries280.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries280 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank110_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe110_2 = true := fieldFacts110_2.1

theorem fieldChecked110_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field110_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts110_2.2

theorem baseChecked111 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding111.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding111.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries280_checked (entries280.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries280 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts111_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe111_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field111_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field111_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries280_checked (entries280.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries280 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank111_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe111_0 = true := fieldFacts111_0.1

theorem fieldChecked111_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field111_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts111_0.2

theorem fieldFacts111_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe111_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field111_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field111_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries280_checked (entries280.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries280 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank111_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe111_1 = true := fieldFacts111_1.1

theorem fieldChecked111_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field111_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts111_1.2

theorem fieldFacts111_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe111_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field111_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field111_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries280_checked (entries280.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries280 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank111_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe111_2 = true := fieldFacts111_2.1

theorem fieldChecked111_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field111_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts111_2.2

theorem baseChecked112 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding112.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding112.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries280_checked (entries280.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries280 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts112_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe112_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field112_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field112_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries280_checked (entries280.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries280 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank112_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe112_0 = true := fieldFacts112_0.1

theorem fieldChecked112_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field112_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts112_0.2

theorem fieldFacts112_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe112_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field112_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field112_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries288_checked (entries288.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries288 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank112_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe112_1 = true := fieldFacts112_1.1

theorem fieldChecked112_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field112_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts112_1.2

theorem fieldFacts112_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe112_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field112_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field112_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries288_checked (entries288.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries288 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank112_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe112_2 = true := fieldFacts112_2.1

theorem fieldChecked112_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field112_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts112_2.2

theorem baseChecked113 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding113.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding113.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries288_checked (entries288.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries288 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts113_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe113_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field113_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field113_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries288_checked (entries288.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries288 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank113_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe113_0 = true := fieldFacts113_0.1

theorem fieldChecked113_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field113_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts113_0.2

theorem fieldFacts113_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe113_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field113_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field113_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries288_checked (entries288.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries288 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank113_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe113_1 = true := fieldFacts113_1.1

theorem fieldChecked113_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field113_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts113_1.2

theorem fieldFacts113_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe113_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field113_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field113_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries288_checked (entries288.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries288 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank113_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe113_2 = true := fieldFacts113_2.1

theorem fieldChecked113_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field113_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts113_2.2

theorem baseChecked114 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding114.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding114.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries288_checked (entries288.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries288 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts114_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe114_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field114_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field114_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries288_checked (entries288.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries288 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank114_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe114_0 = true := fieldFacts114_0.1

theorem fieldChecked114_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field114_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts114_0.2

theorem fieldFacts114_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe114_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field114_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field114_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries296_checked (entries296.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries296 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank114_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe114_1 = true := fieldFacts114_1.1

theorem fieldChecked114_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field114_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts114_1.2

theorem fieldFacts114_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe114_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field114_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field114_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries296_checked (entries296.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries296 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank114_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe114_2 = true := fieldFacts114_2.1

theorem fieldChecked114_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field114_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts114_2.2

theorem baseChecked115 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding115.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding115.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries296_checked (entries296.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries296 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts115_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe115_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field115_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field115_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries296_checked (entries296.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries296 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank115_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe115_0 = true := fieldFacts115_0.1

theorem fieldChecked115_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field115_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts115_0.2

theorem fieldFacts115_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe115_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field115_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field115_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries296_checked (entries296.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries296 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank115_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe115_1 = true := fieldFacts115_1.1

theorem fieldChecked115_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field115_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts115_1.2

theorem fieldFacts115_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe115_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field115_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field115_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries296_checked (entries296.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries296 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank115_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe115_2 = true := fieldFacts115_2.1

theorem fieldChecked115_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field115_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts115_2.2

theorem baseChecked116 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding116.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding116.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries296_checked (entries296.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries296 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts116_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe116_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field116_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field116_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries296_checked (entries296.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries296 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank116_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe116_0 = true := fieldFacts116_0.1

theorem fieldChecked116_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field116_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts116_0.2

theorem fieldFacts116_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe116_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field116_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field116_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries304_checked (entries304.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries304 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank116_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe116_1 = true := fieldFacts116_1.1

theorem fieldChecked116_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field116_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts116_1.2

theorem fieldFacts116_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe116_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field116_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field116_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries304_checked (entries304.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries304 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank116_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe116_2 = true := fieldFacts116_2.1

theorem fieldChecked116_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field116_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts116_2.2

theorem baseChecked117 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding117.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding117.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries304_checked (entries304.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries304 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts117_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe117_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field117_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field117_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries304_checked (entries304.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries304 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank117_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe117_0 = true := fieldFacts117_0.1

theorem fieldChecked117_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field117_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts117_0.2

theorem fieldFacts117_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe117_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field117_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field117_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries304_checked (entries304.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries304 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank117_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe117_1 = true := fieldFacts117_1.1

theorem fieldChecked117_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field117_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts117_1.2

theorem fieldFacts117_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe117_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field117_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field117_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries304_checked (entries304.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries304 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank117_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe117_2 = true := fieldFacts117_2.1

theorem fieldChecked117_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field117_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts117_2.2

theorem baseChecked118 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding118.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding118.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries304_checked (entries304.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries304 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts118_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe118_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field118_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field118_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries304_checked (entries304.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries304 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank118_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe118_0 = true := fieldFacts118_0.1

theorem fieldChecked118_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field118_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts118_0.2

theorem fieldFacts118_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe118_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field118_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field118_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries312_checked (entries312.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries312 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank118_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe118_1 = true := fieldFacts118_1.1

theorem fieldChecked118_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field118_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts118_1.2

theorem fieldFacts118_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe118_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field118_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field118_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries312_checked (entries312.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries312 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank118_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe118_2 = true := fieldFacts118_2.1

theorem fieldChecked118_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field118_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts118_2.2

theorem baseChecked119 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding119.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding119.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries312_checked (entries312.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries312 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts119_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe119_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field119_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field119_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries312_checked (entries312.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries312 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank119_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe119_0 = true := fieldFacts119_0.1

theorem fieldChecked119_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field119_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts119_0.2

theorem fieldFacts119_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe119_1 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field119_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field119_1 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries312_checked (entries312.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries312 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank119_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe119_1 = true := fieldFacts119_1.1

theorem fieldChecked119_1 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field119_1.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts119_1.2

theorem fieldFacts119_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe119_2 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field119_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field119_2 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries312_checked (entries312.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries312 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank119_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe119_2 = true := fieldFacts119_2.1

theorem fieldChecked119_2 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field119_2.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts119_2.2

theorem baseChecked120 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding120.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding120.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries312_checked (entries312.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries312 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts120_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe120_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field120_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field120_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries312_checked (entries312.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries312 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank120_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe120_0 = true := fieldFacts120_0.1

theorem fieldChecked120_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field120_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts120_0.2

theorem baseChecked121 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding121.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding121.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries320_checked (entries320.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries320 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts121_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe121_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field121_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field121_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries320_checked (entries320.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries320 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank121_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe121_0 = true := fieldFacts121_0.1

theorem fieldChecked121_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field121_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts121_0.2

theorem baseChecked122 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding122.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding122.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries320_checked (entries320.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries320 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts122_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe122_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field122_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field122_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries320_checked (entries320.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries320 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank122_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe122_0 = true := fieldFacts122_0.1

theorem fieldChecked122_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field122_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts122_0.2

theorem baseChecked123 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding123.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding123.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries320_checked (entries320.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries320 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts123_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe123_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field123_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field123_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries320_checked (entries320.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries320 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank123_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe123_0 = true := fieldFacts123_0.1

theorem fieldChecked123_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field123_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts123_0.2

theorem baseChecked124 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding124.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding124.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries320_checked (entries320.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries320 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts124_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe124_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field124_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field124_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries320_checked (entries320.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries320 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank124_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe124_0 = true := fieldFacts124_0.1

theorem fieldChecked124_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field124_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts124_0.2

theorem baseChecked125 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding125.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding125.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries328_checked (entries328.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries328 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts125_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe125_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field125_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field125_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries328_checked (entries328.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries328 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank125_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe125_0 = true := fieldFacts125_0.1

theorem fieldChecked125_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field125_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts125_0.2

theorem baseChecked126 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding126.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding126.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries328_checked (entries328.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries328 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts126_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe126_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field126_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field126_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries328_checked (entries328.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries328 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank126_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe126_0 = true := fieldFacts126_0.1

theorem fieldChecked126_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field126_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts126_0.2

theorem baseChecked127 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding127.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding127.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries328_checked (entries328.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries328 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts127_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe127_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field127_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field127_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries328_checked (entries328.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries328 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank127_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe127_0 = true := fieldFacts127_0.1

theorem fieldChecked127_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field127_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts127_0.2

theorem baseChecked128 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding128.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding128.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries328_checked (entries328.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries328 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts128_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe128_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field128_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field128_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries328_checked (entries328.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries328 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank128_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe128_0 = true := fieldFacts128_0.1

theorem fieldChecked128_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field128_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts128_0.2

theorem baseChecked129 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding129.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding129.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries336_checked (entries336.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries336 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts129_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe129_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field129_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field129_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries336_checked (entries336.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries336 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank129_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe129_0 = true := fieldFacts129_0.1

theorem fieldChecked129_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field129_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts129_0.2

theorem baseChecked130 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding130.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding130.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries336_checked (entries336.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries336 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts130_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe130_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field130_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field130_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries336_checked (entries336.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries336 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank130_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe130_0 = true := fieldFacts130_0.1

theorem fieldChecked130_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field130_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts130_0.2

theorem baseChecked131 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding131.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding131.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries336_checked (entries336.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries336 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts131_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe131_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field131_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field131_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries336_checked (entries336.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries336 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank131_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe131_0 = true := fieldFacts131_0.1

theorem fieldChecked131_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field131_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts131_0.2

theorem baseChecked132 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding132.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding132.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries336_checked (entries336.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries336 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts132_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe132_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field132_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field132_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries336_checked (entries336.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries336 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank132_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe132_0 = true := fieldFacts132_0.1

theorem fieldChecked132_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field132_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts132_0.2

theorem baseChecked133 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding133.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding133.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries344_checked (entries344.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries344 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts133_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe133_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field133_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field133_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries344_checked (entries344.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries344 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank133_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe133_0 = true := fieldFacts133_0.1

theorem fieldChecked133_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field133_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts133_0.2

theorem baseChecked134 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding134.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding134.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries344_checked (entries344.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries344 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts134_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe134_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field134_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field134_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries344_checked (entries344.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries344 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank134_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe134_0 = true := fieldFacts134_0.1

theorem fieldChecked134_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field134_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts134_0.2

theorem baseChecked135 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding135.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding135.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries344_checked (entries344.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries344 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts135_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe135_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field135_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field135_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries344_checked (entries344.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries344 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank135_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe135_0 = true := fieldFacts135_0.1

theorem fieldChecked135_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field135_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts135_0.2

theorem baseChecked136 : Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding136.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.encoding136.baseCheck Airbender.Compiler.ConsumerNative.BigintCached.native.typing)).check = true :=
    List.all_eq_true.mp entries344_checked (entries344.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries344 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts136_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe136_0 = true ∧ Airbender.Compiler.LookupSourceNative.BigintCached.native.field136_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BigintCached.native.field136_0 Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank).check = true :=
    List.all_eq_true.mp entries344_checked (entries344.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries344 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank136_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.check Airbender.Compiler.LookupSourceNative.BigintCached.native.recipe136_0 = true := fieldFacts136_0.1

theorem fieldChecked136_0 : Airbender.Compiler.LookupSourceNative.BigintCached.native.field136_0.check Airbender.Compiler.LookupNative.BigintCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BigintCached.native.bank.placement = true := fieldFacts136_0.2

theorem genericSetupChecked : Airbender.Compiler.LookupSourceNative.BigintCached.native.leaf59.isSetup = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.leaf59.isSetup)).check = true :=
    List.all_eq_true.mp entries352_checked (entries352.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries352 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem genericSourceCoverage : decide (((Airbender.Compiler.LookupNative.BigintCached.native.genericTree).leaves.map Airbender.Compiler.LookupSourceNative.BigintCached.native.genericLabel).Perm (List.range (Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.length + 1))) = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (decide (((Airbender.Compiler.LookupNative.BigintCached.native.genericTree).leaves.map Airbender.Compiler.LookupSourceNative.BigintCached.native.genericLabel).Perm (List.range (Airbender.Compiler.LookupSourceNative.BigintCached.native.genericQueries.length + 1))))).check = true :=
    List.all_eq_true.mp entries352_checked (entries352.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries352 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem range16SetupChecked : Airbender.Compiler.LookupSourceNative.BigintCached.native.leaf1.isSetup = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (Airbender.Compiler.LookupSourceNative.BigintCached.native.leaf1.isSetup)).check = true :=
    List.all_eq_true.mp entries352_checked (entries352.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries352 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem range16SourceCoverage : decide (((Airbender.Compiler.LookupNative.BigintCached.native.range16Tree).leaves.map Airbender.Compiler.LookupSourceNative.BigintCached.native.range16Label).Perm (List.range (Airbender.Compiler.LookupSourceNative.BigintCached.native.range16Queries.length + 1))) = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 222) (decide (((Airbender.Compiler.LookupNative.BigintCached.native.range16Tree).leaves.map Airbender.Compiler.LookupSourceNative.BigintCached.native.range16Label).Perm (List.range (Airbender.Compiler.LookupSourceNative.BigintCached.native.range16Queries.length + 1))))).check = true :=
    List.all_eq_true.mp entries352_checked (entries352.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries352 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

end Airbender.Compiler.LookupSourceChecks.BigintCached
