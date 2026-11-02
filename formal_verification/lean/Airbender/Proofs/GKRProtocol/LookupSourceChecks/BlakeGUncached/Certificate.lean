import Airbender.Proofs.GKRProtocol.LookupSourceChecks.BlakeGUncached.Bindings
import Airbender.Proofs.GKRProtocol.NumericCleanArgumentChecks

namespace Airbender.Compiler.LookupSourceChecks.BlakeGUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=
  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked

noncomputable def entries0 := [
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding0.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding1.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding2.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding3.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding4.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding5.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding6.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding7.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem entries0_binding : ((originalEntries.drop 0).take 8) = entries0 := by rfl

theorem entries0_checked : entries0.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries0_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 0 8

noncomputable def entries8 := [
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding8.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding9.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding10.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding11.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding12.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding13.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding14.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding15.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem entries8_binding : ((originalEntries.drop 8).take 8) = entries8 := by rfl

theorem entries8_checked : entries8.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries8_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 8 8

noncomputable def entries16 := [
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding16.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding17.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding18.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding19.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding20.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding21.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding22.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank]

theorem entries16_binding : ((originalEntries.drop 16).take 8) = entries16 := by rfl

theorem entries16_checked : entries16.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries16_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 16 8

noncomputable def entries24 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank]

theorem entries24_binding : ((originalEntries.drop 24).take 8) = entries24 := by rfl

theorem entries24_checked : entries24.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries24_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 24 8

noncomputable def entries32 := [
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding23.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding24.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank]

theorem entries32_binding : ((originalEntries.drop 32).take 8) = entries32 := by rfl

theorem entries32_checked : entries32.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries32_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 32 8

noncomputable def entries40 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding25.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank]

theorem entries40_binding : ((originalEntries.drop 40).take 8) = entries40 := by rfl

theorem entries40_checked : entries40.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries40_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 40 8

noncomputable def entries48 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding26.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank]

theorem entries48_binding : ((originalEntries.drop 48).take 8) = entries48 := by rfl

theorem entries48_checked : entries48.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries48_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 48 8

noncomputable def entries56 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding27.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem entries56_binding : ((originalEntries.drop 56).take 8) = entries56 := by rfl

theorem entries56_checked : entries56.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries56_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 56 8

noncomputable def entries64 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank]

theorem entries64_binding : ((originalEntries.drop 64).take 8) = entries64 := by rfl

theorem entries64_checked : entries64.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries64_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 64 8

noncomputable def entries72 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding28.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank]

theorem entries72_binding : ((originalEntries.drop 72).take 8) = entries72 := by rfl

theorem entries72_checked : entries72.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries72_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 72 8

noncomputable def entries80 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding29.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank]

theorem entries80_binding : ((originalEntries.drop 80).take 8) = entries80 := by rfl

theorem entries80_checked : entries80.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries80_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 80 8

noncomputable def entries88 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding30.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank]

theorem entries88_binding : ((originalEntries.drop 88).take 8) = entries88 := by rfl

theorem entries88_checked : entries88.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries88_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 88 8

noncomputable def entries96 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding31.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem entries96_binding : ((originalEntries.drop 96).take 8) = entries96 := by rfl

theorem entries96_checked : entries96.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries96_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 96 8

noncomputable def entries104 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank]

theorem entries104_binding : ((originalEntries.drop 104).take 8) = entries104 := by rfl

theorem entries104_checked : entries104.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries104_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 104 8

noncomputable def entries112 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding32.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank]

theorem entries112_binding : ((originalEntries.drop 112).take 8) = entries112 := by rfl

theorem entries112_checked : entries112.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries112_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 112 8

noncomputable def entries120 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding33.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank]

theorem entries120_binding : ((originalEntries.drop 120).take 8) = entries120 := by rfl

theorem entries120_checked : entries120.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries120_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 120 8

noncomputable def entries128 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding34.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank]

theorem entries128_binding : ((originalEntries.drop 128).take 8) = entries128 := by rfl

theorem entries128_checked : entries128.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries128_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 128 8

noncomputable def entries136 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding35.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem entries136_binding : ((originalEntries.drop 136).take 8) = entries136 := by rfl

theorem entries136_checked : entries136.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries136_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 136 8

noncomputable def entries144 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank]

theorem entries144_binding : ((originalEntries.drop 144).take 8) = entries144 := by rfl

theorem entries144_checked : entries144.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries144_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 144 8

noncomputable def entries152 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding36.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank]

theorem entries152_binding : ((originalEntries.drop 152).take 8) = entries152 := by rfl

theorem entries152_checked : entries152.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries152_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 152 8

noncomputable def entries160 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding37.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank]

theorem entries160_binding : ((originalEntries.drop 160).take 8) = entries160 := by rfl

theorem entries160_checked : entries160.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries160_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 160 8

noncomputable def entries168 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding38.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank]

theorem entries168_binding : ((originalEntries.drop 168).take 8) = entries168 := by rfl

theorem entries168_checked : entries168.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries168_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 168 8

noncomputable def entries176 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding39.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)]

theorem entries176_binding : ((originalEntries.drop 176).take 8) = entries176 := by rfl

theorem entries176_checked : entries176.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries176_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 176 8

noncomputable def entries184 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank]

theorem entries184_binding : ((originalEntries.drop 184).take 8) = entries184 := by rfl

theorem entries184_checked : entries184.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries184_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 184 8

noncomputable def entries192 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding40.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank]

theorem entries192_binding : ((originalEntries.drop 192).take 8) = entries192 := by rfl

theorem entries192_checked : entries192.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries192_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 192 8

noncomputable def entries200 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding41.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank]

theorem entries200_binding : ((originalEntries.drop 200).take 8) = entries200 := by rfl

theorem entries200_checked : entries200.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries200_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 200 8

noncomputable def entries208 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.leaf23.isSetup),
  NumericLookupSourceChecks.ofFlag (n := 87) (decide (((Airbender.Compiler.LookupNative.BlakeGUncached.native.genericTree).leaves.map Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.genericLabel).Perm (List.range (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.genericQueries.length + 1))))]

theorem entries208_binding : ((originalEntries.drop 208).take 7) = entries208 := by rfl

theorem entries208_checked : entries208.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries208_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 208 7

theorem baseChecked0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding0.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding0.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries0 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding1.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding1.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries0 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding2.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding2.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries0 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding3.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding3.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries0 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding4.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding4.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries0 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding5.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding5.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries0 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding6.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding6.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries0 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding7.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding7.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries0 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding8.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding8.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries8 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked9 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding9.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding9.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries8 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked10 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding10.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding10.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries8 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked11 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding11.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding11.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries8 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked12 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding12.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding12.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries8 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked13 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding13.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding13.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries8 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked14 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding14.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding14.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries8 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked15 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding15.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding15.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries8 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked16 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding16.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding16.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries16 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked17 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding17.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding17.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries16 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked18 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding18.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding18.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries16 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked19 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding19.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding19.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries16 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked20 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding20.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding20.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries16 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked21 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding21.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding21.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries16 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked22 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding22.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding22.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries16 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts22_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe22_0 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries16 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank22_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe22_0 = true := fieldFacts22_0.1

theorem fieldChecked22_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts22_0.2

theorem fieldFacts22_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe22_1 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries24 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank22_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe22_1 = true := fieldFacts22_1.1

theorem fieldChecked22_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts22_1.2

theorem fieldFacts22_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe22_2 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries24 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank22_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe22_2 = true := fieldFacts22_2.1

theorem fieldChecked22_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts22_2.2

theorem fieldFacts22_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe22_3 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries24 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank22_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe22_3 = true := fieldFacts22_3.1

theorem fieldChecked22_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts22_3.2

theorem fieldFacts22_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe22_4 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries24 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank22_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe22_4 = true := fieldFacts22_4.1

theorem fieldChecked22_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts22_4.2

theorem fieldFacts22_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe22_5 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries24 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank22_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe22_5 = true := fieldFacts22_5.1

theorem fieldChecked22_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts22_5.2

theorem fieldFacts22_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe22_6 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries24 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank22_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe22_6 = true := fieldFacts22_6.1

theorem fieldChecked22_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts22_6.2

theorem fieldFacts22_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe22_7 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries24 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank22_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe22_7 = true := fieldFacts22_7.1

theorem fieldChecked22_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts22_7.2

theorem fieldFacts22_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe22_8 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries24 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank22_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe22_8 = true := fieldFacts22_8.1

theorem fieldChecked22_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field22_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts22_8.2

theorem baseChecked23 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding23.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding23.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries32 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked24 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding24.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding24.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries32 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts24_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe24_0 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries32 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank24_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe24_0 = true := fieldFacts24_0.1

theorem fieldChecked24_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts24_0.2

theorem fieldFacts24_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe24_1 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries32 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank24_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe24_1 = true := fieldFacts24_1.1

theorem fieldChecked24_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts24_1.2

theorem fieldFacts24_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe24_2 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries32 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank24_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe24_2 = true := fieldFacts24_2.1

theorem fieldChecked24_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts24_2.2

theorem fieldFacts24_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe24_3 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries32 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank24_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe24_3 = true := fieldFacts24_3.1

theorem fieldChecked24_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts24_3.2

theorem fieldFacts24_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe24_4 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries32 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank24_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe24_4 = true := fieldFacts24_4.1

theorem fieldChecked24_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts24_4.2

theorem fieldFacts24_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe24_5 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries32 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank24_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe24_5 = true := fieldFacts24_5.1

theorem fieldChecked24_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts24_5.2

theorem fieldFacts24_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe24_6 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries40 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank24_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe24_6 = true := fieldFacts24_6.1

theorem fieldChecked24_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts24_6.2

theorem fieldFacts24_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe24_7 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries40 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank24_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe24_7 = true := fieldFacts24_7.1

theorem fieldChecked24_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts24_7.2

theorem fieldFacts24_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe24_8 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries40 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank24_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe24_8 = true := fieldFacts24_8.1

theorem fieldChecked24_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field24_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts24_8.2

theorem baseChecked25 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding25.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding25.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries40 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts25_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe25_0 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries40 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank25_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe25_0 = true := fieldFacts25_0.1

theorem fieldChecked25_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts25_0.2

theorem fieldFacts25_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe25_1 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries40 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank25_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe25_1 = true := fieldFacts25_1.1

theorem fieldChecked25_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts25_1.2

theorem fieldFacts25_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe25_2 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries40 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank25_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe25_2 = true := fieldFacts25_2.1

theorem fieldChecked25_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts25_2.2

theorem fieldFacts25_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe25_3 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries40 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank25_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe25_3 = true := fieldFacts25_3.1

theorem fieldChecked25_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts25_3.2

theorem fieldFacts25_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe25_4 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries48 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank25_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe25_4 = true := fieldFacts25_4.1

theorem fieldChecked25_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts25_4.2

theorem fieldFacts25_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe25_5 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries48 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank25_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe25_5 = true := fieldFacts25_5.1

theorem fieldChecked25_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts25_5.2

theorem fieldFacts25_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe25_6 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries48 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank25_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe25_6 = true := fieldFacts25_6.1

theorem fieldChecked25_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts25_6.2

theorem fieldFacts25_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe25_7 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries48 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank25_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe25_7 = true := fieldFacts25_7.1

theorem fieldChecked25_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts25_7.2

theorem fieldFacts25_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe25_8 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries48 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank25_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe25_8 = true := fieldFacts25_8.1

theorem fieldChecked25_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field25_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts25_8.2

theorem baseChecked26 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding26.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding26.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries48 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts26_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe26_0 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries48 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank26_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe26_0 = true := fieldFacts26_0.1

theorem fieldChecked26_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts26_0.2

theorem fieldFacts26_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe26_1 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries48 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank26_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe26_1 = true := fieldFacts26_1.1

theorem fieldChecked26_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts26_1.2

theorem fieldFacts26_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe26_2 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries56 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank26_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe26_2 = true := fieldFacts26_2.1

theorem fieldChecked26_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts26_2.2

theorem fieldFacts26_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe26_3 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries56 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank26_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe26_3 = true := fieldFacts26_3.1

theorem fieldChecked26_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts26_3.2

theorem fieldFacts26_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe26_4 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries56 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank26_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe26_4 = true := fieldFacts26_4.1

theorem fieldChecked26_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts26_4.2

theorem fieldFacts26_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe26_5 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries56 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank26_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe26_5 = true := fieldFacts26_5.1

theorem fieldChecked26_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts26_5.2

theorem fieldFacts26_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe26_6 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries56 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank26_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe26_6 = true := fieldFacts26_6.1

theorem fieldChecked26_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts26_6.2

theorem fieldFacts26_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe26_7 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries56 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank26_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe26_7 = true := fieldFacts26_7.1

theorem fieldChecked26_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts26_7.2

theorem fieldFacts26_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe26_8 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries56 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank26_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe26_8 = true := fieldFacts26_8.1

theorem fieldChecked26_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field26_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts26_8.2

theorem baseChecked27 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding27.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding27.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries56 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts27_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe27_0 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries64 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank27_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe27_0 = true := fieldFacts27_0.1

theorem fieldChecked27_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts27_0.2

theorem fieldFacts27_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe27_1 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries64 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank27_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe27_1 = true := fieldFacts27_1.1

theorem fieldChecked27_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts27_1.2

theorem fieldFacts27_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe27_2 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries64 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank27_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe27_2 = true := fieldFacts27_2.1

theorem fieldChecked27_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts27_2.2

theorem fieldFacts27_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe27_3 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries64 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank27_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe27_3 = true := fieldFacts27_3.1

theorem fieldChecked27_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts27_3.2

theorem fieldFacts27_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe27_4 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries64 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank27_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe27_4 = true := fieldFacts27_4.1

theorem fieldChecked27_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts27_4.2

theorem fieldFacts27_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe27_5 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries64 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank27_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe27_5 = true := fieldFacts27_5.1

theorem fieldChecked27_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts27_5.2

theorem fieldFacts27_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe27_6 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries64 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank27_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe27_6 = true := fieldFacts27_6.1

theorem fieldChecked27_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts27_6.2

theorem fieldFacts27_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe27_7 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries64 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank27_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe27_7 = true := fieldFacts27_7.1

theorem fieldChecked27_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts27_7.2

theorem fieldFacts27_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe27_8 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries72 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank27_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe27_8 = true := fieldFacts27_8.1

theorem fieldChecked27_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field27_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts27_8.2

theorem baseChecked28 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding28.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding28.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries72 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts28_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe28_0 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries72 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank28_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe28_0 = true := fieldFacts28_0.1

theorem fieldChecked28_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts28_0.2

theorem fieldFacts28_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe28_1 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries72 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank28_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe28_1 = true := fieldFacts28_1.1

theorem fieldChecked28_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts28_1.2

theorem fieldFacts28_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe28_2 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries72 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank28_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe28_2 = true := fieldFacts28_2.1

theorem fieldChecked28_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts28_2.2

theorem fieldFacts28_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe28_3 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries72 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank28_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe28_3 = true := fieldFacts28_3.1

theorem fieldChecked28_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts28_3.2

theorem fieldFacts28_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe28_4 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries72 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank28_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe28_4 = true := fieldFacts28_4.1

theorem fieldChecked28_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts28_4.2

theorem fieldFacts28_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe28_5 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries72 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank28_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe28_5 = true := fieldFacts28_5.1

theorem fieldChecked28_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts28_5.2

theorem fieldFacts28_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe28_6 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries80 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank28_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe28_6 = true := fieldFacts28_6.1

theorem fieldChecked28_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts28_6.2

theorem fieldFacts28_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe28_7 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries80 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank28_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe28_7 = true := fieldFacts28_7.1

theorem fieldChecked28_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts28_7.2

theorem fieldFacts28_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe28_8 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries80 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank28_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe28_8 = true := fieldFacts28_8.1

theorem fieldChecked28_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field28_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts28_8.2

theorem baseChecked29 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding29.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding29.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries80 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts29_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe29_0 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries80 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank29_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe29_0 = true := fieldFacts29_0.1

theorem fieldChecked29_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts29_0.2

theorem fieldFacts29_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe29_1 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries80 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank29_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe29_1 = true := fieldFacts29_1.1

theorem fieldChecked29_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts29_1.2

theorem fieldFacts29_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe29_2 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries80 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank29_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe29_2 = true := fieldFacts29_2.1

theorem fieldChecked29_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts29_2.2

theorem fieldFacts29_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe29_3 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries80 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank29_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe29_3 = true := fieldFacts29_3.1

theorem fieldChecked29_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts29_3.2

theorem fieldFacts29_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe29_4 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries88 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank29_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe29_4 = true := fieldFacts29_4.1

theorem fieldChecked29_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts29_4.2

theorem fieldFacts29_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe29_5 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries88 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank29_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe29_5 = true := fieldFacts29_5.1

theorem fieldChecked29_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts29_5.2

theorem fieldFacts29_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe29_6 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries88 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank29_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe29_6 = true := fieldFacts29_6.1

theorem fieldChecked29_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts29_6.2

theorem fieldFacts29_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe29_7 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries88 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank29_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe29_7 = true := fieldFacts29_7.1

theorem fieldChecked29_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts29_7.2

theorem fieldFacts29_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe29_8 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries88 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank29_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe29_8 = true := fieldFacts29_8.1

theorem fieldChecked29_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field29_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts29_8.2

theorem baseChecked30 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding30.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding30.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries88 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts30_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe30_0 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries88 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank30_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe30_0 = true := fieldFacts30_0.1

theorem fieldChecked30_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts30_0.2

theorem fieldFacts30_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe30_1 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries88 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank30_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe30_1 = true := fieldFacts30_1.1

theorem fieldChecked30_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts30_1.2

theorem fieldFacts30_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe30_2 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries96 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank30_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe30_2 = true := fieldFacts30_2.1

theorem fieldChecked30_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts30_2.2

theorem fieldFacts30_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe30_3 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries96 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank30_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe30_3 = true := fieldFacts30_3.1

theorem fieldChecked30_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts30_3.2

theorem fieldFacts30_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe30_4 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries96 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank30_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe30_4 = true := fieldFacts30_4.1

theorem fieldChecked30_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts30_4.2

theorem fieldFacts30_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe30_5 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries96 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank30_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe30_5 = true := fieldFacts30_5.1

theorem fieldChecked30_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts30_5.2

theorem fieldFacts30_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe30_6 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries96 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank30_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe30_6 = true := fieldFacts30_6.1

theorem fieldChecked30_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts30_6.2

theorem fieldFacts30_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe30_7 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries96 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank30_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe30_7 = true := fieldFacts30_7.1

theorem fieldChecked30_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts30_7.2

theorem fieldFacts30_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe30_8 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries96 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank30_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe30_8 = true := fieldFacts30_8.1

theorem fieldChecked30_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field30_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts30_8.2

theorem baseChecked31 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding31.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding31.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries96 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts31_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe31_0 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries104 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank31_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe31_0 = true := fieldFacts31_0.1

theorem fieldChecked31_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts31_0.2

theorem fieldFacts31_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe31_1 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries104 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank31_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe31_1 = true := fieldFacts31_1.1

theorem fieldChecked31_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts31_1.2

theorem fieldFacts31_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe31_2 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries104 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank31_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe31_2 = true := fieldFacts31_2.1

theorem fieldChecked31_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts31_2.2

theorem fieldFacts31_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe31_3 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries104 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank31_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe31_3 = true := fieldFacts31_3.1

theorem fieldChecked31_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts31_3.2

theorem fieldFacts31_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe31_4 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries104 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank31_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe31_4 = true := fieldFacts31_4.1

theorem fieldChecked31_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts31_4.2

theorem fieldFacts31_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe31_5 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries104 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank31_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe31_5 = true := fieldFacts31_5.1

theorem fieldChecked31_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts31_5.2

theorem fieldFacts31_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe31_6 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries104 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank31_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe31_6 = true := fieldFacts31_6.1

theorem fieldChecked31_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts31_6.2

theorem fieldFacts31_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe31_7 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries104 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank31_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe31_7 = true := fieldFacts31_7.1

theorem fieldChecked31_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts31_7.2

theorem fieldFacts31_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe31_8 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries112 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank31_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe31_8 = true := fieldFacts31_8.1

theorem fieldChecked31_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field31_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts31_8.2

theorem baseChecked32 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding32.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding32.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries112 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts32_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe32_0 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries112 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank32_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe32_0 = true := fieldFacts32_0.1

theorem fieldChecked32_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts32_0.2

theorem fieldFacts32_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe32_1 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries112 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank32_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe32_1 = true := fieldFacts32_1.1

theorem fieldChecked32_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts32_1.2

theorem fieldFacts32_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe32_2 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries112 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank32_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe32_2 = true := fieldFacts32_2.1

theorem fieldChecked32_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts32_2.2

theorem fieldFacts32_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe32_3 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries112 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank32_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe32_3 = true := fieldFacts32_3.1

theorem fieldChecked32_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts32_3.2

theorem fieldFacts32_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe32_4 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries112 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank32_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe32_4 = true := fieldFacts32_4.1

theorem fieldChecked32_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts32_4.2

theorem fieldFacts32_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe32_5 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries112 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank32_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe32_5 = true := fieldFacts32_5.1

theorem fieldChecked32_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts32_5.2

theorem fieldFacts32_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe32_6 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries120 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank32_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe32_6 = true := fieldFacts32_6.1

theorem fieldChecked32_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts32_6.2

theorem fieldFacts32_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe32_7 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries120 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank32_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe32_7 = true := fieldFacts32_7.1

theorem fieldChecked32_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts32_7.2

theorem fieldFacts32_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe32_8 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries120 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank32_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe32_8 = true := fieldFacts32_8.1

theorem fieldChecked32_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field32_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts32_8.2

theorem baseChecked33 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding33.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding33.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries120 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts33_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe33_0 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries120 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank33_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe33_0 = true := fieldFacts33_0.1

theorem fieldChecked33_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts33_0.2

theorem fieldFacts33_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe33_1 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries120 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank33_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe33_1 = true := fieldFacts33_1.1

theorem fieldChecked33_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts33_1.2

theorem fieldFacts33_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe33_2 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries120 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank33_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe33_2 = true := fieldFacts33_2.1

theorem fieldChecked33_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts33_2.2

theorem fieldFacts33_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe33_3 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries120 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank33_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe33_3 = true := fieldFacts33_3.1

theorem fieldChecked33_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts33_3.2

theorem fieldFacts33_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe33_4 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries128 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank33_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe33_4 = true := fieldFacts33_4.1

theorem fieldChecked33_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts33_4.2

theorem fieldFacts33_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe33_5 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries128 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank33_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe33_5 = true := fieldFacts33_5.1

theorem fieldChecked33_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts33_5.2

theorem fieldFacts33_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe33_6 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries128 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank33_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe33_6 = true := fieldFacts33_6.1

theorem fieldChecked33_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts33_6.2

theorem fieldFacts33_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe33_7 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries128 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank33_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe33_7 = true := fieldFacts33_7.1

theorem fieldChecked33_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts33_7.2

theorem fieldFacts33_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe33_8 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries128 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank33_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe33_8 = true := fieldFacts33_8.1

theorem fieldChecked33_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field33_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts33_8.2

theorem baseChecked34 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding34.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding34.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries128 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts34_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe34_0 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries128 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank34_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe34_0 = true := fieldFacts34_0.1

theorem fieldChecked34_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts34_0.2

theorem fieldFacts34_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe34_1 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries128 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank34_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe34_1 = true := fieldFacts34_1.1

theorem fieldChecked34_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts34_1.2

theorem fieldFacts34_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe34_2 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries136 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank34_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe34_2 = true := fieldFacts34_2.1

theorem fieldChecked34_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts34_2.2

theorem fieldFacts34_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe34_3 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries136 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank34_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe34_3 = true := fieldFacts34_3.1

theorem fieldChecked34_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts34_3.2

theorem fieldFacts34_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe34_4 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries136 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank34_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe34_4 = true := fieldFacts34_4.1

theorem fieldChecked34_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts34_4.2

theorem fieldFacts34_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe34_5 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries136 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank34_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe34_5 = true := fieldFacts34_5.1

theorem fieldChecked34_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts34_5.2

theorem fieldFacts34_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe34_6 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries136 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank34_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe34_6 = true := fieldFacts34_6.1

theorem fieldChecked34_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts34_6.2

theorem fieldFacts34_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe34_7 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries136 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank34_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe34_7 = true := fieldFacts34_7.1

theorem fieldChecked34_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts34_7.2

theorem fieldFacts34_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe34_8 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries136 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank34_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe34_8 = true := fieldFacts34_8.1

theorem fieldChecked34_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field34_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts34_8.2

theorem baseChecked35 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding35.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding35.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries136 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts35_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe35_0 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries144 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank35_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe35_0 = true := fieldFacts35_0.1

theorem fieldChecked35_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts35_0.2

theorem fieldFacts35_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe35_1 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries144 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank35_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe35_1 = true := fieldFacts35_1.1

theorem fieldChecked35_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts35_1.2

theorem fieldFacts35_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe35_2 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries144 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank35_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe35_2 = true := fieldFacts35_2.1

theorem fieldChecked35_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts35_2.2

theorem fieldFacts35_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe35_3 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries144 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank35_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe35_3 = true := fieldFacts35_3.1

theorem fieldChecked35_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts35_3.2

theorem fieldFacts35_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe35_4 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries144 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank35_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe35_4 = true := fieldFacts35_4.1

theorem fieldChecked35_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts35_4.2

theorem fieldFacts35_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe35_5 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries144 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank35_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe35_5 = true := fieldFacts35_5.1

theorem fieldChecked35_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts35_5.2

theorem fieldFacts35_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe35_6 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries144 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank35_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe35_6 = true := fieldFacts35_6.1

theorem fieldChecked35_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts35_6.2

theorem fieldFacts35_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe35_7 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries144 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank35_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe35_7 = true := fieldFacts35_7.1

theorem fieldChecked35_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts35_7.2

theorem fieldFacts35_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe35_8 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries152 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank35_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe35_8 = true := fieldFacts35_8.1

theorem fieldChecked35_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field35_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts35_8.2

theorem baseChecked36 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding36.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding36.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries152 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts36_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe36_0 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries152 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank36_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe36_0 = true := fieldFacts36_0.1

theorem fieldChecked36_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts36_0.2

theorem fieldFacts36_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe36_1 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries152 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank36_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe36_1 = true := fieldFacts36_1.1

theorem fieldChecked36_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts36_1.2

theorem fieldFacts36_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe36_2 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries152 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank36_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe36_2 = true := fieldFacts36_2.1

theorem fieldChecked36_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts36_2.2

theorem fieldFacts36_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe36_3 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries152 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank36_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe36_3 = true := fieldFacts36_3.1

theorem fieldChecked36_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts36_3.2

theorem fieldFacts36_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe36_4 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries152 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank36_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe36_4 = true := fieldFacts36_4.1

theorem fieldChecked36_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts36_4.2

theorem fieldFacts36_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe36_5 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries152 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank36_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe36_5 = true := fieldFacts36_5.1

theorem fieldChecked36_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts36_5.2

theorem fieldFacts36_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe36_6 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries160 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank36_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe36_6 = true := fieldFacts36_6.1

theorem fieldChecked36_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts36_6.2

theorem fieldFacts36_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe36_7 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries160 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank36_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe36_7 = true := fieldFacts36_7.1

theorem fieldChecked36_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts36_7.2

theorem fieldFacts36_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe36_8 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries160 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank36_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe36_8 = true := fieldFacts36_8.1

theorem fieldChecked36_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field36_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts36_8.2

theorem baseChecked37 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding37.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding37.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries160 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts37_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe37_0 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries160 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank37_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe37_0 = true := fieldFacts37_0.1

theorem fieldChecked37_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts37_0.2

theorem fieldFacts37_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe37_1 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries160 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank37_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe37_1 = true := fieldFacts37_1.1

theorem fieldChecked37_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts37_1.2

theorem fieldFacts37_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe37_2 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries160 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank37_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe37_2 = true := fieldFacts37_2.1

theorem fieldChecked37_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts37_2.2

theorem fieldFacts37_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe37_3 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries160 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank37_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe37_3 = true := fieldFacts37_3.1

theorem fieldChecked37_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts37_3.2

theorem fieldFacts37_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe37_4 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries168 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank37_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe37_4 = true := fieldFacts37_4.1

theorem fieldChecked37_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts37_4.2

theorem fieldFacts37_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe37_5 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries168 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank37_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe37_5 = true := fieldFacts37_5.1

theorem fieldChecked37_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts37_5.2

theorem fieldFacts37_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe37_6 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries168 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank37_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe37_6 = true := fieldFacts37_6.1

theorem fieldChecked37_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts37_6.2

theorem fieldFacts37_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe37_7 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries168 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank37_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe37_7 = true := fieldFacts37_7.1

theorem fieldChecked37_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts37_7.2

theorem fieldFacts37_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe37_8 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries168 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank37_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe37_8 = true := fieldFacts37_8.1

theorem fieldChecked37_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field37_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts37_8.2

theorem baseChecked38 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding38.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding38.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries168 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts38_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe38_0 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries168 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank38_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe38_0 = true := fieldFacts38_0.1

theorem fieldChecked38_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts38_0.2

theorem fieldFacts38_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe38_1 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries168 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank38_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe38_1 = true := fieldFacts38_1.1

theorem fieldChecked38_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts38_1.2

theorem fieldFacts38_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe38_2 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries176 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank38_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe38_2 = true := fieldFacts38_2.1

theorem fieldChecked38_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts38_2.2

theorem fieldFacts38_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe38_3 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries176 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank38_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe38_3 = true := fieldFacts38_3.1

theorem fieldChecked38_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts38_3.2

theorem fieldFacts38_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe38_4 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries176 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank38_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe38_4 = true := fieldFacts38_4.1

theorem fieldChecked38_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts38_4.2

theorem fieldFacts38_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe38_5 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries176 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank38_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe38_5 = true := fieldFacts38_5.1

theorem fieldChecked38_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts38_5.2

theorem fieldFacts38_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe38_6 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries176 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank38_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe38_6 = true := fieldFacts38_6.1

theorem fieldChecked38_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts38_6.2

theorem fieldFacts38_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe38_7 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries176 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank38_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe38_7 = true := fieldFacts38_7.1

theorem fieldChecked38_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts38_7.2

theorem fieldFacts38_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe38_8 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries176 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank38_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe38_8 = true := fieldFacts38_8.1

theorem fieldChecked38_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field38_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts38_8.2

theorem baseChecked39 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding39.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding39.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries176 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts39_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe39_0 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries184 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank39_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe39_0 = true := fieldFacts39_0.1

theorem fieldChecked39_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts39_0.2

theorem fieldFacts39_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe39_1 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries184 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank39_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe39_1 = true := fieldFacts39_1.1

theorem fieldChecked39_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts39_1.2

theorem fieldFacts39_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe39_2 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries184 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank39_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe39_2 = true := fieldFacts39_2.1

theorem fieldChecked39_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts39_2.2

theorem fieldFacts39_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe39_3 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries184 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank39_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe39_3 = true := fieldFacts39_3.1

theorem fieldChecked39_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts39_3.2

theorem fieldFacts39_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe39_4 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries184 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank39_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe39_4 = true := fieldFacts39_4.1

theorem fieldChecked39_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts39_4.2

theorem fieldFacts39_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe39_5 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries184 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank39_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe39_5 = true := fieldFacts39_5.1

theorem fieldChecked39_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts39_5.2

theorem fieldFacts39_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe39_6 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries184 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank39_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe39_6 = true := fieldFacts39_6.1

theorem fieldChecked39_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts39_6.2

theorem fieldFacts39_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe39_7 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries184 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank39_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe39_7 = true := fieldFacts39_7.1

theorem fieldChecked39_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts39_7.2

theorem fieldFacts39_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe39_8 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries192 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank39_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe39_8 = true := fieldFacts39_8.1

theorem fieldChecked39_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field39_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts39_8.2

theorem baseChecked40 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding40.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding40.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries192 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts40_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe40_0 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries192 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank40_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe40_0 = true := fieldFacts40_0.1

theorem fieldChecked40_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts40_0.2

theorem fieldFacts40_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe40_1 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries192 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank40_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe40_1 = true := fieldFacts40_1.1

theorem fieldChecked40_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts40_1.2

theorem fieldFacts40_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe40_2 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries192 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank40_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe40_2 = true := fieldFacts40_2.1

theorem fieldChecked40_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts40_2.2

theorem fieldFacts40_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe40_3 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries192 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank40_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe40_3 = true := fieldFacts40_3.1

theorem fieldChecked40_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts40_3.2

theorem fieldFacts40_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe40_4 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries192 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank40_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe40_4 = true := fieldFacts40_4.1

theorem fieldChecked40_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts40_4.2

theorem fieldFacts40_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe40_5 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries192 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank40_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe40_5 = true := fieldFacts40_5.1

theorem fieldChecked40_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts40_5.2

theorem fieldFacts40_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe40_6 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries200 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank40_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe40_6 = true := fieldFacts40_6.1

theorem fieldChecked40_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts40_6.2

theorem fieldFacts40_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe40_7 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries200 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank40_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe40_7 = true := fieldFacts40_7.1

theorem fieldChecked40_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts40_7.2

theorem fieldFacts40_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe40_8 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries200 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank40_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe40_8 = true := fieldFacts40_8.1

theorem fieldChecked40_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field40_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts40_8.2

theorem baseChecked41 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding41.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.encoding41.baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing)).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries200 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts41_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe41_0 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_0 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries200 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank41_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe41_0 = true := fieldFacts41_0.1

theorem fieldChecked41_0 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_0.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts41_0.2

theorem fieldFacts41_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe41_1 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_1 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries200 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank41_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe41_1 = true := fieldFacts41_1.1

theorem fieldChecked41_1 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_1.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts41_1.2

theorem fieldFacts41_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe41_2 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_2 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries200 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank41_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe41_2 = true := fieldFacts41_2.1

theorem fieldChecked41_2 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_2.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts41_2.2

theorem fieldFacts41_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe41_3 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_3 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries200 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank41_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe41_3 = true := fieldFacts41_3.1

theorem fieldChecked41_3 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_3.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts41_3.2

theorem fieldFacts41_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe41_4 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_4 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries208 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank41_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe41_4 = true := fieldFacts41_4.1

theorem fieldChecked41_4 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_4.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts41_4.2

theorem fieldFacts41_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe41_5 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_5 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries208 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank41_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe41_5 = true := fieldFacts41_5.1

theorem fieldChecked41_5 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_5.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts41_5.2

theorem fieldFacts41_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe41_6 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_6 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries208 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank41_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe41_6 = true := fieldFacts41_6.1

theorem fieldChecked41_6 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_6.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts41_6.2

theorem fieldFacts41_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe41_7 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_7 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries208 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank41_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe41_7 = true := fieldFacts41_7.1

theorem fieldChecked41_7 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_7.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts41_7.2

theorem fieldFacts41_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe41_8 = true ∧ Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_8 Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries208 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank41_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.check Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.recipe41_8 = true := fieldFacts41_8.1

theorem fieldChecked41_8 : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.field41_8.check Airbender.Compiler.LookupNative.BlakeGUncached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.bank.placement = true := fieldFacts41_8.2

theorem genericSetupChecked : Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.leaf23.isSetup = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.leaf23.isSetup)).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries208 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem genericSourceCoverage : decide (((Airbender.Compiler.LookupNative.BlakeGUncached.native.genericTree).leaves.map Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.genericLabel).Perm (List.range (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.genericQueries.length + 1))) = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 87) (decide (((Airbender.Compiler.LookupNative.BlakeGUncached.native.genericTree).leaves.map Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.genericLabel).Perm (List.range (Airbender.Compiler.LookupSourceNative.BlakeGUncached.native.genericQueries.length + 1))))).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries208 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

end Airbender.Compiler.LookupSourceChecks.BlakeGUncached
