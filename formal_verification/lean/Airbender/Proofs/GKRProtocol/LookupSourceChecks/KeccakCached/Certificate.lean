import Airbender.Proofs.GKRProtocol.LookupSourceChecks.KeccakCached.Bindings
import Airbender.Proofs.GKRProtocol.NumericCleanArgumentChecks

namespace Airbender.Compiler.LookupSourceChecks.KeccakCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=
  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked

noncomputable def entries0 := [
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding0.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding1.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding2.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding3.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding4.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding5.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding6.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding7.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem entries0_binding : ((originalEntries.drop 0).take 8) = entries0 := by rfl

theorem entries0_checked : entries0.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries0_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 0 8

noncomputable def entries8 := [
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding8.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding9.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding10.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding11.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding12.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding13.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding14.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding15.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem entries8_binding : ((originalEntries.drop 8).take 8) = entries8 := by rfl

theorem entries8_checked : entries8.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries8_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 8 8

noncomputable def entries16 := [
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding16.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding17.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding18.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding19.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding20.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding21.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding22.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding23.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem entries16_binding : ((originalEntries.drop 16).take 8) = entries16 := by rfl

theorem entries16_checked : entries16.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries16_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 16 8

noncomputable def entries24 := [
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding24.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding25.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding26.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding27.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding28.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding29.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding30.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries24_binding : ((originalEntries.drop 24).take 8) = entries24 := by rfl

theorem entries24_checked : entries24.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries24_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 24 8

noncomputable def entries32 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding31.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem entries32_binding : ((originalEntries.drop 32).take 8) = entries32 := by rfl

theorem entries32_checked : entries32.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries32_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 32 8

noncomputable def entries40 := [
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding32.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries40_binding : ((originalEntries.drop 40).take 8) = entries40 := by rfl

theorem entries40_checked : entries40.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries40_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 40 8

noncomputable def entries48 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding33.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries48_binding : ((originalEntries.drop 48).take 8) = entries48 := by rfl

theorem entries48_checked : entries48.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries48_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 48 8

noncomputable def entries56 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding34.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries56_binding : ((originalEntries.drop 56).take 8) = entries56 := by rfl

theorem entries56_checked : entries56.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries56_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 56 8

noncomputable def entries64 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding35.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries64_binding : ((originalEntries.drop 64).take 8) = entries64 := by rfl

theorem entries64_checked : entries64.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries64_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 64 8

noncomputable def entries72 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding36.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries72_binding : ((originalEntries.drop 72).take 8) = entries72 := by rfl

theorem entries72_checked : entries72.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries72_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 72 8

noncomputable def entries80 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding37.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries80_binding : ((originalEntries.drop 80).take 8) = entries80 := by rfl

theorem entries80_checked : entries80.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries80_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 80 8

noncomputable def entries88 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding38.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries88_binding : ((originalEntries.drop 88).take 8) = entries88 := by rfl

theorem entries88_checked : entries88.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries88_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 88 8

noncomputable def entries96 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding39.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem entries96_binding : ((originalEntries.drop 96).take 8) = entries96 := by rfl

theorem entries96_checked : entries96.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries96_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 96 8

noncomputable def entries104 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries104_binding : ((originalEntries.drop 104).take 8) = entries104 := by rfl

theorem entries104_checked : entries104.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries104_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 104 8

noncomputable def entries112 := [
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding40.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries112_binding : ((originalEntries.drop 112).take 8) = entries112 := by rfl

theorem entries112_checked : entries112.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries112_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 112 8

noncomputable def entries120 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding41.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries120_binding : ((originalEntries.drop 120).take 8) = entries120 := by rfl

theorem entries120_checked : entries120.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries120_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 120 8

noncomputable def entries128 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding42.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries128_binding : ((originalEntries.drop 128).take 8) = entries128 := by rfl

theorem entries128_checked : entries128.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries128_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 128 8

noncomputable def entries136 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding43.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries136_binding : ((originalEntries.drop 136).take 8) = entries136 := by rfl

theorem entries136_checked : entries136.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries136_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 136 8

noncomputable def entries144 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding44.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries144_binding : ((originalEntries.drop 144).take 8) = entries144 := by rfl

theorem entries144_checked : entries144.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries144_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 144 8

noncomputable def entries152 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding45.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries152_binding : ((originalEntries.drop 152).take 8) = entries152 := by rfl

theorem entries152_checked : entries152.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries152_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 152 8

noncomputable def entries160 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding46.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries160_binding : ((originalEntries.drop 160).take 8) = entries160 := by rfl

theorem entries160_checked : entries160.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries160_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 160 8

noncomputable def entries168 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding47.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem entries168_binding : ((originalEntries.drop 168).take 8) = entries168 := by rfl

theorem entries168_checked : entries168.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries168_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 168 8

noncomputable def entries176 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries176_binding : ((originalEntries.drop 176).take 8) = entries176 := by rfl

theorem entries176_checked : entries176.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries176_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 176 8

noncomputable def entries184 := [
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding48.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries184_binding : ((originalEntries.drop 184).take 8) = entries184 := by rfl

theorem entries184_checked : entries184.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries184_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 184 8

noncomputable def entries192 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding49.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries192_binding : ((originalEntries.drop 192).take 8) = entries192 := by rfl

theorem entries192_checked : entries192.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries192_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 192 8

noncomputable def entries200 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding50.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries200_binding : ((originalEntries.drop 200).take 8) = entries200 := by rfl

theorem entries200_checked : entries200.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries200_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 200 8

noncomputable def entries208 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding51.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries208_binding : ((originalEntries.drop 208).take 8) = entries208 := by rfl

theorem entries208_checked : entries208.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries208_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 208 8

noncomputable def entries216 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding52.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries216_binding : ((originalEntries.drop 216).take 8) = entries216 := by rfl

theorem entries216_checked : entries216.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries216_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 216 8

noncomputable def entries224 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding53.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries224_binding : ((originalEntries.drop 224).take 8) = entries224 := by rfl

theorem entries224_checked : entries224.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries224_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 224 8

noncomputable def entries232 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding54.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries232_binding : ((originalEntries.drop 232).take 8) = entries232 := by rfl

theorem entries232_checked : entries232.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries232_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 232 8

noncomputable def entries240 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding55.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem entries240_binding : ((originalEntries.drop 240).take 8) = entries240 := by rfl

theorem entries240_checked : entries240.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries240_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 240 8

noncomputable def entries248 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries248_binding : ((originalEntries.drop 248).take 8) = entries248 := by rfl

theorem entries248_checked : entries248.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries248_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 248 8

noncomputable def entries256 := [
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding56.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries256_binding : ((originalEntries.drop 256).take 8) = entries256 := by rfl

theorem entries256_checked : entries256.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries256_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 256 8

noncomputable def entries264 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding57.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries264_binding : ((originalEntries.drop 264).take 8) = entries264 := by rfl

theorem entries264_checked : entries264.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries264_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 264 8

noncomputable def entries272 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding58.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries272_binding : ((originalEntries.drop 272).take 8) = entries272 := by rfl

theorem entries272_checked : entries272.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries272_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 272 8

noncomputable def entries280 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding59.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries280_binding : ((originalEntries.drop 280).take 8) = entries280 := by rfl

theorem entries280_checked : entries280.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries280_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 280 8

noncomputable def entries288 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding60.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries288_binding : ((originalEntries.drop 288).take 8) = entries288 := by rfl

theorem entries288_checked : entries288.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries288_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 288 8

noncomputable def entries296 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding61.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries296_binding : ((originalEntries.drop 296).take 8) = entries296 := by rfl

theorem entries296_checked : entries296.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries296_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 296 8

noncomputable def entries304 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding62.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries304_binding : ((originalEntries.drop 304).take 8) = entries304 := by rfl

theorem entries304_checked : entries304.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries304_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 304 8

noncomputable def entries312 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding63.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem entries312_binding : ((originalEntries.drop 312).take 8) = entries312 := by rfl

theorem entries312_checked : entries312.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries312_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 312 8

noncomputable def entries320 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries320_binding : ((originalEntries.drop 320).take 8) = entries320 := by rfl

theorem entries320_checked : entries320.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries320_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 320 8

noncomputable def entries328 := [
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding64.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries328_binding : ((originalEntries.drop 328).take 8) = entries328 := by rfl

theorem entries328_checked : entries328.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries328_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 328 8

noncomputable def entries336 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding65.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries336_binding : ((originalEntries.drop 336).take 8) = entries336 := by rfl

theorem entries336_checked : entries336.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries336_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 336 8

noncomputable def entries344 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding66.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries344_binding : ((originalEntries.drop 344).take 8) = entries344 := by rfl

theorem entries344_checked : entries344.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries344_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 344 8

noncomputable def entries352 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding67.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries352_binding : ((originalEntries.drop 352).take 8) = entries352 := by rfl

theorem entries352_checked : entries352.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries352_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 352 8

noncomputable def entries360 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding68.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries360_binding : ((originalEntries.drop 360).take 8) = entries360 := by rfl

theorem entries360_checked : entries360.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries360_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 360 8

noncomputable def entries368 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding69.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries368_binding : ((originalEntries.drop 368).take 8) = entries368 := by rfl

theorem entries368_checked : entries368.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries368_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 368 8

noncomputable def entries376 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding70.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries376_binding : ((originalEntries.drop 376).take 8) = entries376 := by rfl

theorem entries376_checked : entries376.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries376_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 376 8

noncomputable def entries384 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding71.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)]

theorem entries384_binding : ((originalEntries.drop 384).take 8) = entries384 := by rfl

theorem entries384_checked : entries384.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries384_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 384 8

noncomputable def entries392 := [
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank,
  NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank]

theorem entries392_binding : ((originalEntries.drop 392).take 8) = entries392 := by rfl

theorem entries392_checked : entries392.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries392_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 392 8

noncomputable def entries400 := [
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding72.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing),
  NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.leaf31.isSetup),
  NumericLookupSourceChecks.ofFlag (n := 228) (decide (((Airbender.Compiler.LookupNative.KeccakCached.native.genericTree).leaves.map Airbender.Compiler.LookupSourceNative.KeccakCached.native.genericLabel).Perm (List.range (Airbender.Compiler.LookupSourceNative.KeccakCached.native.genericQueries.length + 1))))]

theorem entries400_binding : ((originalEntries.drop 400).take 3) = entries400 := by rfl

theorem entries400_checked : entries400.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries400_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 400 3

theorem baseChecked0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding0.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding0.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries0 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding1.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding1.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries0 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding2.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding2.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries0 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding3.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding3.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries0 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding4.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding4.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries0 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding5.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding5.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries0 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding6.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding6.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries0 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding7.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding7.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries0 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked8 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding8.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding8.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries8 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked9 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding9.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding9.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries8 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked10 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding10.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding10.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries8 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked11 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding11.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding11.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries8 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked12 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding12.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding12.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries8 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked13 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding13.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding13.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries8 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked14 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding14.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding14.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries8 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked15 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding15.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding15.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries8 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked16 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding16.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding16.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries16 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked17 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding17.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding17.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries16 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked18 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding18.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding18.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries16 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked19 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding19.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding19.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries16 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked20 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding20.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding20.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries16 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked21 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding21.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding21.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries16 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked22 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding22.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding22.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries16 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked23 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding23.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding23.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries16 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked24 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding24.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding24.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries24 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked25 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding25.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding25.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries24 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked26 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding26.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding26.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries24 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked27 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding27.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding27.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries24 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked28 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding28.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding28.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries24 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked29 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding29.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding29.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries24 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked30 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding30.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding30.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries24 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts30_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe30_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries24 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank30_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe30_0 = true := fieldFacts30_0.1

theorem fieldChecked30_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts30_0.2

theorem fieldFacts30_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe30_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries32 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank30_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe30_1 = true := fieldFacts30_1.1

theorem fieldChecked30_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts30_1.2

theorem fieldFacts30_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe30_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries32 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank30_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe30_2 = true := fieldFacts30_2.1

theorem fieldChecked30_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts30_2.2

theorem fieldFacts30_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe30_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries32 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank30_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe30_3 = true := fieldFacts30_3.1

theorem fieldChecked30_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts30_3.2

theorem fieldFacts30_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe30_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries32 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank30_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe30_4 = true := fieldFacts30_4.1

theorem fieldChecked30_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts30_4.2

theorem fieldFacts30_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe30_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries32 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank30_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe30_5 = true := fieldFacts30_5.1

theorem fieldChecked30_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts30_5.2

theorem fieldFacts30_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe30_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries32 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank30_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe30_6 = true := fieldFacts30_6.1

theorem fieldChecked30_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts30_6.2

theorem fieldFacts30_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe30_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries32 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank30_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe30_7 = true := fieldFacts30_7.1

theorem fieldChecked30_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field30_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts30_7.2

theorem baseChecked31 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding31.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding31.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries32 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem baseChecked32 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding32.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding32.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries40 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts32_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe32_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries40 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank32_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe32_0 = true := fieldFacts32_0.1

theorem fieldChecked32_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts32_0.2

theorem fieldFacts32_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe32_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries40 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank32_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe32_1 = true := fieldFacts32_1.1

theorem fieldChecked32_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts32_1.2

theorem fieldFacts32_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe32_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries40 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank32_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe32_2 = true := fieldFacts32_2.1

theorem fieldChecked32_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts32_2.2

theorem fieldFacts32_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe32_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries40 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank32_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe32_3 = true := fieldFacts32_3.1

theorem fieldChecked32_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts32_3.2

theorem fieldFacts32_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe32_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries40 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank32_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe32_4 = true := fieldFacts32_4.1

theorem fieldChecked32_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts32_4.2

theorem fieldFacts32_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe32_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries40 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank32_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe32_5 = true := fieldFacts32_5.1

theorem fieldChecked32_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts32_5.2

theorem fieldFacts32_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe32_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries40 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank32_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe32_6 = true := fieldFacts32_6.1

theorem fieldChecked32_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts32_6.2

theorem fieldFacts32_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe32_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries48 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank32_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe32_7 = true := fieldFacts32_7.1

theorem fieldChecked32_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field32_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts32_7.2

theorem baseChecked33 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding33.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding33.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries48 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts33_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe33_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries48 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank33_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe33_0 = true := fieldFacts33_0.1

theorem fieldChecked33_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts33_0.2

theorem fieldFacts33_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe33_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries48 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank33_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe33_1 = true := fieldFacts33_1.1

theorem fieldChecked33_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts33_1.2

theorem fieldFacts33_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe33_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries48 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank33_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe33_2 = true := fieldFacts33_2.1

theorem fieldChecked33_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts33_2.2

theorem fieldFacts33_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe33_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries48 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank33_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe33_3 = true := fieldFacts33_3.1

theorem fieldChecked33_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts33_3.2

theorem fieldFacts33_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe33_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries48 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank33_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe33_4 = true := fieldFacts33_4.1

theorem fieldChecked33_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts33_4.2

theorem fieldFacts33_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe33_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries48 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank33_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe33_5 = true := fieldFacts33_5.1

theorem fieldChecked33_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts33_5.2

theorem fieldFacts33_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe33_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries56 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank33_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe33_6 = true := fieldFacts33_6.1

theorem fieldChecked33_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts33_6.2

theorem fieldFacts33_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe33_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries56 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank33_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe33_7 = true := fieldFacts33_7.1

theorem fieldChecked33_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field33_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts33_7.2

theorem baseChecked34 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding34.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding34.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries56 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts34_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe34_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries56 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank34_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe34_0 = true := fieldFacts34_0.1

theorem fieldChecked34_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts34_0.2

theorem fieldFacts34_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe34_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries56 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank34_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe34_1 = true := fieldFacts34_1.1

theorem fieldChecked34_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts34_1.2

theorem fieldFacts34_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe34_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries56 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank34_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe34_2 = true := fieldFacts34_2.1

theorem fieldChecked34_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts34_2.2

theorem fieldFacts34_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe34_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries56 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank34_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe34_3 = true := fieldFacts34_3.1

theorem fieldChecked34_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts34_3.2

theorem fieldFacts34_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe34_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries56 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank34_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe34_4 = true := fieldFacts34_4.1

theorem fieldChecked34_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts34_4.2

theorem fieldFacts34_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe34_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries64 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank34_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe34_5 = true := fieldFacts34_5.1

theorem fieldChecked34_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts34_5.2

theorem fieldFacts34_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe34_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries64 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank34_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe34_6 = true := fieldFacts34_6.1

theorem fieldChecked34_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts34_6.2

theorem fieldFacts34_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe34_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries64 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank34_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe34_7 = true := fieldFacts34_7.1

theorem fieldChecked34_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field34_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts34_7.2

theorem baseChecked35 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding35.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding35.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries64 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts35_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe35_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries64 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank35_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe35_0 = true := fieldFacts35_0.1

theorem fieldChecked35_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts35_0.2

theorem fieldFacts35_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe35_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries64 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank35_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe35_1 = true := fieldFacts35_1.1

theorem fieldChecked35_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts35_1.2

theorem fieldFacts35_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe35_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries64 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank35_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe35_2 = true := fieldFacts35_2.1

theorem fieldChecked35_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts35_2.2

theorem fieldFacts35_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe35_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries64 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank35_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe35_3 = true := fieldFacts35_3.1

theorem fieldChecked35_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts35_3.2

theorem fieldFacts35_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe35_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries72 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank35_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe35_4 = true := fieldFacts35_4.1

theorem fieldChecked35_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts35_4.2

theorem fieldFacts35_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe35_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries72 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank35_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe35_5 = true := fieldFacts35_5.1

theorem fieldChecked35_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts35_5.2

theorem fieldFacts35_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe35_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries72 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank35_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe35_6 = true := fieldFacts35_6.1

theorem fieldChecked35_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts35_6.2

theorem fieldFacts35_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe35_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries72 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank35_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe35_7 = true := fieldFacts35_7.1

theorem fieldChecked35_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field35_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts35_7.2

theorem baseChecked36 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding36.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding36.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries72 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts36_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe36_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries72 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank36_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe36_0 = true := fieldFacts36_0.1

theorem fieldChecked36_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts36_0.2

theorem fieldFacts36_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe36_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries72 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank36_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe36_1 = true := fieldFacts36_1.1

theorem fieldChecked36_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts36_1.2

theorem fieldFacts36_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe36_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries72 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank36_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe36_2 = true := fieldFacts36_2.1

theorem fieldChecked36_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts36_2.2

theorem fieldFacts36_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe36_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries80 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank36_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe36_3 = true := fieldFacts36_3.1

theorem fieldChecked36_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts36_3.2

theorem fieldFacts36_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe36_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries80 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank36_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe36_4 = true := fieldFacts36_4.1

theorem fieldChecked36_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts36_4.2

theorem fieldFacts36_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe36_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries80 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank36_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe36_5 = true := fieldFacts36_5.1

theorem fieldChecked36_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts36_5.2

theorem fieldFacts36_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe36_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries80 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank36_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe36_6 = true := fieldFacts36_6.1

theorem fieldChecked36_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts36_6.2

theorem fieldFacts36_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe36_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries80 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank36_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe36_7 = true := fieldFacts36_7.1

theorem fieldChecked36_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field36_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts36_7.2

theorem baseChecked37 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding37.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding37.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries80 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts37_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe37_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries80 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank37_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe37_0 = true := fieldFacts37_0.1

theorem fieldChecked37_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts37_0.2

theorem fieldFacts37_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe37_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries80 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank37_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe37_1 = true := fieldFacts37_1.1

theorem fieldChecked37_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts37_1.2

theorem fieldFacts37_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe37_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries88 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank37_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe37_2 = true := fieldFacts37_2.1

theorem fieldChecked37_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts37_2.2

theorem fieldFacts37_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe37_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries88 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank37_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe37_3 = true := fieldFacts37_3.1

theorem fieldChecked37_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts37_3.2

theorem fieldFacts37_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe37_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries88 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank37_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe37_4 = true := fieldFacts37_4.1

theorem fieldChecked37_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts37_4.2

theorem fieldFacts37_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe37_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries88 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank37_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe37_5 = true := fieldFacts37_5.1

theorem fieldChecked37_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts37_5.2

theorem fieldFacts37_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe37_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries88 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank37_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe37_6 = true := fieldFacts37_6.1

theorem fieldChecked37_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts37_6.2

theorem fieldFacts37_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe37_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries88 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank37_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe37_7 = true := fieldFacts37_7.1

theorem fieldChecked37_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field37_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts37_7.2

theorem baseChecked38 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding38.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding38.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries88 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts38_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe38_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries88 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank38_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe38_0 = true := fieldFacts38_0.1

theorem fieldChecked38_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts38_0.2

theorem fieldFacts38_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe38_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries96 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank38_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe38_1 = true := fieldFacts38_1.1

theorem fieldChecked38_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts38_1.2

theorem fieldFacts38_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe38_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries96 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank38_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe38_2 = true := fieldFacts38_2.1

theorem fieldChecked38_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts38_2.2

theorem fieldFacts38_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe38_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries96 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank38_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe38_3 = true := fieldFacts38_3.1

theorem fieldChecked38_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts38_3.2

theorem fieldFacts38_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe38_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries96 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank38_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe38_4 = true := fieldFacts38_4.1

theorem fieldChecked38_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts38_4.2

theorem fieldFacts38_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe38_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries96 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank38_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe38_5 = true := fieldFacts38_5.1

theorem fieldChecked38_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts38_5.2

theorem fieldFacts38_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe38_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries96 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank38_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe38_6 = true := fieldFacts38_6.1

theorem fieldChecked38_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts38_6.2

theorem fieldFacts38_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe38_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries96 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank38_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe38_7 = true := fieldFacts38_7.1

theorem fieldChecked38_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field38_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts38_7.2

theorem baseChecked39 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding39.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding39.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries96 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts39_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe39_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries104 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank39_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe39_0 = true := fieldFacts39_0.1

theorem fieldChecked39_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts39_0.2

theorem fieldFacts39_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe39_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries104 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank39_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe39_1 = true := fieldFacts39_1.1

theorem fieldChecked39_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts39_1.2

theorem fieldFacts39_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe39_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries104 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank39_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe39_2 = true := fieldFacts39_2.1

theorem fieldChecked39_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts39_2.2

theorem fieldFacts39_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe39_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries104 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank39_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe39_3 = true := fieldFacts39_3.1

theorem fieldChecked39_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts39_3.2

theorem fieldFacts39_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe39_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries104 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank39_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe39_4 = true := fieldFacts39_4.1

theorem fieldChecked39_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts39_4.2

theorem fieldFacts39_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe39_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries104 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank39_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe39_5 = true := fieldFacts39_5.1

theorem fieldChecked39_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts39_5.2

theorem fieldFacts39_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe39_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries104 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank39_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe39_6 = true := fieldFacts39_6.1

theorem fieldChecked39_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts39_6.2

theorem fieldFacts39_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe39_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries104 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank39_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe39_7 = true := fieldFacts39_7.1

theorem fieldChecked39_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field39_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts39_7.2

theorem baseChecked40 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding40.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding40.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries112 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts40_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe40_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries112 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank40_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe40_0 = true := fieldFacts40_0.1

theorem fieldChecked40_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts40_0.2

theorem fieldFacts40_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe40_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries112 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank40_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe40_1 = true := fieldFacts40_1.1

theorem fieldChecked40_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts40_1.2

theorem fieldFacts40_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe40_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries112 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank40_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe40_2 = true := fieldFacts40_2.1

theorem fieldChecked40_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts40_2.2

theorem fieldFacts40_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe40_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries112 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank40_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe40_3 = true := fieldFacts40_3.1

theorem fieldChecked40_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts40_3.2

theorem fieldFacts40_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe40_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries112 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank40_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe40_4 = true := fieldFacts40_4.1

theorem fieldChecked40_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts40_4.2

theorem fieldFacts40_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe40_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries112 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank40_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe40_5 = true := fieldFacts40_5.1

theorem fieldChecked40_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts40_5.2

theorem fieldFacts40_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe40_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries112 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank40_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe40_6 = true := fieldFacts40_6.1

theorem fieldChecked40_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts40_6.2

theorem fieldFacts40_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe40_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries120 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank40_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe40_7 = true := fieldFacts40_7.1

theorem fieldChecked40_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field40_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts40_7.2

theorem baseChecked41 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding41.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding41.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries120 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts41_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe41_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries120 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank41_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe41_0 = true := fieldFacts41_0.1

theorem fieldChecked41_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts41_0.2

theorem fieldFacts41_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe41_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries120 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank41_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe41_1 = true := fieldFacts41_1.1

theorem fieldChecked41_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts41_1.2

theorem fieldFacts41_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe41_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries120 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank41_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe41_2 = true := fieldFacts41_2.1

theorem fieldChecked41_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts41_2.2

theorem fieldFacts41_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe41_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries120 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank41_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe41_3 = true := fieldFacts41_3.1

theorem fieldChecked41_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts41_3.2

theorem fieldFacts41_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe41_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries120 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank41_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe41_4 = true := fieldFacts41_4.1

theorem fieldChecked41_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts41_4.2

theorem fieldFacts41_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe41_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries120 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank41_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe41_5 = true := fieldFacts41_5.1

theorem fieldChecked41_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts41_5.2

theorem fieldFacts41_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe41_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries128 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank41_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe41_6 = true := fieldFacts41_6.1

theorem fieldChecked41_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts41_6.2

theorem fieldFacts41_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe41_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries128 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank41_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe41_7 = true := fieldFacts41_7.1

theorem fieldChecked41_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field41_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts41_7.2

theorem baseChecked42 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding42.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding42.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries128 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts42_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe42_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries128 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank42_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe42_0 = true := fieldFacts42_0.1

theorem fieldChecked42_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts42_0.2

theorem fieldFacts42_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe42_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries128 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank42_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe42_1 = true := fieldFacts42_1.1

theorem fieldChecked42_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts42_1.2

theorem fieldFacts42_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe42_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries128 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank42_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe42_2 = true := fieldFacts42_2.1

theorem fieldChecked42_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts42_2.2

theorem fieldFacts42_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe42_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries128 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank42_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe42_3 = true := fieldFacts42_3.1

theorem fieldChecked42_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts42_3.2

theorem fieldFacts42_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe42_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries128 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank42_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe42_4 = true := fieldFacts42_4.1

theorem fieldChecked42_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts42_4.2

theorem fieldFacts42_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe42_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries136 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank42_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe42_5 = true := fieldFacts42_5.1

theorem fieldChecked42_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts42_5.2

theorem fieldFacts42_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe42_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries136 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank42_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe42_6 = true := fieldFacts42_6.1

theorem fieldChecked42_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts42_6.2

theorem fieldFacts42_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe42_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries136 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank42_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe42_7 = true := fieldFacts42_7.1

theorem fieldChecked42_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field42_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts42_7.2

theorem baseChecked43 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding43.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding43.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries136 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts43_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe43_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries136 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank43_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe43_0 = true := fieldFacts43_0.1

theorem fieldChecked43_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts43_0.2

theorem fieldFacts43_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe43_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries136 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank43_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe43_1 = true := fieldFacts43_1.1

theorem fieldChecked43_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts43_1.2

theorem fieldFacts43_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe43_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries136 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank43_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe43_2 = true := fieldFacts43_2.1

theorem fieldChecked43_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts43_2.2

theorem fieldFacts43_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe43_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries136 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank43_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe43_3 = true := fieldFacts43_3.1

theorem fieldChecked43_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts43_3.2

theorem fieldFacts43_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe43_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries144 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank43_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe43_4 = true := fieldFacts43_4.1

theorem fieldChecked43_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts43_4.2

theorem fieldFacts43_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe43_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries144 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank43_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe43_5 = true := fieldFacts43_5.1

theorem fieldChecked43_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts43_5.2

theorem fieldFacts43_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe43_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries144 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank43_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe43_6 = true := fieldFacts43_6.1

theorem fieldChecked43_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts43_6.2

theorem fieldFacts43_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe43_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries144 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank43_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe43_7 = true := fieldFacts43_7.1

theorem fieldChecked43_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field43_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts43_7.2

theorem baseChecked44 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding44.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding44.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries144 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts44_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe44_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries144 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank44_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe44_0 = true := fieldFacts44_0.1

theorem fieldChecked44_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts44_0.2

theorem fieldFacts44_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe44_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries144 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank44_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe44_1 = true := fieldFacts44_1.1

theorem fieldChecked44_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts44_1.2

theorem fieldFacts44_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe44_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries144 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank44_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe44_2 = true := fieldFacts44_2.1

theorem fieldChecked44_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts44_2.2

theorem fieldFacts44_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe44_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries152 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank44_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe44_3 = true := fieldFacts44_3.1

theorem fieldChecked44_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts44_3.2

theorem fieldFacts44_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe44_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries152 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank44_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe44_4 = true := fieldFacts44_4.1

theorem fieldChecked44_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts44_4.2

theorem fieldFacts44_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe44_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries152 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank44_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe44_5 = true := fieldFacts44_5.1

theorem fieldChecked44_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts44_5.2

theorem fieldFacts44_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe44_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries152 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank44_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe44_6 = true := fieldFacts44_6.1

theorem fieldChecked44_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts44_6.2

theorem fieldFacts44_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe44_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries152 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank44_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe44_7 = true := fieldFacts44_7.1

theorem fieldChecked44_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field44_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts44_7.2

theorem baseChecked45 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding45.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding45.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries152 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts45_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe45_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries152 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank45_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe45_0 = true := fieldFacts45_0.1

theorem fieldChecked45_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts45_0.2

theorem fieldFacts45_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe45_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries152 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank45_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe45_1 = true := fieldFacts45_1.1

theorem fieldChecked45_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts45_1.2

theorem fieldFacts45_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe45_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries160 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank45_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe45_2 = true := fieldFacts45_2.1

theorem fieldChecked45_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts45_2.2

theorem fieldFacts45_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe45_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries160 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank45_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe45_3 = true := fieldFacts45_3.1

theorem fieldChecked45_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts45_3.2

theorem fieldFacts45_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe45_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries160 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank45_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe45_4 = true := fieldFacts45_4.1

theorem fieldChecked45_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts45_4.2

theorem fieldFacts45_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe45_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries160 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank45_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe45_5 = true := fieldFacts45_5.1

theorem fieldChecked45_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts45_5.2

theorem fieldFacts45_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe45_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries160 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank45_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe45_6 = true := fieldFacts45_6.1

theorem fieldChecked45_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts45_6.2

theorem fieldFacts45_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe45_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries160 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank45_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe45_7 = true := fieldFacts45_7.1

theorem fieldChecked45_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field45_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts45_7.2

theorem baseChecked46 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding46.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding46.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries160 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts46_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe46_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries160 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank46_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe46_0 = true := fieldFacts46_0.1

theorem fieldChecked46_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts46_0.2

theorem fieldFacts46_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe46_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries168 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank46_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe46_1 = true := fieldFacts46_1.1

theorem fieldChecked46_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts46_1.2

theorem fieldFacts46_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe46_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries168 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank46_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe46_2 = true := fieldFacts46_2.1

theorem fieldChecked46_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts46_2.2

theorem fieldFacts46_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe46_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries168 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank46_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe46_3 = true := fieldFacts46_3.1

theorem fieldChecked46_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts46_3.2

theorem fieldFacts46_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe46_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries168 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank46_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe46_4 = true := fieldFacts46_4.1

theorem fieldChecked46_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts46_4.2

theorem fieldFacts46_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe46_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries168 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank46_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe46_5 = true := fieldFacts46_5.1

theorem fieldChecked46_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts46_5.2

theorem fieldFacts46_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe46_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries168 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank46_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe46_6 = true := fieldFacts46_6.1

theorem fieldChecked46_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts46_6.2

theorem fieldFacts46_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe46_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries168 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank46_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe46_7 = true := fieldFacts46_7.1

theorem fieldChecked46_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field46_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts46_7.2

theorem baseChecked47 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding47.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding47.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries168 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts47_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe47_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries176 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank47_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe47_0 = true := fieldFacts47_0.1

theorem fieldChecked47_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts47_0.2

theorem fieldFacts47_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe47_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries176 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank47_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe47_1 = true := fieldFacts47_1.1

theorem fieldChecked47_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts47_1.2

theorem fieldFacts47_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe47_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries176 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank47_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe47_2 = true := fieldFacts47_2.1

theorem fieldChecked47_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts47_2.2

theorem fieldFacts47_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe47_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries176 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank47_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe47_3 = true := fieldFacts47_3.1

theorem fieldChecked47_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts47_3.2

theorem fieldFacts47_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe47_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries176 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank47_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe47_4 = true := fieldFacts47_4.1

theorem fieldChecked47_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts47_4.2

theorem fieldFacts47_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe47_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries176 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank47_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe47_5 = true := fieldFacts47_5.1

theorem fieldChecked47_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts47_5.2

theorem fieldFacts47_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe47_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries176 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank47_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe47_6 = true := fieldFacts47_6.1

theorem fieldChecked47_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts47_6.2

theorem fieldFacts47_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe47_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries176 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank47_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe47_7 = true := fieldFacts47_7.1

theorem fieldChecked47_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field47_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts47_7.2

theorem baseChecked48 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding48.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding48.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries184 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts48_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe48_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries184 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank48_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe48_0 = true := fieldFacts48_0.1

theorem fieldChecked48_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts48_0.2

theorem fieldFacts48_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe48_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries184 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank48_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe48_1 = true := fieldFacts48_1.1

theorem fieldChecked48_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts48_1.2

theorem fieldFacts48_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe48_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries184 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank48_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe48_2 = true := fieldFacts48_2.1

theorem fieldChecked48_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts48_2.2

theorem fieldFacts48_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe48_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries184 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank48_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe48_3 = true := fieldFacts48_3.1

theorem fieldChecked48_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts48_3.2

theorem fieldFacts48_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe48_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries184 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank48_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe48_4 = true := fieldFacts48_4.1

theorem fieldChecked48_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts48_4.2

theorem fieldFacts48_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe48_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries184 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank48_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe48_5 = true := fieldFacts48_5.1

theorem fieldChecked48_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts48_5.2

theorem fieldFacts48_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe48_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries184 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank48_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe48_6 = true := fieldFacts48_6.1

theorem fieldChecked48_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts48_6.2

theorem fieldFacts48_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe48_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries192 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank48_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe48_7 = true := fieldFacts48_7.1

theorem fieldChecked48_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field48_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts48_7.2

theorem baseChecked49 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding49.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding49.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries192 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts49_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe49_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries192 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank49_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe49_0 = true := fieldFacts49_0.1

theorem fieldChecked49_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts49_0.2

theorem fieldFacts49_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe49_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries192 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank49_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe49_1 = true := fieldFacts49_1.1

theorem fieldChecked49_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts49_1.2

theorem fieldFacts49_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe49_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries192 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank49_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe49_2 = true := fieldFacts49_2.1

theorem fieldChecked49_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts49_2.2

theorem fieldFacts49_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe49_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries192 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank49_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe49_3 = true := fieldFacts49_3.1

theorem fieldChecked49_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts49_3.2

theorem fieldFacts49_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe49_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries192 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank49_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe49_4 = true := fieldFacts49_4.1

theorem fieldChecked49_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts49_4.2

theorem fieldFacts49_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe49_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries192 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank49_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe49_5 = true := fieldFacts49_5.1

theorem fieldChecked49_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts49_5.2

theorem fieldFacts49_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe49_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries200 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank49_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe49_6 = true := fieldFacts49_6.1

theorem fieldChecked49_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts49_6.2

theorem fieldFacts49_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe49_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries200 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank49_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe49_7 = true := fieldFacts49_7.1

theorem fieldChecked49_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field49_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts49_7.2

theorem baseChecked50 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding50.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding50.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries200 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts50_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe50_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries200 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank50_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe50_0 = true := fieldFacts50_0.1

theorem fieldChecked50_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts50_0.2

theorem fieldFacts50_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe50_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries200 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank50_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe50_1 = true := fieldFacts50_1.1

theorem fieldChecked50_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts50_1.2

theorem fieldFacts50_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe50_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries200 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank50_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe50_2 = true := fieldFacts50_2.1

theorem fieldChecked50_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts50_2.2

theorem fieldFacts50_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe50_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries200 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank50_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe50_3 = true := fieldFacts50_3.1

theorem fieldChecked50_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts50_3.2

theorem fieldFacts50_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe50_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries200 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank50_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe50_4 = true := fieldFacts50_4.1

theorem fieldChecked50_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts50_4.2

theorem fieldFacts50_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe50_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries208 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank50_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe50_5 = true := fieldFacts50_5.1

theorem fieldChecked50_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts50_5.2

theorem fieldFacts50_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe50_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries208 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank50_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe50_6 = true := fieldFacts50_6.1

theorem fieldChecked50_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts50_6.2

theorem fieldFacts50_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe50_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries208 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank50_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe50_7 = true := fieldFacts50_7.1

theorem fieldChecked50_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field50_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts50_7.2

theorem baseChecked51 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding51.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding51.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries208 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts51_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe51_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries208 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank51_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe51_0 = true := fieldFacts51_0.1

theorem fieldChecked51_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts51_0.2

theorem fieldFacts51_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe51_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries208 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank51_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe51_1 = true := fieldFacts51_1.1

theorem fieldChecked51_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts51_1.2

theorem fieldFacts51_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe51_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries208 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank51_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe51_2 = true := fieldFacts51_2.1

theorem fieldChecked51_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts51_2.2

theorem fieldFacts51_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe51_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries208 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank51_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe51_3 = true := fieldFacts51_3.1

theorem fieldChecked51_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts51_3.2

theorem fieldFacts51_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe51_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries216 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank51_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe51_4 = true := fieldFacts51_4.1

theorem fieldChecked51_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts51_4.2

theorem fieldFacts51_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe51_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries216 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank51_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe51_5 = true := fieldFacts51_5.1

theorem fieldChecked51_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts51_5.2

theorem fieldFacts51_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe51_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries216 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank51_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe51_6 = true := fieldFacts51_6.1

theorem fieldChecked51_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts51_6.2

theorem fieldFacts51_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe51_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries216 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank51_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe51_7 = true := fieldFacts51_7.1

theorem fieldChecked51_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field51_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts51_7.2

theorem baseChecked52 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding52.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding52.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries216 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts52_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe52_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries216 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank52_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe52_0 = true := fieldFacts52_0.1

theorem fieldChecked52_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts52_0.2

theorem fieldFacts52_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe52_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries216 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank52_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe52_1 = true := fieldFacts52_1.1

theorem fieldChecked52_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts52_1.2

theorem fieldFacts52_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe52_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries216 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank52_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe52_2 = true := fieldFacts52_2.1

theorem fieldChecked52_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts52_2.2

theorem fieldFacts52_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe52_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries224 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank52_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe52_3 = true := fieldFacts52_3.1

theorem fieldChecked52_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts52_3.2

theorem fieldFacts52_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe52_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries224 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank52_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe52_4 = true := fieldFacts52_4.1

theorem fieldChecked52_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts52_4.2

theorem fieldFacts52_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe52_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries224 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank52_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe52_5 = true := fieldFacts52_5.1

theorem fieldChecked52_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts52_5.2

theorem fieldFacts52_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe52_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries224 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank52_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe52_6 = true := fieldFacts52_6.1

theorem fieldChecked52_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts52_6.2

theorem fieldFacts52_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe52_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries224 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank52_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe52_7 = true := fieldFacts52_7.1

theorem fieldChecked52_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field52_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts52_7.2

theorem baseChecked53 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding53.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding53.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries224 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts53_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe53_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries224 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank53_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe53_0 = true := fieldFacts53_0.1

theorem fieldChecked53_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts53_0.2

theorem fieldFacts53_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe53_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries224 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank53_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe53_1 = true := fieldFacts53_1.1

theorem fieldChecked53_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts53_1.2

theorem fieldFacts53_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe53_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries232 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank53_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe53_2 = true := fieldFacts53_2.1

theorem fieldChecked53_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts53_2.2

theorem fieldFacts53_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe53_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries232 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank53_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe53_3 = true := fieldFacts53_3.1

theorem fieldChecked53_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts53_3.2

theorem fieldFacts53_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe53_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries232 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank53_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe53_4 = true := fieldFacts53_4.1

theorem fieldChecked53_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts53_4.2

theorem fieldFacts53_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe53_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries232 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank53_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe53_5 = true := fieldFacts53_5.1

theorem fieldChecked53_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts53_5.2

theorem fieldFacts53_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe53_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries232 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank53_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe53_6 = true := fieldFacts53_6.1

theorem fieldChecked53_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts53_6.2

theorem fieldFacts53_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe53_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries232 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank53_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe53_7 = true := fieldFacts53_7.1

theorem fieldChecked53_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field53_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts53_7.2

theorem baseChecked54 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding54.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding54.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries232 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts54_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe54_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries232 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank54_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe54_0 = true := fieldFacts54_0.1

theorem fieldChecked54_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts54_0.2

theorem fieldFacts54_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe54_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries240 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank54_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe54_1 = true := fieldFacts54_1.1

theorem fieldChecked54_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts54_1.2

theorem fieldFacts54_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe54_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries240 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank54_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe54_2 = true := fieldFacts54_2.1

theorem fieldChecked54_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts54_2.2

theorem fieldFacts54_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe54_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries240 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank54_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe54_3 = true := fieldFacts54_3.1

theorem fieldChecked54_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts54_3.2

theorem fieldFacts54_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe54_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries240 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank54_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe54_4 = true := fieldFacts54_4.1

theorem fieldChecked54_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts54_4.2

theorem fieldFacts54_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe54_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries240 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank54_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe54_5 = true := fieldFacts54_5.1

theorem fieldChecked54_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts54_5.2

theorem fieldFacts54_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe54_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries240 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank54_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe54_6 = true := fieldFacts54_6.1

theorem fieldChecked54_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts54_6.2

theorem fieldFacts54_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe54_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries240 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank54_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe54_7 = true := fieldFacts54_7.1

theorem fieldChecked54_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field54_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts54_7.2

theorem baseChecked55 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding55.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding55.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries240 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts55_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe55_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries248 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank55_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe55_0 = true := fieldFacts55_0.1

theorem fieldChecked55_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts55_0.2

theorem fieldFacts55_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe55_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries248 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank55_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe55_1 = true := fieldFacts55_1.1

theorem fieldChecked55_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts55_1.2

theorem fieldFacts55_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe55_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries248 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank55_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe55_2 = true := fieldFacts55_2.1

theorem fieldChecked55_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts55_2.2

theorem fieldFacts55_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe55_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries248 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank55_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe55_3 = true := fieldFacts55_3.1

theorem fieldChecked55_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts55_3.2

theorem fieldFacts55_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe55_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries248 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank55_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe55_4 = true := fieldFacts55_4.1

theorem fieldChecked55_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts55_4.2

theorem fieldFacts55_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe55_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries248 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank55_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe55_5 = true := fieldFacts55_5.1

theorem fieldChecked55_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts55_5.2

theorem fieldFacts55_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe55_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries248 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank55_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe55_6 = true := fieldFacts55_6.1

theorem fieldChecked55_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts55_6.2

theorem fieldFacts55_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe55_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries248 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank55_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe55_7 = true := fieldFacts55_7.1

theorem fieldChecked55_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field55_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts55_7.2

theorem baseChecked56 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding56.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding56.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries256_checked (entries256.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries256 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts56_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe56_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries256_checked (entries256.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries256 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank56_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe56_0 = true := fieldFacts56_0.1

theorem fieldChecked56_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts56_0.2

theorem fieldFacts56_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe56_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries256_checked (entries256.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries256 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank56_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe56_1 = true := fieldFacts56_1.1

theorem fieldChecked56_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts56_1.2

theorem fieldFacts56_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe56_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries256_checked (entries256.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries256 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank56_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe56_2 = true := fieldFacts56_2.1

theorem fieldChecked56_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts56_2.2

theorem fieldFacts56_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe56_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries256_checked (entries256.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries256 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank56_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe56_3 = true := fieldFacts56_3.1

theorem fieldChecked56_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts56_3.2

theorem fieldFacts56_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe56_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries256_checked (entries256.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries256 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank56_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe56_4 = true := fieldFacts56_4.1

theorem fieldChecked56_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts56_4.2

theorem fieldFacts56_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe56_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries256_checked (entries256.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries256 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank56_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe56_5 = true := fieldFacts56_5.1

theorem fieldChecked56_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts56_5.2

theorem fieldFacts56_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe56_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries256_checked (entries256.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries256 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank56_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe56_6 = true := fieldFacts56_6.1

theorem fieldChecked56_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts56_6.2

theorem fieldFacts56_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe56_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries264_checked (entries264.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries264 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank56_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe56_7 = true := fieldFacts56_7.1

theorem fieldChecked56_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field56_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts56_7.2

theorem baseChecked57 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding57.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding57.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries264_checked (entries264.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries264 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts57_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe57_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries264_checked (entries264.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries264 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank57_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe57_0 = true := fieldFacts57_0.1

theorem fieldChecked57_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts57_0.2

theorem fieldFacts57_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe57_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries264_checked (entries264.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries264 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank57_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe57_1 = true := fieldFacts57_1.1

theorem fieldChecked57_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts57_1.2

theorem fieldFacts57_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe57_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries264_checked (entries264.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries264 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank57_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe57_2 = true := fieldFacts57_2.1

theorem fieldChecked57_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts57_2.2

theorem fieldFacts57_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe57_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries264_checked (entries264.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries264 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank57_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe57_3 = true := fieldFacts57_3.1

theorem fieldChecked57_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts57_3.2

theorem fieldFacts57_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe57_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries264_checked (entries264.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries264 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank57_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe57_4 = true := fieldFacts57_4.1

theorem fieldChecked57_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts57_4.2

theorem fieldFacts57_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe57_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries264_checked (entries264.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries264 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank57_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe57_5 = true := fieldFacts57_5.1

theorem fieldChecked57_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts57_5.2

theorem fieldFacts57_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe57_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries272_checked (entries272.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries272 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank57_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe57_6 = true := fieldFacts57_6.1

theorem fieldChecked57_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts57_6.2

theorem fieldFacts57_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe57_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries272_checked (entries272.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries272 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank57_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe57_7 = true := fieldFacts57_7.1

theorem fieldChecked57_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field57_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts57_7.2

theorem baseChecked58 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding58.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding58.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries272_checked (entries272.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries272 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts58_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe58_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries272_checked (entries272.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries272 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank58_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe58_0 = true := fieldFacts58_0.1

theorem fieldChecked58_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts58_0.2

theorem fieldFacts58_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe58_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries272_checked (entries272.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries272 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank58_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe58_1 = true := fieldFacts58_1.1

theorem fieldChecked58_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts58_1.2

theorem fieldFacts58_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe58_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries272_checked (entries272.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries272 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank58_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe58_2 = true := fieldFacts58_2.1

theorem fieldChecked58_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts58_2.2

theorem fieldFacts58_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe58_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries272_checked (entries272.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries272 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank58_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe58_3 = true := fieldFacts58_3.1

theorem fieldChecked58_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts58_3.2

theorem fieldFacts58_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe58_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries272_checked (entries272.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries272 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank58_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe58_4 = true := fieldFacts58_4.1

theorem fieldChecked58_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts58_4.2

theorem fieldFacts58_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe58_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries280_checked (entries280.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries280 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank58_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe58_5 = true := fieldFacts58_5.1

theorem fieldChecked58_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts58_5.2

theorem fieldFacts58_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe58_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries280_checked (entries280.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries280 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank58_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe58_6 = true := fieldFacts58_6.1

theorem fieldChecked58_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts58_6.2

theorem fieldFacts58_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe58_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries280_checked (entries280.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries280 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank58_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe58_7 = true := fieldFacts58_7.1

theorem fieldChecked58_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field58_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts58_7.2

theorem baseChecked59 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding59.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding59.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries280_checked (entries280.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries280 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts59_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe59_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries280_checked (entries280.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries280 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank59_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe59_0 = true := fieldFacts59_0.1

theorem fieldChecked59_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts59_0.2

theorem fieldFacts59_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe59_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries280_checked (entries280.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries280 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank59_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe59_1 = true := fieldFacts59_1.1

theorem fieldChecked59_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts59_1.2

theorem fieldFacts59_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe59_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries280_checked (entries280.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries280 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank59_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe59_2 = true := fieldFacts59_2.1

theorem fieldChecked59_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts59_2.2

theorem fieldFacts59_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe59_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries280_checked (entries280.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries280 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank59_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe59_3 = true := fieldFacts59_3.1

theorem fieldChecked59_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts59_3.2

theorem fieldFacts59_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe59_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries288_checked (entries288.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries288 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank59_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe59_4 = true := fieldFacts59_4.1

theorem fieldChecked59_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts59_4.2

theorem fieldFacts59_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe59_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries288_checked (entries288.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries288 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank59_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe59_5 = true := fieldFacts59_5.1

theorem fieldChecked59_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts59_5.2

theorem fieldFacts59_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe59_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries288_checked (entries288.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries288 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank59_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe59_6 = true := fieldFacts59_6.1

theorem fieldChecked59_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts59_6.2

theorem fieldFacts59_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe59_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries288_checked (entries288.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries288 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank59_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe59_7 = true := fieldFacts59_7.1

theorem fieldChecked59_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field59_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts59_7.2

theorem baseChecked60 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding60.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding60.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries288_checked (entries288.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries288 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts60_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe60_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries288_checked (entries288.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries288 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank60_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe60_0 = true := fieldFacts60_0.1

theorem fieldChecked60_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts60_0.2

theorem fieldFacts60_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe60_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries288_checked (entries288.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries288 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank60_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe60_1 = true := fieldFacts60_1.1

theorem fieldChecked60_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts60_1.2

theorem fieldFacts60_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe60_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries288_checked (entries288.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries288 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank60_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe60_2 = true := fieldFacts60_2.1

theorem fieldChecked60_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts60_2.2

theorem fieldFacts60_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe60_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries296_checked (entries296.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries296 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank60_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe60_3 = true := fieldFacts60_3.1

theorem fieldChecked60_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts60_3.2

theorem fieldFacts60_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe60_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries296_checked (entries296.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries296 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank60_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe60_4 = true := fieldFacts60_4.1

theorem fieldChecked60_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts60_4.2

theorem fieldFacts60_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe60_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries296_checked (entries296.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries296 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank60_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe60_5 = true := fieldFacts60_5.1

theorem fieldChecked60_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts60_5.2

theorem fieldFacts60_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe60_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries296_checked (entries296.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries296 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank60_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe60_6 = true := fieldFacts60_6.1

theorem fieldChecked60_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts60_6.2

theorem fieldFacts60_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe60_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries296_checked (entries296.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries296 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank60_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe60_7 = true := fieldFacts60_7.1

theorem fieldChecked60_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field60_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts60_7.2

theorem baseChecked61 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding61.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding61.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries296_checked (entries296.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries296 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts61_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe61_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries296_checked (entries296.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries296 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank61_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe61_0 = true := fieldFacts61_0.1

theorem fieldChecked61_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts61_0.2

theorem fieldFacts61_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe61_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries296_checked (entries296.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries296 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank61_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe61_1 = true := fieldFacts61_1.1

theorem fieldChecked61_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts61_1.2

theorem fieldFacts61_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe61_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries304_checked (entries304.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries304 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank61_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe61_2 = true := fieldFacts61_2.1

theorem fieldChecked61_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts61_2.2

theorem fieldFacts61_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe61_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries304_checked (entries304.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries304 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank61_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe61_3 = true := fieldFacts61_3.1

theorem fieldChecked61_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts61_3.2

theorem fieldFacts61_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe61_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries304_checked (entries304.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries304 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank61_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe61_4 = true := fieldFacts61_4.1

theorem fieldChecked61_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts61_4.2

theorem fieldFacts61_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe61_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries304_checked (entries304.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries304 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank61_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe61_5 = true := fieldFacts61_5.1

theorem fieldChecked61_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts61_5.2

theorem fieldFacts61_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe61_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries304_checked (entries304.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries304 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank61_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe61_6 = true := fieldFacts61_6.1

theorem fieldChecked61_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts61_6.2

theorem fieldFacts61_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe61_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries304_checked (entries304.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries304 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank61_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe61_7 = true := fieldFacts61_7.1

theorem fieldChecked61_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field61_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts61_7.2

theorem baseChecked62 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding62.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding62.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries304_checked (entries304.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries304 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts62_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe62_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries304_checked (entries304.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries304 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank62_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe62_0 = true := fieldFacts62_0.1

theorem fieldChecked62_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts62_0.2

theorem fieldFacts62_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe62_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries312_checked (entries312.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries312 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank62_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe62_1 = true := fieldFacts62_1.1

theorem fieldChecked62_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts62_1.2

theorem fieldFacts62_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe62_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries312_checked (entries312.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries312 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank62_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe62_2 = true := fieldFacts62_2.1

theorem fieldChecked62_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts62_2.2

theorem fieldFacts62_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe62_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries312_checked (entries312.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries312 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank62_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe62_3 = true := fieldFacts62_3.1

theorem fieldChecked62_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts62_3.2

theorem fieldFacts62_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe62_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries312_checked (entries312.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries312 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank62_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe62_4 = true := fieldFacts62_4.1

theorem fieldChecked62_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts62_4.2

theorem fieldFacts62_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe62_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries312_checked (entries312.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries312 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank62_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe62_5 = true := fieldFacts62_5.1

theorem fieldChecked62_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts62_5.2

theorem fieldFacts62_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe62_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries312_checked (entries312.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries312 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank62_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe62_6 = true := fieldFacts62_6.1

theorem fieldChecked62_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts62_6.2

theorem fieldFacts62_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe62_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries312_checked (entries312.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries312 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank62_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe62_7 = true := fieldFacts62_7.1

theorem fieldChecked62_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field62_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts62_7.2

theorem baseChecked63 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding63.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding63.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries312_checked (entries312.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries312 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts63_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe63_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries320_checked (entries320.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries320 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank63_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe63_0 = true := fieldFacts63_0.1

theorem fieldChecked63_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts63_0.2

theorem fieldFacts63_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe63_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries320_checked (entries320.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries320 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank63_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe63_1 = true := fieldFacts63_1.1

theorem fieldChecked63_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts63_1.2

theorem fieldFacts63_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe63_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries320_checked (entries320.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries320 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank63_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe63_2 = true := fieldFacts63_2.1

theorem fieldChecked63_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts63_2.2

theorem fieldFacts63_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe63_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries320_checked (entries320.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries320 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank63_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe63_3 = true := fieldFacts63_3.1

theorem fieldChecked63_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts63_3.2

theorem fieldFacts63_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe63_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries320_checked (entries320.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries320 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank63_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe63_4 = true := fieldFacts63_4.1

theorem fieldChecked63_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts63_4.2

theorem fieldFacts63_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe63_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries320_checked (entries320.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries320 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank63_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe63_5 = true := fieldFacts63_5.1

theorem fieldChecked63_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts63_5.2

theorem fieldFacts63_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe63_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries320_checked (entries320.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries320 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank63_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe63_6 = true := fieldFacts63_6.1

theorem fieldChecked63_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts63_6.2

theorem fieldFacts63_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe63_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries320_checked (entries320.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries320 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank63_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe63_7 = true := fieldFacts63_7.1

theorem fieldChecked63_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field63_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts63_7.2

theorem baseChecked64 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding64.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding64.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries328_checked (entries328.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries328 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts64_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe64_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries328_checked (entries328.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries328 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank64_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe64_0 = true := fieldFacts64_0.1

theorem fieldChecked64_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts64_0.2

theorem fieldFacts64_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe64_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries328_checked (entries328.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries328 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank64_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe64_1 = true := fieldFacts64_1.1

theorem fieldChecked64_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts64_1.2

theorem fieldFacts64_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe64_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries328_checked (entries328.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries328 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank64_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe64_2 = true := fieldFacts64_2.1

theorem fieldChecked64_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts64_2.2

theorem fieldFacts64_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe64_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries328_checked (entries328.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries328 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank64_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe64_3 = true := fieldFacts64_3.1

theorem fieldChecked64_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts64_3.2

theorem fieldFacts64_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe64_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries328_checked (entries328.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries328 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank64_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe64_4 = true := fieldFacts64_4.1

theorem fieldChecked64_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts64_4.2

theorem fieldFacts64_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe64_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries328_checked (entries328.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries328 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank64_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe64_5 = true := fieldFacts64_5.1

theorem fieldChecked64_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts64_5.2

theorem fieldFacts64_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe64_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries328_checked (entries328.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries328 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank64_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe64_6 = true := fieldFacts64_6.1

theorem fieldChecked64_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts64_6.2

theorem fieldFacts64_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe64_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries336_checked (entries336.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries336 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank64_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe64_7 = true := fieldFacts64_7.1

theorem fieldChecked64_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field64_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts64_7.2

theorem baseChecked65 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding65.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding65.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries336_checked (entries336.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries336 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts65_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe65_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries336_checked (entries336.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries336 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank65_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe65_0 = true := fieldFacts65_0.1

theorem fieldChecked65_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts65_0.2

theorem fieldFacts65_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe65_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries336_checked (entries336.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries336 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank65_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe65_1 = true := fieldFacts65_1.1

theorem fieldChecked65_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts65_1.2

theorem fieldFacts65_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe65_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries336_checked (entries336.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries336 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank65_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe65_2 = true := fieldFacts65_2.1

theorem fieldChecked65_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts65_2.2

theorem fieldFacts65_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe65_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries336_checked (entries336.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries336 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank65_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe65_3 = true := fieldFacts65_3.1

theorem fieldChecked65_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts65_3.2

theorem fieldFacts65_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe65_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries336_checked (entries336.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries336 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank65_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe65_4 = true := fieldFacts65_4.1

theorem fieldChecked65_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts65_4.2

theorem fieldFacts65_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe65_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries336_checked (entries336.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries336 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank65_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe65_5 = true := fieldFacts65_5.1

theorem fieldChecked65_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts65_5.2

theorem fieldFacts65_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe65_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries344_checked (entries344.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries344 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank65_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe65_6 = true := fieldFacts65_6.1

theorem fieldChecked65_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts65_6.2

theorem fieldFacts65_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe65_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries344_checked (entries344.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries344 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank65_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe65_7 = true := fieldFacts65_7.1

theorem fieldChecked65_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field65_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts65_7.2

theorem baseChecked66 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding66.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding66.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries344_checked (entries344.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries344 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts66_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe66_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries344_checked (entries344.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries344 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank66_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe66_0 = true := fieldFacts66_0.1

theorem fieldChecked66_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts66_0.2

theorem fieldFacts66_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe66_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries344_checked (entries344.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries344 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank66_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe66_1 = true := fieldFacts66_1.1

theorem fieldChecked66_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts66_1.2

theorem fieldFacts66_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe66_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries344_checked (entries344.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries344 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank66_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe66_2 = true := fieldFacts66_2.1

theorem fieldChecked66_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts66_2.2

theorem fieldFacts66_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe66_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries344_checked (entries344.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries344 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank66_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe66_3 = true := fieldFacts66_3.1

theorem fieldChecked66_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts66_3.2

theorem fieldFacts66_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe66_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries344_checked (entries344.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries344 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank66_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe66_4 = true := fieldFacts66_4.1

theorem fieldChecked66_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts66_4.2

theorem fieldFacts66_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe66_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries352_checked (entries352.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries352 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank66_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe66_5 = true := fieldFacts66_5.1

theorem fieldChecked66_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts66_5.2

theorem fieldFacts66_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe66_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries352_checked (entries352.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries352 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank66_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe66_6 = true := fieldFacts66_6.1

theorem fieldChecked66_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts66_6.2

theorem fieldFacts66_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe66_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries352_checked (entries352.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries352 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank66_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe66_7 = true := fieldFacts66_7.1

theorem fieldChecked66_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field66_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts66_7.2

theorem baseChecked67 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding67.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding67.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries352_checked (entries352.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries352 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts67_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe67_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries352_checked (entries352.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries352 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank67_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe67_0 = true := fieldFacts67_0.1

theorem fieldChecked67_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts67_0.2

theorem fieldFacts67_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe67_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries352_checked (entries352.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries352 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank67_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe67_1 = true := fieldFacts67_1.1

theorem fieldChecked67_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts67_1.2

theorem fieldFacts67_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe67_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries352_checked (entries352.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries352 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank67_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe67_2 = true := fieldFacts67_2.1

theorem fieldChecked67_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts67_2.2

theorem fieldFacts67_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe67_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries352_checked (entries352.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries352 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank67_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe67_3 = true := fieldFacts67_3.1

theorem fieldChecked67_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts67_3.2

theorem fieldFacts67_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe67_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries360_checked (entries360.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries360 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank67_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe67_4 = true := fieldFacts67_4.1

theorem fieldChecked67_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts67_4.2

theorem fieldFacts67_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe67_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries360_checked (entries360.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries360 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank67_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe67_5 = true := fieldFacts67_5.1

theorem fieldChecked67_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts67_5.2

theorem fieldFacts67_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe67_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries360_checked (entries360.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries360 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank67_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe67_6 = true := fieldFacts67_6.1

theorem fieldChecked67_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts67_6.2

theorem fieldFacts67_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe67_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries360_checked (entries360.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries360 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank67_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe67_7 = true := fieldFacts67_7.1

theorem fieldChecked67_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field67_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts67_7.2

theorem baseChecked68 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding68.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding68.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries360_checked (entries360.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries360 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts68_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe68_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries360_checked (entries360.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries360 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank68_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe68_0 = true := fieldFacts68_0.1

theorem fieldChecked68_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts68_0.2

theorem fieldFacts68_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe68_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries360_checked (entries360.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries360 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank68_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe68_1 = true := fieldFacts68_1.1

theorem fieldChecked68_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts68_1.2

theorem fieldFacts68_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe68_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries360_checked (entries360.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries360 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank68_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe68_2 = true := fieldFacts68_2.1

theorem fieldChecked68_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts68_2.2

theorem fieldFacts68_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe68_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries368_checked (entries368.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries368 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank68_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe68_3 = true := fieldFacts68_3.1

theorem fieldChecked68_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts68_3.2

theorem fieldFacts68_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe68_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries368_checked (entries368.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries368 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank68_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe68_4 = true := fieldFacts68_4.1

theorem fieldChecked68_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts68_4.2

theorem fieldFacts68_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe68_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries368_checked (entries368.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries368 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank68_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe68_5 = true := fieldFacts68_5.1

theorem fieldChecked68_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts68_5.2

theorem fieldFacts68_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe68_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries368_checked (entries368.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries368 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank68_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe68_6 = true := fieldFacts68_6.1

theorem fieldChecked68_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts68_6.2

theorem fieldFacts68_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe68_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries368_checked (entries368.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries368 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank68_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe68_7 = true := fieldFacts68_7.1

theorem fieldChecked68_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field68_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts68_7.2

theorem baseChecked69 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding69.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding69.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries368_checked (entries368.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries368 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts69_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe69_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries368_checked (entries368.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries368 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank69_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe69_0 = true := fieldFacts69_0.1

theorem fieldChecked69_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts69_0.2

theorem fieldFacts69_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe69_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries368_checked (entries368.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries368 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank69_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe69_1 = true := fieldFacts69_1.1

theorem fieldChecked69_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts69_1.2

theorem fieldFacts69_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe69_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries376_checked (entries376.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries376 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank69_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe69_2 = true := fieldFacts69_2.1

theorem fieldChecked69_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts69_2.2

theorem fieldFacts69_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe69_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries376_checked (entries376.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries376 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank69_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe69_3 = true := fieldFacts69_3.1

theorem fieldChecked69_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts69_3.2

theorem fieldFacts69_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe69_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries376_checked (entries376.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries376 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank69_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe69_4 = true := fieldFacts69_4.1

theorem fieldChecked69_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts69_4.2

theorem fieldFacts69_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe69_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries376_checked (entries376.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries376 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank69_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe69_5 = true := fieldFacts69_5.1

theorem fieldChecked69_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts69_5.2

theorem fieldFacts69_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe69_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries376_checked (entries376.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries376 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank69_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe69_6 = true := fieldFacts69_6.1

theorem fieldChecked69_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts69_6.2

theorem fieldFacts69_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe69_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries376_checked (entries376.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries376 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank69_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe69_7 = true := fieldFacts69_7.1

theorem fieldChecked69_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field69_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts69_7.2

theorem baseChecked70 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding70.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding70.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries376_checked (entries376.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries376 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts70_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe70_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries376_checked (entries376.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries376 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank70_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe70_0 = true := fieldFacts70_0.1

theorem fieldChecked70_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts70_0.2

theorem fieldFacts70_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe70_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries384_checked (entries384.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries384 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank70_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe70_1 = true := fieldFacts70_1.1

theorem fieldChecked70_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts70_1.2

theorem fieldFacts70_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe70_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries384_checked (entries384.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries384 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank70_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe70_2 = true := fieldFacts70_2.1

theorem fieldChecked70_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts70_2.2

theorem fieldFacts70_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe70_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries384_checked (entries384.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries384 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank70_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe70_3 = true := fieldFacts70_3.1

theorem fieldChecked70_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts70_3.2

theorem fieldFacts70_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe70_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries384_checked (entries384.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries384 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank70_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe70_4 = true := fieldFacts70_4.1

theorem fieldChecked70_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts70_4.2

theorem fieldFacts70_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe70_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries384_checked (entries384.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries384 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank70_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe70_5 = true := fieldFacts70_5.1

theorem fieldChecked70_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts70_5.2

theorem fieldFacts70_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe70_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries384_checked (entries384.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries384 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank70_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe70_6 = true := fieldFacts70_6.1

theorem fieldChecked70_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts70_6.2

theorem fieldFacts70_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe70_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries384_checked (entries384.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries384 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank70_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe70_7 = true := fieldFacts70_7.1

theorem fieldChecked70_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field70_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts70_7.2

theorem baseChecked71 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding71.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding71.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries384_checked (entries384.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries384 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem fieldFacts71_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe71_0 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_0 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries392_checked (entries392.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries392 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank71_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe71_0 = true := fieldFacts71_0.1

theorem fieldChecked71_0 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_0.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts71_0.2

theorem fieldFacts71_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe71_1 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_1 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries392_checked (entries392.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries392 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank71_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe71_1 = true := fieldFacts71_1.1

theorem fieldChecked71_1 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_1.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts71_1.2

theorem fieldFacts71_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe71_2 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_2 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries392_checked (entries392.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries392 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank71_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe71_2 = true := fieldFacts71_2.1

theorem fieldChecked71_2 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_2.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts71_2.2

theorem fieldFacts71_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe71_3 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_3 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries392_checked (entries392.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries392 ⟨3, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank71_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe71_3 = true := fieldFacts71_3.1

theorem fieldChecked71_3 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_3.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts71_3.2

theorem fieldFacts71_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe71_4 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_4 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries392_checked (entries392.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries392 ⟨4, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank71_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe71_4 = true := fieldFacts71_4.1

theorem fieldChecked71_4 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_4.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts71_4.2

theorem fieldFacts71_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe71_5 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_5 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries392_checked (entries392.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries392 ⟨5, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank71_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe71_5 = true := fieldFacts71_5.1

theorem fieldChecked71_5 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_5.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts71_5.2

theorem fieldFacts71_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe71_6 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_6 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries392_checked (entries392.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries392 ⟨6, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank71_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe71_6 = true := fieldFacts71_6.1

theorem fieldChecked71_6 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_6.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts71_6.2

theorem fieldFacts71_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe71_7 = true ∧ Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := by
  have item : (NumericLookupSourceChecks.ofAgreement Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_7 Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank).check = true :=
    List.all_eq_true.mp entries392_checked (entries392.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries392 ⟨7, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofAgreement_check, Bool.and_eq_true] using item

theorem inBank71_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.check Airbender.Compiler.LookupSourceNative.KeccakCached.native.recipe71_7 = true := fieldFacts71_7.1

theorem fieldChecked71_7 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.field71_7.check Airbender.Compiler.LookupNative.KeccakCached.native.sourcePlacement Airbender.Compiler.LookupSourceNative.KeccakCached.native.bank.placement = true := fieldFacts71_7.2

theorem baseChecked72 : Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding72.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.encoding72.baseCheck Airbender.Compiler.ConsumerNative.KeccakCached.native.typing)).check = true :=
    List.all_eq_true.mp entries400_checked (entries400.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries400 ⟨0, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem genericSetupChecked : Airbender.Compiler.LookupSourceNative.KeccakCached.native.leaf31.isSetup = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (Airbender.Compiler.LookupSourceNative.KeccakCached.native.leaf31.isSetup)).check = true :=
    List.all_eq_true.mp entries400_checked (entries400.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries400 ⟨1, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

theorem genericSourceCoverage : decide (((Airbender.Compiler.LookupNative.KeccakCached.native.genericTree).leaves.map Airbender.Compiler.LookupSourceNative.KeccakCached.native.genericLabel).Perm (List.range (Airbender.Compiler.LookupSourceNative.KeccakCached.native.genericQueries.length + 1))) = true := by
  have item : (NumericLookupSourceChecks.ofFlag (n := 228) (decide (((Airbender.Compiler.LookupNative.KeccakCached.native.genericTree).leaves.map Airbender.Compiler.LookupSourceNative.KeccakCached.native.genericLabel).Perm (List.range (Airbender.Compiler.LookupSourceNative.KeccakCached.native.genericQueries.length + 1))))).check = true :=
    List.all_eq_true.mp entries400_checked (entries400.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries400 ⟨2, by decide +kernel⟩)
  simpa only [NumericLookupSourceChecks.ofFlag_check] using item

end Airbender.Compiler.LookupSourceChecks.KeccakCached
