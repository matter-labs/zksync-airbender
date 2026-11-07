import Airbender.Proofs.GKRProtocol.CleanArgumentChecks.BlakeGCached.Bindings

namespace Airbender.Compiler.CleanArgumentChecks.BlakeGCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=
  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked

noncomputable def entries0 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe0.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe2.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe3.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe4.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe5.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe6.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe7.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe8.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank]

theorem entries0_binding : ((originalEntries.drop 0).take 8) = entries0 := by rfl

theorem entries0_checked : entries0.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries0_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 0 8

noncomputable def entries8 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe9.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression9 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe10.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression10 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe11.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression11 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe12.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression12 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe13.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression13 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe14.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression14 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe15.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression15 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe16.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank]

theorem entries8_binding : ((originalEntries.drop 8).take 8) = entries8 := by rfl

theorem entries8_checked : entries8.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries8_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 8 8

noncomputable def entries16 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression16 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe17.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression17 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe18.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression18 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe19.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression19 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe20.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression20 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe21.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression0_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field0_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression0_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field0_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression0_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field0_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank]

theorem entries16_binding : ((originalEntries.drop 16).take 8) = entries16 := by rfl

theorem entries16_checked : entries16.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries16_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 16 8

noncomputable def entries24 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression0_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field0_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression0_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field0_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression0_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field0_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression0_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field0_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression0_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field0_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression0_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field0_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression1_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field1_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression1_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field1_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank]

theorem entries24_binding : ((originalEntries.drop 24).take 8) = entries24 := by rfl

theorem entries24_checked : entries24.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries24_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 24 8

noncomputable def entries32 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression1_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field1_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression1_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field1_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression1_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field1_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression1_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field1_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression1_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field1_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression1_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field1_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression1_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field1_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression2_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field2_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank]

theorem entries32_binding : ((originalEntries.drop 32).take 8) = entries32 := by rfl

theorem entries32_checked : entries32.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries32_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 32 8

noncomputable def entries40 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression2_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field2_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression2_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field2_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression2_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field2_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression2_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field2_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression2_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field2_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression2_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field2_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression2_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field2_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression2_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field2_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank]

theorem entries40_binding : ((originalEntries.drop 40).take 8) = entries40 := by rfl

theorem entries40_checked : entries40.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries40_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 40 8

noncomputable def entries48 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression3_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field3_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression3_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field3_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression3_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field3_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression3_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field3_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression3_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field3_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression3_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field3_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression3_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field3_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression3_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field3_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank]

theorem entries48_binding : ((originalEntries.drop 48).take 8) = entries48 := by rfl

theorem entries48_checked : entries48.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries48_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 48 8

noncomputable def entries56 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression3_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field3_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression4_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field4_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression4_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field4_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression4_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field4_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression4_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field4_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression4_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field4_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression4_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field4_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression4_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field4_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank]

theorem entries56_binding : ((originalEntries.drop 56).take 8) = entries56 := by rfl

theorem entries56_checked : entries56.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries56_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 56 8

noncomputable def entries64 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression4_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field4_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression4_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field4_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression5_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field5_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression5_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field5_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression5_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field5_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression5_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field5_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression5_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field5_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression5_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field5_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank]

theorem entries64_binding : ((originalEntries.drop 64).take 8) = entries64 := by rfl

theorem entries64_checked : entries64.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries64_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 64 8

noncomputable def entries72 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression5_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field5_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression5_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field5_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression5_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field5_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression6_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field6_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression6_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field6_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression6_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field6_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression6_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field6_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression6_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field6_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank]

theorem entries72_binding : ((originalEntries.drop 72).take 8) = entries72 := by rfl

theorem entries72_checked : entries72.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries72_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 72 8

noncomputable def entries80 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression6_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field6_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression6_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field6_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression6_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field6_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression6_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field6_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression7_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field7_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression7_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field7_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression7_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field7_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression7_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field7_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank]

theorem entries80_binding : ((originalEntries.drop 80).take 8) = entries80 := by rfl

theorem entries80_checked : entries80.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries80_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 80 8

noncomputable def entries88 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression7_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field7_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression7_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field7_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression7_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field7_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression7_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field7_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression7_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field7_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field8_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field8_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field8_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank]

theorem entries88_binding : ((originalEntries.drop 88).take 8) = entries88 := by rfl

theorem entries88_checked : entries88.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries88_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 88 8

noncomputable def entries96 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field8_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field8_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field8_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field8_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field8_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field8_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field9_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field9_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank]

theorem entries96_binding : ((originalEntries.drop 96).take 8) = entries96 := by rfl

theorem entries96_checked : entries96.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries96_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 96 8

noncomputable def entries104 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field9_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field9_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field9_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field9_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field9_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field9_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field9_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field10_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank]

theorem entries104_binding : ((originalEntries.drop 104).take 8) = entries104 := by rfl

theorem entries104_checked : entries104.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries104_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 104 8

noncomputable def entries112 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field10_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field10_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field10_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field10_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field10_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field10_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field10_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field10_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank]

theorem entries112_binding : ((originalEntries.drop 112).take 8) = entries112 := by rfl

theorem entries112_checked : entries112.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries112_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 112 8

noncomputable def entries120 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field11_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field11_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field11_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field11_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field11_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field11_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field11_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field11_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank]

theorem entries120_binding : ((originalEntries.drop 120).take 8) = entries120 := by rfl

theorem entries120_checked : entries120.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries120_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 120 8

noncomputable def entries128 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field11_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field12_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field12_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field12_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field12_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field12_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field12_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field12_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank]

theorem entries128_binding : ((originalEntries.drop 128).take 8) = entries128 := by rfl

theorem entries128_checked : entries128.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries128_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 128 8

noncomputable def entries136 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field12_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field12_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field13_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field13_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field13_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field13_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field13_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field13_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank]

theorem entries136_binding : ((originalEntries.drop 136).take 8) = entries136 := by rfl

theorem entries136_checked : entries136.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries136_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 136 8

noncomputable def entries144 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field13_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field13_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field13_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field14_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field14_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field14_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field14_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field14_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank]

theorem entries144_binding : ((originalEntries.drop 144).take 8) = entries144 := by rfl

theorem entries144_checked : entries144.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries144_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 144 8

noncomputable def entries152 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field14_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field14_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field14_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field14_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field15_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field15_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field15_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field15_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank]

theorem entries152_binding : ((originalEntries.drop 152).take 8) = entries152 := by rfl

theorem entries152_checked : entries152.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries152_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 152 8

noncomputable def entries160 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field15_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field15_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field15_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field15_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field15_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression16_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field16_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression16_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field16_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression16_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field16_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank]

theorem entries160_binding : ((originalEntries.drop 160).take 8) = entries160 := by rfl

theorem entries160_checked : entries160.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries160_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 160 8

noncomputable def entries168 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression16_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field16_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression16_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field16_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression16_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field16_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression16_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field16_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression16_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field16_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression16_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field16_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression17_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field17_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression17_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field17_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank]

theorem entries168_binding : ((originalEntries.drop 168).take 8) = entries168 := by rfl

theorem entries168_checked : entries168.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries168_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 168 8

noncomputable def entries176 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression17_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field17_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression17_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field17_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression17_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field17_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression17_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field17_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression17_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field17_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression17_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field17_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression17_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field17_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression18_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field18_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank]

theorem entries176_binding : ((originalEntries.drop 176).take 8) = entries176 := by rfl

theorem entries176_checked : entries176.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries176_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 176 8

noncomputable def entries184 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression18_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field18_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression18_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field18_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression18_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field18_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression18_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field18_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression18_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field18_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression18_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field18_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression18_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field18_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression18_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field18_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank]

theorem entries184_binding : ((originalEntries.drop 184).take 8) = entries184 := by rfl

theorem entries184_checked : entries184.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries184_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 184 8

theorem timestampChecked0 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe0.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe0.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries0 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked1 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe2.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe2.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries0 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked2 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe3.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe3.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries0 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked3 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe4.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe4.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries0 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked4 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe5.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe5.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries0 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked5 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe6.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe6.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries0 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked6 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe7.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe7.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries0 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked7 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe8.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe8.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries0 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked8 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe9.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe9.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries8 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked9 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression9 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe10.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression9 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe10.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries8 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked10 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression10 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe11.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression10 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe11.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries8 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked11 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression11 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe12.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression11 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe12.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries8 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked12 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression12 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe13.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression12 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe13.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries8 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked13 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression13 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe14.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression13 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe14.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries8 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked14 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression14 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe15.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression14 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe15.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries8 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked15 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression15 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe16.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression15 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe16.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries8 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked16 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression16 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe17.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression16 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe17.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries16 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked17 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression17 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe18.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression17 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe18.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries16 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked18 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression18 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe19.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression18 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe19.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries16 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked19 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression19 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe20.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression19 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe20.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries16 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked20 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression20 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe21.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BlakeGCached.native.timestampExpression20 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank (Airbender.Compiler.HelperNative.BlakeGCached.native.recipe21.expression Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.placement) Airbender.Compiler.MemoryNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries16 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression0_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field0_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression0_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field0_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries16 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression0_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field0_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression0_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field0_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries16 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression0_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field0_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression0_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field0_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries16 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression0_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field0_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression0_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field0_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries24 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression0_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field0_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression0_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field0_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries24 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression0_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field0_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression0_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field0_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries24 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression0_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field0_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression0_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field0_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries24 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression0_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field0_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression0_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field0_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries24 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_8 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression0_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field0_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression0_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field0_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries24 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked1_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression1_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field1_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression1_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field1_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries24 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked1_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression1_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field1_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression1_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field1_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries24 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked1_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression1_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field1_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression1_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field1_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries32 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked1_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression1_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field1_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression1_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field1_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries32 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked1_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression1_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field1_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression1_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field1_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries32 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked1_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression1_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field1_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression1_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field1_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries32 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked1_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression1_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field1_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression1_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field1_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries32 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked1_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression1_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field1_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression1_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field1_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries32 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked1_8 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression1_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field1_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression1_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field1_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries32 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked2_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression2_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field2_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression2_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field2_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries32 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked2_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression2_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field2_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression2_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field2_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries40 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked2_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression2_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field2_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression2_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field2_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries40 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked2_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression2_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field2_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression2_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field2_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries40 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked2_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression2_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field2_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression2_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field2_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries40 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked2_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression2_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field2_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression2_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field2_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries40 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked2_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression2_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field2_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression2_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field2_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries40 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked2_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression2_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field2_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression2_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field2_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries40 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked2_8 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression2_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field2_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression2_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field2_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries40 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked3_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression3_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field3_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression3_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field3_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries48 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked3_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression3_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field3_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression3_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field3_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries48 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked3_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression3_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field3_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression3_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field3_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries48 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked3_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression3_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field3_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression3_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field3_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries48 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked3_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression3_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field3_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression3_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field3_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries48 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked3_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression3_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field3_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression3_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field3_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries48 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked3_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression3_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field3_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression3_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field3_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries48 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked3_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression3_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field3_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression3_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field3_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries48 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked3_8 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression3_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field3_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression3_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field3_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries56 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked4_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression4_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field4_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression4_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field4_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries56 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked4_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression4_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field4_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression4_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field4_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries56 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked4_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression4_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field4_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression4_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field4_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries56 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked4_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression4_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field4_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression4_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field4_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries56 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked4_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression4_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field4_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression4_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field4_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries56 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked4_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression4_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field4_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression4_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field4_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries56 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked4_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression4_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field4_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression4_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field4_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries56 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked4_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression4_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field4_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression4_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field4_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries64 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked4_8 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression4_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field4_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression4_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field4_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries64 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked5_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression5_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field5_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression5_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field5_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries64 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked5_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression5_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field5_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression5_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field5_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries64 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked5_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression5_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field5_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression5_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field5_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries64 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked5_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression5_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field5_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression5_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field5_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries64 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked5_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression5_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field5_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression5_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field5_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries64 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked5_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression5_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field5_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression5_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field5_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries64 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked5_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression5_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field5_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression5_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field5_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries72 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked5_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression5_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field5_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression5_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field5_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries72 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked5_8 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression5_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field5_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression5_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field5_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries72 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked6_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression6_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field6_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression6_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field6_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries72 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked6_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression6_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field6_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression6_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field6_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries72 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked6_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression6_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field6_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression6_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field6_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries72 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked6_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression6_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field6_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression6_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field6_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries72 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked6_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression6_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field6_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression6_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field6_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries72 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked6_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression6_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field6_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression6_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field6_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries80 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked6_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression6_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field6_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression6_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field6_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries80 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked6_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression6_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field6_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression6_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field6_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries80 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked6_8 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression6_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field6_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression6_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field6_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries80 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked7_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression7_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field7_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression7_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field7_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries80 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked7_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression7_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field7_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression7_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field7_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries80 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked7_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression7_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field7_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression7_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field7_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries80 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked7_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression7_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field7_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression7_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field7_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries80 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked7_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression7_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field7_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression7_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field7_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries88 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked7_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression7_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field7_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression7_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field7_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries88 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked7_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression7_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field7_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression7_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field7_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries88 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked7_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression7_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field7_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression7_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field7_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries88 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked7_8 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression7_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field7_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part0.genericExpression7_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field7_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries88 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked8_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field8_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field8_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries88 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked8_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field8_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field8_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries88 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked8_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field8_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field8_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries88 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked8_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field8_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field8_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries96 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked8_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field8_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field8_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries96 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked8_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field8_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field8_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries96 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked8_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field8_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field8_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries96 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked8_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field8_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field8_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries96 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked8_8 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field8_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression8_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field8_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries96 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked9_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field9_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field9_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries96 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked9_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field9_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field9_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries96 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked9_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field9_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field9_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries104 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked9_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field9_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field9_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries104 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked9_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field9_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field9_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries104 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked9_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field9_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field9_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries104 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked9_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field9_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field9_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries104 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked9_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field9_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field9_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries104 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked9_8 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field9_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression9_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field9_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries104 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked10_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field10_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field10_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries104 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked10_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field10_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field10_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries112 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked10_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field10_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field10_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries112 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked10_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field10_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field10_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries112 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked10_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field10_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field10_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries112 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked10_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field10_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field10_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries112 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked10_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field10_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field10_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries112 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked10_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field10_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field10_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries112 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked10_8 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field10_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression10_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field10_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries112 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked11_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field11_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field11_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries120 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked11_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field11_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field11_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries120 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked11_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field11_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field11_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries120 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked11_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field11_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field11_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries120 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked11_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field11_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field11_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries120 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked11_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field11_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field11_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries120 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked11_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field11_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field11_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries120 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked11_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field11_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field11_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries120 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked11_8 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field11_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression11_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field11_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries128 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked12_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field12_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field12_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries128 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked12_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field12_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field12_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries128 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked12_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field12_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field12_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries128 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked12_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field12_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field12_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries128 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked12_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field12_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field12_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries128 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked12_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field12_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field12_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries128 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked12_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field12_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field12_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries128 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked12_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field12_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field12_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries136 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked12_8 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field12_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression12_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field12_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries136 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked13_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field13_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field13_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries136 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked13_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field13_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field13_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries136 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked13_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field13_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field13_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries136 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked13_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field13_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field13_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries136 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked13_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field13_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field13_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries136 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked13_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field13_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field13_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries136 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked13_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field13_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field13_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries144 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked13_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field13_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field13_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries144 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked13_8 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field13_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression13_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field13_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries144 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked14_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field14_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field14_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries144 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked14_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field14_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field14_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries144 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked14_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field14_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field14_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries144 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked14_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field14_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field14_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries144 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked14_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field14_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field14_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries144 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked14_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field14_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field14_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries152 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked14_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field14_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field14_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries152 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked14_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field14_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field14_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries152 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked14_8 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field14_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression14_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field14_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries152 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked15_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field15_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field15_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries152 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked15_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field15_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field15_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries152 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked15_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field15_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field15_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries152 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked15_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field15_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field15_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries152 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked15_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field15_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field15_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries160 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked15_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field15_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field15_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries160 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked15_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field15_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field15_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries160 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked15_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field15_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field15_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries160 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked15_8 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field15_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part1.genericExpression15_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field15_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries160 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked16_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression16_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field16_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression16_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field16_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries160 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked16_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression16_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field16_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression16_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field16_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries160 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked16_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression16_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field16_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression16_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field16_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries160 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked16_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression16_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field16_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression16_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field16_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries168 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked16_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression16_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field16_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression16_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field16_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries168 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked16_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression16_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field16_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression16_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field16_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries168 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked16_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression16_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field16_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression16_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field16_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries168 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked16_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression16_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field16_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression16_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field16_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries168 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked16_8 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression16_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field16_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression16_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field16_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries168 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked17_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression17_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field17_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression17_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field17_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries168 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked17_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression17_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field17_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression17_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field17_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries168 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked17_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression17_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field17_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression17_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field17_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries176 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked17_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression17_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field17_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression17_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field17_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries176 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked17_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression17_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field17_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression17_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field17_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries176 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked17_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression17_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field17_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression17_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field17_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries176 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked17_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression17_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field17_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression17_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field17_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries176 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked17_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression17_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field17_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression17_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field17_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries176 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked17_8 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression17_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field17_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression17_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field17_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries176 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked18_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression18_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field18_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression18_0 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field18_0.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries176 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked18_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression18_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field18_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression18_1 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field18_1.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries184 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked18_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression18_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field18_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression18_2 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field18_2.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries184 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked18_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression18_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field18_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression18_3 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field18_3.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries184 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked18_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression18_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field18_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression18_4 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field18_4.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries184 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked18_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression18_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field18_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression18_5 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field18_5.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries184 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked18_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression18_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field18_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression18_6 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field18_6.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries184 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked18_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression18_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field18_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression18_7 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field18_7.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries184 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked18_8 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression18_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field18_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BlakeGCached.native.part2.genericExpression18_8 Airbender.Compiler.CleanArithmeticNative.BlakeGCached.native.placement Airbender.Compiler.FullArithmeticNative.BlakeGCached.native.bank Airbender.Compiler.LookupNative.BlakeGCached.native.field18_8.lowered Airbender.Compiler.LookupSourceNative.BlakeGCached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries184 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

end Airbender.Compiler.CleanArgumentChecks.BlakeGCached
