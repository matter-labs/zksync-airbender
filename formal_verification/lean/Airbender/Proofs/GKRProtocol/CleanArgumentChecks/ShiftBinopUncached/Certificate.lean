import Airbender.Proofs.GKRProtocol.CleanArgumentChecks.ShiftBinopUncached.Bindings

namespace Airbender.Compiler.CleanArgumentChecks.ShiftBinopUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=
  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked

noncomputable def entries0 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.rangeExpression0 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field5_0.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.rangeExpression1 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field6_0.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression0 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.recipe2.expression Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.placement) Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression1 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.recipe4.expression Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.placement) Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression2 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.recipe5.expression Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.placement) Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression3 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.recipe6.expression Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.placement) Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression4 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.recipe7.expression Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.placement) Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression5 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.recipe8.expression Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.placement) Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank]

theorem entries0_binding : ((originalEntries.drop 0).take 8) = entries0 := by rfl

theorem entries0_checked : entries0.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries0_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 0 8

noncomputable def entries8 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression6 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.recipe9.expression Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.placement) Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression7 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.recipe13.expression Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.placement) Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_0 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field0_0.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_1 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field0_1.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_2 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field0_2.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_3 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field0_3.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_4 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field0_4.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_5 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field0_5.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank]

theorem entries8_binding : ((originalEntries.drop 8).take 8) = entries8 := by rfl

theorem entries8_checked : entries8.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries8_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 8 8

noncomputable def entries16 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_6 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field0_6.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_7 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field0_7.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_8 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field0_8.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_9 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field0_9.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_0 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field1_0.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_1 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field1_1.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_2 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field1_2.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_3 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field1_3.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank]

theorem entries16_binding : ((originalEntries.drop 16).take 8) = entries16 := by rfl

theorem entries16_checked : entries16.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries16_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 16 8

noncomputable def entries24 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_4 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field1_4.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_5 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field1_5.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_6 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field1_6.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_7 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field1_7.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_8 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field1_8.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_9 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field1_9.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_0 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field2_0.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_1 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field2_1.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank]

theorem entries24_binding : ((originalEntries.drop 24).take 8) = entries24 := by rfl

theorem entries24_checked : entries24.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries24_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 24 8

noncomputable def entries32 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_2 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field2_2.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_3 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field2_3.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_4 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field2_4.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_5 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field2_5.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_6 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field2_6.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_7 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field2_7.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_8 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field2_8.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_9 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field2_9.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank]

theorem entries32_binding : ((originalEntries.drop 32).take 8) = entries32 := by rfl

theorem entries32_checked : entries32.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries32_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 32 8

noncomputable def entries40 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_0 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field3_0.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_1 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field3_1.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_2 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field3_2.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_3 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field3_3.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_4 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field3_4.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_5 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field3_5.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_6 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field3_6.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_7 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field3_7.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank]

theorem entries40_binding : ((originalEntries.drop 40).take 8) = entries40 := by rfl

theorem entries40_checked : entries40.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries40_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 40 8

noncomputable def entries48 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_8 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field3_8.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_9 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field3_9.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_0 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field4_0.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_1 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field4_1.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_2 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field4_2.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_3 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field4_3.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_4 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field4_4.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_5 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field4_5.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank]

theorem entries48_binding : ((originalEntries.drop 48).take 8) = entries48 := by rfl

theorem entries48_checked : entries48.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries48_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 48 8

noncomputable def entries56 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_6 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field4_6.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_7 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field4_7.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_8 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field4_8.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_9 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field4_9.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank]

theorem entries56_binding : ((originalEntries.drop 56).take 4) = entries56 := by rfl

theorem entries56_checked : entries56.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries56_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 56 4

theorem rangeChecked0 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.rangeExpression0 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field5_0.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.rangeExpression0 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field5_0.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries0 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked1 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.rangeExpression1 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field6_0.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.rangeExpression1 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field6_0.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries0 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked0 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression0 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.recipe2.expression Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.placement) Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression0 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.recipe2.expression Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.placement) Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries0 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked1 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression1 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.recipe4.expression Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.placement) Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression1 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.recipe4.expression Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.placement) Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries0 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked2 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression2 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.recipe5.expression Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.placement) Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression2 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.recipe5.expression Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.placement) Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries0 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked3 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression3 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.recipe6.expression Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.placement) Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression3 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.recipe6.expression Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.placement) Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries0 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked4 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression4 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.recipe7.expression Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.placement) Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression4 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.recipe7.expression Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.placement) Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries0 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked5 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression5 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.recipe8.expression Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.placement) Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression5 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.recipe8.expression Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.placement) Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries0 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked6 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression6 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.recipe9.expression Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.placement) Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression6 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.recipe9.expression Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.placement) Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries8 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked7 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression7 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.recipe13.expression Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.placement) Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.ShiftBinopUncached.native.timestampExpression7 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank (Airbender.Compiler.HelperNative.ShiftBinopUncached.native.recipe13.expression Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank.placement) Airbender.Compiler.MemoryNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries8 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_0 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field0_0.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_0 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field0_0.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries8 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_1 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field0_1.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_1 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field0_1.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries8 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_2 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field0_2.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_2 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field0_2.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries8 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_3 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field0_3.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_3 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field0_3.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries8 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_4 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field0_4.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_4 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field0_4.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries8 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_5 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field0_5.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_5 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field0_5.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries8 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_6 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field0_6.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_6 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field0_6.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries16 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_7 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field0_7.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_7 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field0_7.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries16 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_8 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_8 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field0_8.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_8 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field0_8.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries16 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_9 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_9 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field0_9.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression0_9 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field0_9.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries16 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked1_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_0 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field1_0.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_0 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field1_0.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries16 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked1_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_1 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field1_1.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_1 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field1_1.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries16 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked1_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_2 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field1_2.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_2 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field1_2.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries16 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked1_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_3 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field1_3.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_3 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field1_3.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries16 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked1_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_4 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field1_4.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_4 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field1_4.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries24 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked1_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_5 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field1_5.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_5 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field1_5.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries24 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked1_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_6 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field1_6.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_6 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field1_6.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries24 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked1_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_7 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field1_7.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_7 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field1_7.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries24 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked1_8 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_8 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field1_8.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_8 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field1_8.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries24 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked1_9 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_9 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field1_9.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression1_9 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field1_9.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries24 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked2_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_0 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field2_0.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_0 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field2_0.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries24 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked2_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_1 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field2_1.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_1 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field2_1.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries24 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked2_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_2 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field2_2.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_2 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field2_2.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries32 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked2_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_3 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field2_3.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_3 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field2_3.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries32 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked2_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_4 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field2_4.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_4 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field2_4.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries32 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked2_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_5 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field2_5.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_5 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field2_5.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries32 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked2_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_6 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field2_6.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_6 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field2_6.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries32 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked2_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_7 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field2_7.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_7 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field2_7.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries32 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked2_8 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_8 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field2_8.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_8 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field2_8.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries32 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked2_9 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_9 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field2_9.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression2_9 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field2_9.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries32 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked3_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_0 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field3_0.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_0 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field3_0.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries40 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked3_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_1 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field3_1.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_1 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field3_1.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries40 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked3_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_2 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field3_2.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_2 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field3_2.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries40 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked3_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_3 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field3_3.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_3 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field3_3.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries40 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked3_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_4 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field3_4.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_4 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field3_4.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries40 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked3_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_5 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field3_5.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_5 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field3_5.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries40 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked3_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_6 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field3_6.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_6 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field3_6.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries40 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked3_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_7 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field3_7.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_7 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field3_7.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries40 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked3_8 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_8 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field3_8.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_8 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field3_8.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries48 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked3_9 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_9 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field3_9.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression3_9 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field3_9.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries48 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked4_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_0 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field4_0.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_0 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field4_0.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries48 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked4_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_1 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field4_1.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_1 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field4_1.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries48 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked4_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_2 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field4_2.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_2 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field4_2.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries48 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked4_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_3 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field4_3.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_3 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field4_3.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries48 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked4_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_4 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field4_4.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_4 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field4_4.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries48 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked4_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_5 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field4_5.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_5 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field4_5.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries48 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked4_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_6 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field4_6.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_6 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field4_6.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries56 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked4_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_7 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field4_7.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_7 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field4_7.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries56 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked4_8 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_8 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field4_8.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_8 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field4_8.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries56 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked4_9 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_9 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field4_9.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.ShiftBinopUncached.native.part0.genericExpression4_9 Airbender.Compiler.CleanArithmeticNative.ShiftBinopUncached.native.placement Airbender.Compiler.FullArithmeticNative.ShiftBinopUncached.native.bank Airbender.Compiler.LookupNative.ShiftBinopUncached.native.field4_9.lowered Airbender.Compiler.LookupSourceNative.ShiftBinopUncached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries56 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

end Airbender.Compiler.CleanArgumentChecks.ShiftBinopUncached
