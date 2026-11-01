import Airbender.Proofs.GKRProtocol.CleanArgumentChecks.KeccakUncached.Bindings

namespace Airbender.Compiler.CleanArgumentChecks.KeccakUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=
  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked

noncomputable def entries0 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe0.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe2.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe3.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe4.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe5.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe6.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe7.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe8.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank]

theorem entries0_binding : ((originalEntries.drop 0).take 8) = entries0 := by rfl

theorem entries0_checked : entries0.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries0_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 0 8

noncomputable def entries8 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression8 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe9.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression9 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe10.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression10 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe11.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression11 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe12.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression12 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe13.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression13 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe14.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression14 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe15.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression15 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe16.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank]

theorem entries8_binding : ((originalEntries.drop 8).take 8) = entries8 := by rfl

theorem entries8_checked : entries8.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries8_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 8 8

noncomputable def entries16 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression16 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe17.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression17 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe18.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression18 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe19.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression19 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe20.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression20 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe21.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression21 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe22.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression22 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe23.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression23 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe24.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank]

theorem entries16_binding : ((originalEntries.drop 16).take 8) = entries16 := by rfl

theorem entries16_checked : entries16.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries16_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 16 8

noncomputable def entries24 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression24 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe25.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression25 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe26.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression26 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe27.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression27 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe28.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression28 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe29.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression29 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe72.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field0_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field0_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries24_binding : ((originalEntries.drop 24).take 8) = entries24 := by rfl

theorem entries24_checked : entries24.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries24_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 24 8

noncomputable def entries32 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field0_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field0_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field0_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field0_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field0_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field0_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field1_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field1_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries32_binding : ((originalEntries.drop 32).take 8) = entries32 := by rfl

theorem entries32_checked : entries32.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries32_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 32 8

noncomputable def entries40 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field1_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field1_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field1_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field1_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field1_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field1_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field2_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field2_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries40_binding : ((originalEntries.drop 40).take 8) = entries40 := by rfl

theorem entries40_checked : entries40.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries40_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 40 8

noncomputable def entries48 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field2_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field2_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field2_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field2_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field2_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field2_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field3_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field3_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries48_binding : ((originalEntries.drop 48).take 8) = entries48 := by rfl

theorem entries48_checked : entries48.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries48_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 48 8

noncomputable def entries56 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field3_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field3_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field3_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field3_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field3_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field3_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field4_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field4_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries56_binding : ((originalEntries.drop 56).take 8) = entries56 := by rfl

theorem entries56_checked : entries56.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries56_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 56 8

noncomputable def entries64 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field4_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field4_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field4_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field4_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field4_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field4_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field5_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field5_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries64_binding : ((originalEntries.drop 64).take 8) = entries64 := by rfl

theorem entries64_checked : entries64.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries64_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 64 8

noncomputable def entries72 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field5_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field5_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field5_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field5_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field5_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field5_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field6_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field6_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries72_binding : ((originalEntries.drop 72).take 8) = entries72 := by rfl

theorem entries72_checked : entries72.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries72_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 72 8

noncomputable def entries80 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field6_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field6_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field6_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field6_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field6_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field6_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field7_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field7_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries80_binding : ((originalEntries.drop 80).take 8) = entries80 := by rfl

theorem entries80_checked : entries80.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries80_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 80 8

noncomputable def entries88 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field7_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field7_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field7_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field7_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field7_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field7_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression8_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field8_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression8_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field8_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries88_binding : ((originalEntries.drop 88).take 8) = entries88 := by rfl

theorem entries88_checked : entries88.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries88_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 88 8

noncomputable def entries96 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression8_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field8_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression8_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field8_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression8_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field8_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression8_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field8_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression8_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field8_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression8_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field8_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression9_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field9_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression9_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field9_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries96_binding : ((originalEntries.drop 96).take 8) = entries96 := by rfl

theorem entries96_checked : entries96.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries96_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 96 8

noncomputable def entries104 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression9_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field9_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression9_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field9_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression9_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field9_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression9_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field9_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression9_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field9_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression9_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field9_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression10_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field10_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression10_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field10_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries104_binding : ((originalEntries.drop 104).take 8) = entries104 := by rfl

theorem entries104_checked : entries104.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries104_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 104 8

noncomputable def entries112 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression10_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field10_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression10_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field10_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression10_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field10_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression10_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field10_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression10_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field10_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression10_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field10_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression11_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field11_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression11_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field11_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries112_binding : ((originalEntries.drop 112).take 8) = entries112 := by rfl

theorem entries112_checked : entries112.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries112_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 112 8

noncomputable def entries120 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression11_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field11_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression11_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field11_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression11_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field11_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression11_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field11_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression11_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field11_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression11_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field11_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression12_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field12_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression12_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field12_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries120_binding : ((originalEntries.drop 120).take 8) = entries120 := by rfl

theorem entries120_checked : entries120.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries120_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 120 8

noncomputable def entries128 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression12_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field12_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression12_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field12_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression12_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field12_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression12_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field12_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression12_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field12_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression12_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field12_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression13_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field13_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression13_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field13_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries128_binding : ((originalEntries.drop 128).take 8) = entries128 := by rfl

theorem entries128_checked : entries128.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries128_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 128 8

noncomputable def entries136 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression13_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field13_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression13_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field13_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression13_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field13_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression13_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field13_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression13_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field13_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression13_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field13_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression14_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field14_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression14_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field14_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries136_binding : ((originalEntries.drop 136).take 8) = entries136 := by rfl

theorem entries136_checked : entries136.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries136_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 136 8

noncomputable def entries144 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression14_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field14_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression14_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field14_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression14_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field14_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression14_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field14_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression14_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field14_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression14_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field14_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression15_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field15_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression15_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field15_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries144_binding : ((originalEntries.drop 144).take 8) = entries144 := by rfl

theorem entries144_checked : entries144.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries144_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 144 8

noncomputable def entries152 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression15_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field15_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression15_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field15_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression15_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field15_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression15_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field15_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression15_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field15_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression15_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field15_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field16_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field16_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries152_binding : ((originalEntries.drop 152).take 8) = entries152 := by rfl

theorem entries152_checked : entries152.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries152_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 152 8

noncomputable def entries160 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field16_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field16_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field16_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field16_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field16_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field16_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field17_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field17_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries160_binding : ((originalEntries.drop 160).take 8) = entries160 := by rfl

theorem entries160_checked : entries160.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries160_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 160 8

noncomputable def entries168 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field17_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field17_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field17_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field17_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field17_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field17_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field18_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field18_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries168_binding : ((originalEntries.drop 168).take 8) = entries168 := by rfl

theorem entries168_checked : entries168.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries168_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 168 8

noncomputable def entries176 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field18_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field18_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field18_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field18_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field18_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field18_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field19_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field19_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries176_binding : ((originalEntries.drop 176).take 8) = entries176 := by rfl

theorem entries176_checked : entries176.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries176_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 176 8

noncomputable def entries184 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field19_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field19_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field19_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field19_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field19_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field19_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field20_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field20_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries184_binding : ((originalEntries.drop 184).take 8) = entries184 := by rfl

theorem entries184_checked : entries184.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries184_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 184 8

noncomputable def entries192 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field20_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field20_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field20_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field20_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field20_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field20_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field21_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field21_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries192_binding : ((originalEntries.drop 192).take 8) = entries192 := by rfl

theorem entries192_checked : entries192.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries192_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 192 8

noncomputable def entries200 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field21_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field21_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field21_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field21_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field21_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field21_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field22_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field22_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries200_binding : ((originalEntries.drop 200).take 8) = entries200 := by rfl

theorem entries200_checked : entries200.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries200_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 200 8

noncomputable def entries208 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field22_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field22_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field22_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field22_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field22_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field22_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field23_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field23_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries208_binding : ((originalEntries.drop 208).take 8) = entries208 := by rfl

theorem entries208_checked : entries208.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries208_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 208 8

noncomputable def entries216 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field23_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field23_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field23_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field23_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field23_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field23_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression24_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field24_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression24_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field24_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries216_binding : ((originalEntries.drop 216).take 8) = entries216 := by rfl

theorem entries216_checked : entries216.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries216_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 216 8

noncomputable def entries224 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression24_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field24_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression24_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field24_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression24_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field24_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression24_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field24_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression24_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field24_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression24_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field24_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression25_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field25_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression25_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field25_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries224_binding : ((originalEntries.drop 224).take 8) = entries224 := by rfl

theorem entries224_checked : entries224.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries224_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 224 8

noncomputable def entries232 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression25_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field25_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression25_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field25_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression25_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field25_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression25_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field25_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression25_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field25_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression25_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field25_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression26_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field26_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression26_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field26_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries232_binding : ((originalEntries.drop 232).take 8) = entries232 := by rfl

theorem entries232_checked : entries232.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries232_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 232 8

noncomputable def entries240 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression26_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field26_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression26_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field26_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression26_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field26_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression26_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field26_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression26_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field26_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression26_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field26_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression27_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field27_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression27_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field27_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries240_binding : ((originalEntries.drop 240).take 8) = entries240 := by rfl

theorem entries240_checked : entries240.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries240_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 240 8

noncomputable def entries248 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression27_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field27_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression27_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field27_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression27_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field27_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression27_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field27_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression27_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field27_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression27_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field27_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression28_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field28_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression28_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field28_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries248_binding : ((originalEntries.drop 248).take 8) = entries248 := by rfl

theorem entries248_checked : entries248.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries248_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 248 8

noncomputable def entries256 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression28_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field28_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression28_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field28_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression28_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field28_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression28_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field28_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression28_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field28_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression28_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field28_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression29_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field29_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression29_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field29_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries256_binding : ((originalEntries.drop 256).take 8) = entries256 := by rfl

theorem entries256_checked : entries256.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries256_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 256 8

noncomputable def entries264 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression29_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field29_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression29_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field29_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression29_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field29_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression29_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field29_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression29_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field29_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression29_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field29_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression30_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field30_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression30_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field30_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries264_binding : ((originalEntries.drop 264).take 8) = entries264 := by rfl

theorem entries264_checked : entries264.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries264_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 264 8

noncomputable def entries272 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression30_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field30_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression30_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field30_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression30_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field30_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression30_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field30_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression30_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field30_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression30_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field30_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression31_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field31_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression31_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field31_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries272_binding : ((originalEntries.drop 272).take 8) = entries272 := by rfl

theorem entries272_checked : entries272.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries272_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 272 8

noncomputable def entries280 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression31_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field31_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression31_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field31_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression31_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field31_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression31_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field31_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression31_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field31_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression31_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field31_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field32_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field32_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries280_binding : ((originalEntries.drop 280).take 8) = entries280 := by rfl

theorem entries280_checked : entries280.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries280_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 280 8

noncomputable def entries288 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field32_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field32_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field32_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field32_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field32_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field32_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field33_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field33_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries288_binding : ((originalEntries.drop 288).take 8) = entries288 := by rfl

theorem entries288_checked : entries288.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries288_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 288 8

noncomputable def entries296 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field33_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field33_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field33_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field33_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field33_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field33_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field34_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field34_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries296_binding : ((originalEntries.drop 296).take 8) = entries296 := by rfl

theorem entries296_checked : entries296.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries296_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 296 8

noncomputable def entries304 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field34_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field34_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field34_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field34_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field34_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field34_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field35_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field35_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries304_binding : ((originalEntries.drop 304).take 8) = entries304 := by rfl

theorem entries304_checked : entries304.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries304_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 304 8

noncomputable def entries312 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field35_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field35_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field35_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field35_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field35_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field35_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field36_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field36_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries312_binding : ((originalEntries.drop 312).take 8) = entries312 := by rfl

theorem entries312_checked : entries312.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries312_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 312 8

noncomputable def entries320 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field36_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field36_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field36_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field36_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field36_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field36_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field37_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field37_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries320_binding : ((originalEntries.drop 320).take 8) = entries320 := by rfl

theorem entries320_checked : entries320.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries320_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 320 8

noncomputable def entries328 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field37_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field37_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field37_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field37_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field37_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field37_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field38_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field38_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries328_binding : ((originalEntries.drop 328).take 8) = entries328 := by rfl

theorem entries328_checked : entries328.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries328_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 328 8

noncomputable def entries336 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field38_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field38_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field38_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field38_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field38_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field38_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field39_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field39_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries336_binding : ((originalEntries.drop 336).take 8) = entries336 := by rfl

theorem entries336_checked : entries336.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries336_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 336 8

noncomputable def entries344 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field39_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field39_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field39_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field39_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field39_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field39_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part5.genericExpression40_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field40_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part5.genericExpression40_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field40_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries344_binding : ((originalEntries.drop 344).take 8) = entries344 := by rfl

theorem entries344_checked : entries344.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries344_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 344 8

noncomputable def entries352 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part5.genericExpression40_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field40_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part5.genericExpression40_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field40_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part5.genericExpression40_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field40_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part5.genericExpression40_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field40_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part5.genericExpression40_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field40_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part5.genericExpression40_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field40_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank]

theorem entries352_binding : ((originalEntries.drop 352).take 6) = entries352 := by rfl

theorem entries352_checked : entries352.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries352_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 352 6

theorem timestampChecked0 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe0.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe0.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries0 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked1 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe2.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe2.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries0 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked2 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe3.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe3.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries0 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked3 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe4.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe4.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries0 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked4 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe5.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe5.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries0 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked5 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe6.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe6.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries0 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked6 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe7.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe7.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries0 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked7 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe8.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe8.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries0 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked8 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression8 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe9.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression8 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe9.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries8 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked9 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression9 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe10.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression9 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe10.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries8 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked10 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression10 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe11.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression10 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe11.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries8 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked11 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression11 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe12.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression11 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe12.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries8 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked12 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression12 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe13.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression12 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe13.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries8 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked13 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression13 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe14.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression13 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe14.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries8 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked14 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression14 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe15.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression14 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe15.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries8 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked15 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression15 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe16.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression15 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe16.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries8 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked16 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression16 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe17.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression16 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe17.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries16 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked17 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression17 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe18.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression17 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe18.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries16 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked18 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression18 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe19.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression18 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe19.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries16 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked19 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression19 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe20.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression19 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe20.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries16 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked20 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression20 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe21.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression20 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe21.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries16 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked21 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression21 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe22.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression21 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe22.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries16 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked22 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression22 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe23.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression22 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe23.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries16 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked23 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression23 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe24.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression23 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe24.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries16 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked24 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression24 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe25.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression24 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe25.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries24 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked25 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression25 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe26.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression25 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe26.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries24 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked26 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression26 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe27.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression26 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe27.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries24 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked27 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression27 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe28.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression27 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe28.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries24 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked28 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression28 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe29.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression28 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe29.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries24 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked29 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression29 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe72.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.KeccakUncached.native.timestampExpression29 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank (Airbender.Compiler.HelperNative.KeccakUncached.native.recipe72.expression Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.placement) Airbender.Compiler.MemoryNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries24 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field0_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field0_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries24 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field0_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field0_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries24 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field0_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field0_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries32 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field0_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field0_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries32 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field0_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field0_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries32 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field0_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field0_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries32 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field0_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field0_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries32 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field0_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression0_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field0_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries32 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked1_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field1_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field1_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries32 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked1_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field1_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field1_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries32 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked1_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field1_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field1_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries40 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked1_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field1_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field1_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries40 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked1_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field1_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field1_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries40 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked1_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field1_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field1_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries40 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked1_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field1_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field1_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries40 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked1_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field1_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression1_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field1_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries40 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked2_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field2_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field2_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries40 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked2_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field2_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field2_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries40 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked2_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field2_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field2_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries48 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked2_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field2_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field2_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries48 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked2_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field2_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field2_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries48 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked2_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field2_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field2_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries48 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked2_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field2_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field2_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries48 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked2_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field2_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression2_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field2_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries48 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked3_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field3_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field3_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries48 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked3_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field3_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field3_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries48 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked3_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field3_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field3_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries56 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked3_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field3_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field3_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries56 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked3_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field3_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field3_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries56 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked3_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field3_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field3_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries56 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked3_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field3_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field3_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries56 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked3_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field3_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression3_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field3_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries56 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked4_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field4_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field4_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries56 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked4_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field4_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field4_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries56 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked4_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field4_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field4_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries64 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked4_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field4_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field4_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries64 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked4_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field4_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field4_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries64 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked4_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field4_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field4_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries64 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked4_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field4_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field4_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries64 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked4_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field4_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression4_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field4_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries64 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked5_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field5_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field5_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries64 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked5_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field5_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field5_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries64 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked5_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field5_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field5_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries72 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked5_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field5_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field5_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries72 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked5_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field5_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field5_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries72 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked5_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field5_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field5_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries72 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked5_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field5_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field5_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries72 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked5_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field5_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression5_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field5_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries72 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked6_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field6_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field6_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries72 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked6_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field6_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field6_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries72 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked6_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field6_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field6_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries80 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked6_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field6_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field6_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries80 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked6_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field6_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field6_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries80 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked6_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field6_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field6_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries80 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked6_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field6_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field6_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries80 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked6_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field6_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression6_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field6_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries80 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked7_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field7_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field7_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries80 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked7_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field7_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field7_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries80 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked7_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field7_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field7_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries88 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked7_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field7_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field7_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries88 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked7_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field7_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field7_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries88 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked7_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field7_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field7_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries88 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked7_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field7_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field7_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries88 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked7_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field7_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part0.genericExpression7_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field7_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries88 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked8_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression8_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field8_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression8_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field8_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries88 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked8_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression8_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field8_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression8_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field8_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries88 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked8_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression8_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field8_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression8_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field8_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries96 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked8_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression8_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field8_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression8_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field8_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries96 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked8_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression8_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field8_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression8_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field8_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries96 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked8_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression8_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field8_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression8_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field8_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries96 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked8_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression8_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field8_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression8_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field8_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries96 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked8_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression8_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field8_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression8_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field8_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries96 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked9_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression9_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field9_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression9_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field9_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries96 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked9_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression9_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field9_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression9_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field9_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries96 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked9_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression9_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field9_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression9_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field9_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries104 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked9_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression9_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field9_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression9_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field9_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries104 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked9_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression9_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field9_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression9_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field9_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries104 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked9_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression9_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field9_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression9_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field9_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries104 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked9_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression9_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field9_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression9_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field9_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries104 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked9_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression9_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field9_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression9_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field9_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries104 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked10_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression10_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field10_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression10_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field10_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries104 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked10_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression10_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field10_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression10_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field10_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries104 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked10_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression10_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field10_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression10_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field10_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries112 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked10_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression10_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field10_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression10_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field10_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries112 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked10_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression10_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field10_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression10_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field10_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries112 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked10_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression10_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field10_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression10_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field10_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries112 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked10_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression10_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field10_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression10_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field10_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries112 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked10_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression10_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field10_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression10_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field10_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries112 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked11_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression11_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field11_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression11_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field11_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries112 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked11_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression11_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field11_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression11_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field11_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries112 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked11_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression11_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field11_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression11_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field11_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries120 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked11_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression11_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field11_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression11_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field11_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries120 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked11_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression11_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field11_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression11_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field11_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries120 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked11_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression11_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field11_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression11_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field11_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries120 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked11_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression11_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field11_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression11_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field11_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries120 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked11_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression11_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field11_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression11_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field11_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries120 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked12_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression12_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field12_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression12_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field12_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries120 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked12_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression12_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field12_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression12_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field12_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries120 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked12_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression12_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field12_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression12_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field12_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries128 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked12_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression12_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field12_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression12_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field12_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries128 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked12_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression12_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field12_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression12_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field12_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries128 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked12_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression12_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field12_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression12_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field12_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries128 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked12_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression12_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field12_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression12_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field12_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries128 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked12_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression12_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field12_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression12_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field12_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries128 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked13_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression13_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field13_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression13_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field13_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries128 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked13_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression13_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field13_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression13_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field13_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries128 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked13_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression13_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field13_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression13_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field13_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries136 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked13_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression13_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field13_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression13_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field13_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries136 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked13_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression13_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field13_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression13_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field13_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries136 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked13_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression13_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field13_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression13_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field13_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries136 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked13_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression13_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field13_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression13_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field13_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries136 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked13_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression13_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field13_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression13_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field13_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries136 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked14_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression14_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field14_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression14_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field14_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries136 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked14_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression14_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field14_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression14_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field14_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries136 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked14_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression14_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field14_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression14_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field14_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries144 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked14_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression14_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field14_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression14_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field14_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries144 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked14_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression14_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field14_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression14_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field14_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries144 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked14_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression14_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field14_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression14_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field14_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries144 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked14_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression14_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field14_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression14_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field14_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries144 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked14_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression14_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field14_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression14_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field14_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries144 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked15_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression15_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field15_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression15_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field15_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries144 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked15_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression15_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field15_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression15_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field15_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries144 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked15_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression15_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field15_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression15_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field15_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries152 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked15_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression15_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field15_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression15_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field15_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries152 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked15_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression15_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field15_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression15_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field15_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries152 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked15_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression15_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field15_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression15_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field15_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries152 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked15_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression15_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field15_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression15_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field15_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries152 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked15_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression15_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field15_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part1.genericExpression15_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field15_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries152 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked16_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field16_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field16_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries152 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked16_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field16_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field16_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries152 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked16_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field16_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field16_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries160 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked16_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field16_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field16_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries160 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked16_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field16_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field16_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries160 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked16_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field16_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field16_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries160 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked16_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field16_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field16_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries160 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked16_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field16_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression16_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field16_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries160 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked17_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field17_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field17_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries160 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked17_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field17_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field17_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries160 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked17_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field17_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field17_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries168 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked17_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field17_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field17_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries168 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked17_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field17_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field17_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries168 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked17_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field17_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field17_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries168 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked17_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field17_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field17_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries168 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked17_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field17_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression17_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field17_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries168 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked18_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field18_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field18_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries168 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked18_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field18_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field18_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries168 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked18_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field18_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field18_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries176 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked18_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field18_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field18_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries176 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked18_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field18_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field18_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries176 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked18_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field18_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field18_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries176 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked18_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field18_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field18_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries176 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked18_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field18_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression18_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field18_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries176 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked19_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field19_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field19_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries176 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked19_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field19_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field19_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries176 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked19_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field19_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field19_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries184 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked19_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field19_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field19_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries184 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked19_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field19_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field19_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries184 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked19_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field19_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field19_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries184 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked19_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field19_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field19_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries184 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked19_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field19_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression19_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field19_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries184 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked20_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field20_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field20_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries184 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked20_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field20_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field20_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries184 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked20_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field20_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field20_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries192 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked20_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field20_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field20_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries192 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked20_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field20_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field20_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries192 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked20_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field20_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field20_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries192 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked20_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field20_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field20_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries192 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked20_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field20_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression20_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field20_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries192 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked21_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field21_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field21_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries192 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked21_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field21_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field21_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries192 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked21_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field21_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field21_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries200 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked21_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field21_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field21_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries200 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked21_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field21_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field21_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries200 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked21_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field21_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field21_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries200 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked21_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field21_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field21_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries200 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked21_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field21_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression21_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field21_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries200 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked22_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field22_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field22_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries200 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked22_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field22_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field22_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries200 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked22_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field22_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field22_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries208 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked22_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field22_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field22_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries208 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked22_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field22_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field22_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries208 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked22_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field22_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field22_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries208 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked22_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field22_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field22_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries208 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked22_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field22_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression22_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field22_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries208 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked23_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field23_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field23_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries208 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked23_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field23_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field23_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries208 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked23_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field23_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field23_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries216 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked23_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field23_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field23_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries216 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked23_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field23_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field23_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries216 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked23_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field23_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field23_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries216 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked23_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field23_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field23_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries216 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked23_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field23_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part2.genericExpression23_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field23_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries216 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked24_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression24_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field24_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression24_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field24_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries216 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked24_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression24_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field24_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression24_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field24_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries216 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked24_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression24_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field24_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression24_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field24_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries224 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked24_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression24_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field24_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression24_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field24_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries224 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked24_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression24_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field24_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression24_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field24_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries224 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked24_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression24_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field24_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression24_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field24_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries224 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked24_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression24_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field24_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression24_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field24_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries224 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked24_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression24_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field24_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression24_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field24_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries224 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked25_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression25_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field25_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression25_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field25_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries224 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked25_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression25_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field25_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression25_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field25_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries224 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked25_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression25_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field25_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression25_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field25_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries232 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked25_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression25_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field25_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression25_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field25_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries232 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked25_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression25_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field25_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression25_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field25_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries232 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked25_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression25_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field25_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression25_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field25_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries232 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked25_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression25_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field25_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression25_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field25_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries232 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked25_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression25_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field25_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression25_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field25_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries232 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked26_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression26_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field26_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression26_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field26_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries232 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked26_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression26_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field26_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression26_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field26_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries232 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked26_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression26_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field26_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression26_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field26_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries240 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked26_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression26_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field26_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression26_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field26_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries240 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked26_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression26_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field26_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression26_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field26_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries240 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked26_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression26_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field26_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression26_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field26_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries240 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked26_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression26_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field26_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression26_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field26_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries240 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked26_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression26_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field26_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression26_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field26_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries240 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked27_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression27_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field27_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression27_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field27_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries240 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked27_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression27_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field27_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression27_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field27_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries240 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked27_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression27_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field27_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression27_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field27_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries248 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked27_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression27_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field27_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression27_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field27_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries248 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked27_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression27_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field27_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression27_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field27_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries248 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked27_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression27_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field27_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression27_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field27_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries248 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked27_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression27_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field27_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression27_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field27_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries248 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked27_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression27_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field27_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression27_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field27_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries248 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked28_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression28_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field28_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression28_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field28_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries248 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked28_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression28_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field28_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression28_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field28_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries248 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked28_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression28_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field28_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression28_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field28_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries256_checked (entries256.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries256 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked28_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression28_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field28_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression28_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field28_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries256_checked (entries256.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries256 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked28_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression28_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field28_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression28_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field28_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries256_checked (entries256.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries256 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked28_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression28_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field28_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression28_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field28_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries256_checked (entries256.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries256 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked28_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression28_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field28_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression28_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field28_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries256_checked (entries256.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries256 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked28_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression28_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field28_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression28_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field28_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries256_checked (entries256.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries256 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked29_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression29_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field29_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression29_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field29_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries256_checked (entries256.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries256 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked29_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression29_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field29_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression29_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field29_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries256_checked (entries256.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries256 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked29_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression29_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field29_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression29_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field29_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries264_checked (entries264.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries264 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked29_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression29_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field29_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression29_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field29_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries264_checked (entries264.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries264 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked29_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression29_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field29_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression29_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field29_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries264_checked (entries264.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries264 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked29_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression29_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field29_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression29_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field29_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries264_checked (entries264.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries264 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked29_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression29_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field29_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression29_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field29_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries264_checked (entries264.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries264 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked29_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression29_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field29_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression29_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field29_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries264_checked (entries264.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries264 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked30_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression30_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field30_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression30_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field30_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries264_checked (entries264.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries264 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked30_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression30_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field30_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression30_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field30_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries264_checked (entries264.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries264 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked30_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression30_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field30_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression30_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field30_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries272_checked (entries272.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries272 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked30_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression30_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field30_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression30_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field30_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries272_checked (entries272.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries272 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked30_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression30_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field30_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression30_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field30_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries272_checked (entries272.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries272 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked30_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression30_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field30_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression30_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field30_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries272_checked (entries272.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries272 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked30_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression30_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field30_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression30_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field30_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries272_checked (entries272.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries272 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked30_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression30_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field30_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression30_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field30_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries272_checked (entries272.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries272 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked31_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression31_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field31_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression31_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field31_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries272_checked (entries272.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries272 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked31_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression31_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field31_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression31_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field31_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries272_checked (entries272.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries272 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked31_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression31_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field31_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression31_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field31_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries280_checked (entries280.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries280 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked31_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression31_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field31_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression31_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field31_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries280_checked (entries280.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries280 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked31_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression31_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field31_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression31_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field31_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries280_checked (entries280.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries280 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked31_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression31_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field31_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression31_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field31_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries280_checked (entries280.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries280 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked31_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression31_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field31_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression31_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field31_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries280_checked (entries280.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries280 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked31_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression31_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field31_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part3.genericExpression31_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field31_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries280_checked (entries280.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries280 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked32_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field32_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field32_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries280_checked (entries280.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries280 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked32_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field32_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field32_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries280_checked (entries280.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries280 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked32_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field32_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field32_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries288_checked (entries288.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries288 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked32_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field32_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field32_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries288_checked (entries288.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries288 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked32_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field32_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field32_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries288_checked (entries288.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries288 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked32_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field32_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field32_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries288_checked (entries288.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries288 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked32_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field32_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field32_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries288_checked (entries288.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries288 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked32_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field32_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression32_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field32_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries288_checked (entries288.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries288 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked33_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field33_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field33_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries288_checked (entries288.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries288 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked33_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field33_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field33_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries288_checked (entries288.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries288 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked33_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field33_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field33_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries296_checked (entries296.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries296 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked33_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field33_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field33_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries296_checked (entries296.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries296 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked33_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field33_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field33_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries296_checked (entries296.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries296 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked33_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field33_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field33_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries296_checked (entries296.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries296 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked33_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field33_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field33_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries296_checked (entries296.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries296 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked33_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field33_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression33_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field33_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries296_checked (entries296.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries296 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked34_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field34_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field34_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries296_checked (entries296.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries296 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked34_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field34_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field34_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries296_checked (entries296.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries296 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked34_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field34_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field34_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries304_checked (entries304.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries304 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked34_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field34_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field34_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries304_checked (entries304.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries304 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked34_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field34_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field34_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries304_checked (entries304.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries304 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked34_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field34_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field34_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries304_checked (entries304.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries304 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked34_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field34_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field34_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries304_checked (entries304.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries304 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked34_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field34_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression34_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field34_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries304_checked (entries304.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries304 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked35_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field35_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field35_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries304_checked (entries304.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries304 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked35_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field35_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field35_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries304_checked (entries304.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries304 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked35_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field35_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field35_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries312_checked (entries312.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries312 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked35_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field35_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field35_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries312_checked (entries312.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries312 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked35_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field35_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field35_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries312_checked (entries312.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries312 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked35_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field35_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field35_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries312_checked (entries312.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries312 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked35_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field35_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field35_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries312_checked (entries312.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries312 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked35_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field35_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression35_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field35_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries312_checked (entries312.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries312 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked36_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field36_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field36_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries312_checked (entries312.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries312 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked36_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field36_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field36_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries312_checked (entries312.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries312 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked36_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field36_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field36_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries320_checked (entries320.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries320 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked36_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field36_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field36_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries320_checked (entries320.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries320 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked36_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field36_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field36_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries320_checked (entries320.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries320 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked36_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field36_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field36_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries320_checked (entries320.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries320 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked36_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field36_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field36_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries320_checked (entries320.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries320 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked36_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field36_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression36_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field36_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries320_checked (entries320.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries320 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked37_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field37_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field37_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries320_checked (entries320.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries320 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked37_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field37_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field37_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries320_checked (entries320.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries320 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked37_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field37_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field37_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries328_checked (entries328.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries328 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked37_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field37_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field37_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries328_checked (entries328.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries328 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked37_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field37_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field37_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries328_checked (entries328.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries328 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked37_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field37_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field37_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries328_checked (entries328.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries328 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked37_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field37_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field37_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries328_checked (entries328.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries328 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked37_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field37_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression37_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field37_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries328_checked (entries328.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries328 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked38_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field38_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field38_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries328_checked (entries328.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries328 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked38_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field38_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field38_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries328_checked (entries328.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries328 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked38_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field38_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field38_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries336_checked (entries336.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries336 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked38_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field38_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field38_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries336_checked (entries336.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries336 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked38_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field38_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field38_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries336_checked (entries336.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries336 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked38_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field38_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field38_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries336_checked (entries336.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries336 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked38_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field38_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field38_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries336_checked (entries336.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries336 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked38_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field38_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression38_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field38_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries336_checked (entries336.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries336 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked39_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field39_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field39_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries336_checked (entries336.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries336 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked39_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field39_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field39_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries336_checked (entries336.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries336 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked39_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field39_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field39_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries344_checked (entries344.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries344 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked39_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field39_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field39_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries344_checked (entries344.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries344 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked39_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field39_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field39_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries344_checked (entries344.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries344 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked39_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field39_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field39_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries344_checked (entries344.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries344 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked39_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field39_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field39_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries344_checked (entries344.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries344 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked39_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field39_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part4.genericExpression39_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field39_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries344_checked (entries344.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries344 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked40_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part5.genericExpression40_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field40_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part5.genericExpression40_0 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field40_0.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries344_checked (entries344.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries344 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked40_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part5.genericExpression40_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field40_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part5.genericExpression40_1 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field40_1.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries344_checked (entries344.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries344 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked40_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part5.genericExpression40_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field40_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part5.genericExpression40_2 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field40_2.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries352_checked (entries352.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries352 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked40_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part5.genericExpression40_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field40_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part5.genericExpression40_3 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field40_3.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries352_checked (entries352.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries352 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked40_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part5.genericExpression40_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field40_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part5.genericExpression40_4 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field40_4.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries352_checked (entries352.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries352 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked40_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part5.genericExpression40_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field40_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part5.genericExpression40_5 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field40_5.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries352_checked (entries352.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries352 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked40_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part5.genericExpression40_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field40_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part5.genericExpression40_6 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field40_6.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries352_checked (entries352.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries352 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked40_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part5.genericExpression40_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field40_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.KeccakUncached.native.part5.genericExpression40_7 Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank Airbender.Compiler.LookupNative.KeccakUncached.native.field40_7.lowered Airbender.Compiler.LookupSourceNative.KeccakUncached.native.bank).check = true :=
    List.all_eq_true.mp entries352_checked (entries352.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries352 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

end Airbender.Compiler.CleanArgumentChecks.KeccakUncached
