import Airbender.Proofs.GKRProtocol.CleanArgumentChecks.BigintUncached.Bindings

namespace Airbender.Compiler.CleanArgumentChecks.BigintUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=
  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked

noncomputable def entries0 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field61_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field62_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field63_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression3 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field64_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression4 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field65_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression5 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field66_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression6 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field67_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression7 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field68_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank]

theorem entries0_binding : ((originalEntries.drop 0).take 8) = entries0 := by rfl

theorem entries0_checked : entries0.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries0_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 0 8

noncomputable def entries8 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression8 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field69_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression9 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field70_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression10 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field71_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression11 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field72_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression12 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field73_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression13 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field74_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression14 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field75_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression15 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field76_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank]

theorem entries8_binding : ((originalEntries.drop 8).take 8) = entries8 := by rfl

theorem entries8_checked : entries8.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries8_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 8 8

noncomputable def entries16 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression16 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field77_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression17 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field78_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression18 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field79_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression19 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field80_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression20 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field81_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression21 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field82_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression22 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field83_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression23 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field84_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank]

theorem entries16_binding : ((originalEntries.drop 16).take 8) = entries16 := by rfl

theorem entries16_checked : entries16.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries16_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 16 8

noncomputable def entries24 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression24 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field85_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression25 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field86_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression26 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field87_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression27 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field88_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression28 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field89_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression29 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field90_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression30 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field91_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression31 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field92_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank]

theorem entries24_binding : ((originalEntries.drop 24).take 8) = entries24 := by rfl

theorem entries24_checked : entries24.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries24_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 24 8

noncomputable def entries32 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe16.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe18.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe19.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression3 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe20.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression4 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe21.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression5 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe22.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression6 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe23.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression7 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe24.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank]

theorem entries32_binding : ((originalEntries.drop 32).take 8) = entries32 := by rfl

theorem entries32_checked : entries32.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries32_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 32 8

noncomputable def entries40 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression8 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe25.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression9 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe26.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression10 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe27.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression11 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe28.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression12 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe29.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression13 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe30.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression14 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe31.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression15 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe32.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank]

theorem entries40_binding : ((originalEntries.drop 40).take 8) = entries40 := by rfl

theorem entries40_checked : entries40.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries40_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 40 8

noncomputable def entries48 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression16 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe33.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression17 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe34.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression18 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe35.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression19 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe36.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression20 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe37.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression21 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe38.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression22 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe39.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression23 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe40.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank]

theorem entries48_binding : ((originalEntries.drop 48).take 8) = entries48 := by rfl

theorem entries48_checked : entries48.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries48_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 48 8

noncomputable def entries56 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression24 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe41.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression25 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe42.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression26 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe43.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression27 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe44.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression28 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe45.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression29 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe46.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression30 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe47.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression31 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe48.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank]

theorem entries56_binding : ((originalEntries.drop 56).take 8) = entries56 := by rfl

theorem entries56_checked : entries56.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries56_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 56 8

noncomputable def entries64 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression32 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe49.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression33 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe50.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression34 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe51.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression35 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe52.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression36 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe53.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression37 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe54.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression38 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe55.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression39 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe56.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank]

theorem entries64_binding : ((originalEntries.drop 64).take 8) = entries64 := by rfl

theorem entries64_checked : entries64.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries64_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 64 8

noncomputable def entries72 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression40 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe57.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression0_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field0_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression0_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field0_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression0_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field0_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression1_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field1_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression1_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field1_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression1_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field1_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression2_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field2_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank]

theorem entries72_binding : ((originalEntries.drop 72).take 8) = entries72 := by rfl

theorem entries72_checked : entries72.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries72_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 72 8

noncomputable def entries80 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression2_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field2_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression2_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field2_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression3_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field3_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression3_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field3_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression3_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field3_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression4_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field4_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression4_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field4_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression4_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field4_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank]

theorem entries80_binding : ((originalEntries.drop 80).take 8) = entries80 := by rfl

theorem entries80_checked : entries80.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries80_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 80 8

noncomputable def entries88 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression5_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field5_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression5_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field5_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression5_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field5_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression6_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field6_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression6_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field6_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression6_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field6_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression7_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field7_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression7_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field7_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank]

theorem entries88_binding : ((originalEntries.drop 88).take 8) = entries88 := by rfl

theorem entries88_checked : entries88.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries88_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 88 8

noncomputable def entries96 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression7_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field7_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression8_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field8_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression8_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field8_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression8_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field8_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression9_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field9_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression9_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field9_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression9_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field9_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression10_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field10_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank]

theorem entries96_binding : ((originalEntries.drop 96).take 8) = entries96 := by rfl

theorem entries96_checked : entries96.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries96_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 96 8

noncomputable def entries104 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression10_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field10_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression10_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field10_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression11_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field11_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression11_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field11_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression11_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field11_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression12_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field12_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression12_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field12_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression12_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field12_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank]

theorem entries104_binding : ((originalEntries.drop 104).take 8) = entries104 := by rfl

theorem entries104_checked : entries104.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries104_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 104 8

noncomputable def entries112 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression13_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field13_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression13_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field13_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression13_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field13_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression14_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field14_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression14_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field14_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression14_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field14_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression15_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field15_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression15_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field15_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank]

theorem entries112_binding : ((originalEntries.drop 112).take 8) = entries112 := by rfl

theorem entries112_checked : entries112.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries112_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 112 8

noncomputable def entries120 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression15_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field15_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression16_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field16_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression16_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field16_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression16_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field16_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression17_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field17_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression17_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field17_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression17_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field17_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression18_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field18_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank]

theorem entries120_binding : ((originalEntries.drop 120).take 8) = entries120 := by rfl

theorem entries120_checked : entries120.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries120_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 120 8

noncomputable def entries128 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression18_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field18_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression18_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field18_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression19_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field19_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression19_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field19_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression19_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field19_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression20_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field20_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression20_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field20_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression20_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field20_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank]

theorem entries128_binding : ((originalEntries.drop 128).take 8) = entries128 := by rfl

theorem entries128_checked : entries128.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries128_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 128 8

noncomputable def entries136 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression21_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field21_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression21_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field21_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression21_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field21_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression22_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field22_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression22_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field22_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression22_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field22_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression23_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field23_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression23_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field23_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank]

theorem entries136_binding : ((originalEntries.drop 136).take 8) = entries136 := by rfl

theorem entries136_checked : entries136.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries136_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 136 8

noncomputable def entries144 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression23_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field23_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression24_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field24_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression24_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field24_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression24_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field24_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression25_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field25_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression25_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field25_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression25_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field25_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression26_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field26_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank]

theorem entries144_binding : ((originalEntries.drop 144).take 8) = entries144 := by rfl

theorem entries144_checked : entries144.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries144_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 144 8

noncomputable def entries152 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression26_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field26_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression26_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field26_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression27_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field27_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression27_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field27_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression27_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field27_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression28_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field28_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression28_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field28_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression28_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field28_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank]

theorem entries152_binding : ((originalEntries.drop 152).take 8) = entries152 := by rfl

theorem entries152_checked : entries152.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries152_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 152 8

noncomputable def entries160 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression29_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field29_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression29_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field29_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression29_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field29_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression30_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field30_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression30_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field30_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression30_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field30_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression31_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field31_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression31_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field31_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank]

theorem entries160_binding : ((originalEntries.drop 160).take 8) = entries160 := by rfl

theorem entries160_checked : entries160.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries160_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 160 8

noncomputable def entries168 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression31_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field31_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression32_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field32_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression32_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field32_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression32_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field32_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression33_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field33_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression33_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field33_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression33_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field33_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression34_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field34_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank]

theorem entries168_binding : ((originalEntries.drop 168).take 8) = entries168 := by rfl

theorem entries168_checked : entries168.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries168_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 168 8

noncomputable def entries176 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression34_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field34_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression34_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field34_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression35_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field35_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression35_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field35_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression35_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field35_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression36_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field36_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression36_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field36_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression36_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field36_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank]

theorem entries176_binding : ((originalEntries.drop 176).take 8) = entries176 := by rfl

theorem entries176_checked : entries176.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries176_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 176 8

noncomputable def entries184 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression37_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field37_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression37_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field37_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression37_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field37_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression38_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field38_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression38_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field38_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression38_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field38_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression39_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field39_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression39_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field39_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank]

theorem entries184_binding : ((originalEntries.drop 184).take 8) = entries184 := by rfl

theorem entries184_checked : entries184.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries184_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 184 8

noncomputable def entries192 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression39_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field39_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression40_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field40_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression40_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field40_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression40_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field40_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression41_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field41_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression41_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field41_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression41_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field41_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression42_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field42_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank]

theorem entries192_binding : ((originalEntries.drop 192).take 8) = entries192 := by rfl

theorem entries192_checked : entries192.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries192_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 192 8

noncomputable def entries200 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression42_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field42_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression42_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field42_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression43_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field43_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression43_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field43_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression43_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field43_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression44_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field44_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression44_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field44_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression44_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field44_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank]

theorem entries200_binding : ((originalEntries.drop 200).take 8) = entries200 := by rfl

theorem entries200_checked : entries200.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries200_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 200 8

noncomputable def entries208 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression45_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field45_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression45_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field45_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression45_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field45_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression46_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field46_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression46_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field46_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression46_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field46_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression47_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field47_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression47_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field47_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank]

theorem entries208_binding : ((originalEntries.drop 208).take 8) = entries208 := by rfl

theorem entries208_checked : entries208.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries208_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 208 8

noncomputable def entries216 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression47_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field47_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression48_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field48_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression48_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field48_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression48_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field48_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression49_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field49_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression49_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field49_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression49_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field49_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression50_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field50_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank]

theorem entries216_binding : ((originalEntries.drop 216).take 8) = entries216 := by rfl

theorem entries216_checked : entries216.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries216_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 216 8

noncomputable def entries224 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression50_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field50_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression50_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field50_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression51_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field51_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression51_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field51_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression51_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field51_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression52_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field52_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression52_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field52_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression52_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field52_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank]

theorem entries224_binding : ((originalEntries.drop 224).take 8) = entries224 := by rfl

theorem entries224_checked : entries224.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries224_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 224 8

noncomputable def entries232 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression53_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field53_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression53_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field53_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression53_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field53_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression54_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field54_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression54_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field54_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression54_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field54_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression55_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field55_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression55_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field55_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank]

theorem entries232_binding : ((originalEntries.drop 232).take 8) = entries232 := by rfl

theorem entries232_checked : entries232.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries232_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 232 8

noncomputable def entries240 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression55_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field55_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression56_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field56_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression56_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field56_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression56_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field56_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression57_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field57_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression57_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field57_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression57_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field57_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression58_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field58_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank]

theorem entries240_binding : ((originalEntries.drop 240).take 8) = entries240 := by rfl

theorem entries240_checked : entries240.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries240_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 240 8

noncomputable def entries248 := [
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression58_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field58_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression58_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field58_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression59_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field59_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression59_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field59_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression59_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field59_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression60_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field60_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression60_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field60_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank,
  NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression60_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field60_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank]

theorem entries248_binding : ((originalEntries.drop 248).take 8) = entries248 := by rfl

theorem entries248_checked : entries248.all NumericFunctionalBaseChecks.Typed.check = true := by
  rw [← entries248_binding]
  exact NumericCleanArgumentChecks.checked_window originalChecked 248 8

theorem rangeChecked0 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field61_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field61_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries0 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked1 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field62_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field62_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries0 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked2 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field63_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field63_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries0 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked3 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression3 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field64_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression3 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field64_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries0 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked4 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression4 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field65_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression4 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field65_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries0 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked5 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression5 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field66_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression5 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field66_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries0 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked6 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression6 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field67_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression6 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field67_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries0 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked7 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression7 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field68_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression7 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field68_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries0_checked (entries0.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries0 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked8 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression8 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field69_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression8 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field69_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries8 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked9 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression9 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field70_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression9 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field70_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries8 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked10 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression10 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field71_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression10 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field71_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries8 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked11 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression11 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field72_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression11 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field72_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries8 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked12 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression12 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field73_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression12 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field73_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries8 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked13 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression13 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field74_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression13 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field74_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries8 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked14 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression14 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field75_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression14 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field75_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries8 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked15 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression15 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field76_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression15 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field76_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries8_checked (entries8.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries8 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked16 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression16 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field77_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression16 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field77_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries16 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked17 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression17 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field78_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression17 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field78_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries16 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked18 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression18 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field79_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression18 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field79_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries16 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked19 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression19 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field80_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression19 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field80_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries16 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked20 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression20 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field81_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression20 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field81_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries16 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked21 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression21 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field82_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression21 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field82_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries16 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked22 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression22 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field83_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression22 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field83_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries16 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked23 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression23 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field84_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression23 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field84_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries16_checked (entries16.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries16 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked24 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression24 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field85_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression24 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field85_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries24 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked25 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression25 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field86_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression25 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field86_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries24 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked26 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression26 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field87_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression26 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field87_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries24 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked27 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression27 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field88_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression27 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field88_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries24 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked28 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression28 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field89_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression28 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field89_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries24 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked29 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression29 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field90_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression29 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field90_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries24 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked30 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression30 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field91_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression30 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field91_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries24 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked31 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression31 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field92_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.rangeExpression31 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field92_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries24_checked (entries24.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries24 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked0 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe16.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe16.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries32 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked1 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe18.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe18.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries32 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked2 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe19.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe19.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries32 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked3 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression3 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe20.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression3 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe20.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries32 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked4 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression4 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe21.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression4 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe21.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries32 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked5 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression5 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe22.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression5 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe22.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries32 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked6 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression6 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe23.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression6 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe23.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries32 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked7 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression7 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe24.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression7 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe24.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries32_checked (entries32.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries32 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked8 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression8 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe25.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression8 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe25.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries40 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked9 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression9 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe26.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression9 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe26.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries40 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked10 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression10 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe27.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression10 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe27.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries40 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked11 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression11 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe28.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression11 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe28.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries40 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked12 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression12 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe29.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression12 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe29.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries40 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked13 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression13 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe30.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression13 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe30.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries40 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked14 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression14 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe31.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression14 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe31.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries40 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked15 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression15 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe32.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression15 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe32.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries40_checked (entries40.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries40 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked16 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression16 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe33.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression16 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe33.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries48 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked17 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression17 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe34.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression17 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe34.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries48 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked18 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression18 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe35.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression18 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe35.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries48 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked19 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression19 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe36.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression19 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe36.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries48 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked20 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression20 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe37.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression20 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe37.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries48 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked21 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression21 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe38.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression21 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe38.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries48 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked22 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression22 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe39.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression22 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe39.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries48 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked23 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression23 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe40.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression23 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe40.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries48_checked (entries48.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries48 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked24 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression24 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe41.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression24 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe41.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries56 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked25 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression25 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe42.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression25 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe42.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries56 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked26 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression26 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe43.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression26 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe43.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries56 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked27 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression27 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe44.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression27 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe44.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries56 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked28 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression28 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe45.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression28 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe45.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries56 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked29 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression29 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe46.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression29 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe46.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries56 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked30 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression30 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe47.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression30 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe47.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries56 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked31 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression31 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe48.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression31 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe48.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries56_checked (entries56.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries56 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked32 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression32 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe49.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression32 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe49.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries64 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked33 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression33 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe50.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression33 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe50.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries64 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked34 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression34 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe51.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression34 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe51.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries64 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked35 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression35 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe52.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression35 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe52.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries64 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked36 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression36 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe53.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression36 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe53.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries64 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked37 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression37 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe54.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression37 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe54.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries64 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked38 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression38 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe55.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression38 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe55.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries64 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked39 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression39 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe56.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression39 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe56.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries64_checked (entries64.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries64 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked40 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression40 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe57.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.BigintUncached.native.timestampExpression40 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank (Airbender.Compiler.HelperNative.BigintUncached.native.recipe57.expression Airbender.Compiler.MemoryNative.BigintUncached.native.bank.placement) Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries72 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression0_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field0_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression0_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field0_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries72 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression0_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field0_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression0_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field0_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries72 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression0_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field0_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression0_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field0_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries72 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked1_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression1_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field1_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression1_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field1_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries72 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked1_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression1_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field1_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression1_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field1_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries72 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked1_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression1_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field1_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression1_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field1_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries72 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked2_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression2_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field2_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression2_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field2_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries72_checked (entries72.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries72 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked2_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression2_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field2_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression2_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field2_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries80 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked2_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression2_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field2_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression2_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field2_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries80 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked3_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression3_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field3_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression3_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field3_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries80 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked3_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression3_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field3_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression3_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field3_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries80 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked3_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression3_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field3_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression3_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field3_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries80 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked4_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression4_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field4_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression4_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field4_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries80 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked4_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression4_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field4_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression4_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field4_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries80 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked4_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression4_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field4_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression4_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field4_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries80_checked (entries80.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries80 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked5_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression5_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field5_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression5_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field5_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries88 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked5_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression5_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field5_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression5_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field5_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries88 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked5_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression5_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field5_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression5_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field5_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries88 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked6_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression6_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field6_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression6_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field6_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries88 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked6_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression6_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field6_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression6_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field6_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries88 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked6_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression6_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field6_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression6_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field6_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries88 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked7_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression7_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field7_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression7_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field7_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries88 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked7_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression7_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field7_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression7_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field7_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries88_checked (entries88.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries88 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked7_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression7_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field7_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part0.genericExpression7_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field7_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries96 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked8_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression8_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field8_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression8_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field8_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries96 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked8_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression8_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field8_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression8_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field8_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries96 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked8_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression8_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field8_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression8_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field8_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries96 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked9_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression9_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field9_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression9_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field9_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries96 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked9_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression9_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field9_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression9_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field9_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries96 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked9_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression9_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field9_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression9_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field9_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries96 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked10_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression10_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field10_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression10_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field10_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries96_checked (entries96.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries96 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked10_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression10_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field10_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression10_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field10_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries104 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked10_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression10_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field10_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression10_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field10_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries104 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked11_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression11_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field11_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression11_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field11_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries104 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked11_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression11_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field11_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression11_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field11_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries104 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked11_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression11_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field11_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression11_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field11_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries104 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked12_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression12_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field12_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression12_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field12_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries104 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked12_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression12_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field12_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression12_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field12_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries104 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked12_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression12_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field12_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression12_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field12_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries104_checked (entries104.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries104 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked13_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression13_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field13_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression13_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field13_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries112 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked13_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression13_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field13_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression13_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field13_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries112 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked13_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression13_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field13_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression13_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field13_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries112 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked14_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression14_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field14_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression14_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field14_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries112 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked14_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression14_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field14_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression14_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field14_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries112 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked14_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression14_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field14_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression14_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field14_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries112 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked15_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression15_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field15_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression15_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field15_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries112 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked15_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression15_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field15_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression15_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field15_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries112_checked (entries112.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries112 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked15_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression15_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field15_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part1.genericExpression15_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field15_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries120 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked16_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression16_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field16_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression16_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field16_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries120 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked16_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression16_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field16_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression16_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field16_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries120 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked16_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression16_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field16_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression16_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field16_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries120 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked17_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression17_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field17_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression17_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field17_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries120 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked17_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression17_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field17_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression17_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field17_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries120 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked17_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression17_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field17_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression17_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field17_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries120 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked18_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression18_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field18_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression18_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field18_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries120_checked (entries120.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries120 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked18_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression18_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field18_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression18_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field18_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries128 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked18_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression18_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field18_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression18_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field18_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries128 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked19_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression19_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field19_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression19_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field19_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries128 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked19_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression19_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field19_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression19_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field19_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries128 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked19_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression19_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field19_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression19_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field19_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries128 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked20_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression20_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field20_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression20_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field20_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries128 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked20_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression20_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field20_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression20_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field20_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries128 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked20_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression20_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field20_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression20_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field20_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries128_checked (entries128.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries128 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked21_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression21_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field21_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression21_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field21_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries136 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked21_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression21_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field21_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression21_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field21_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries136 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked21_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression21_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field21_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression21_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field21_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries136 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked22_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression22_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field22_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression22_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field22_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries136 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked22_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression22_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field22_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression22_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field22_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries136 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked22_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression22_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field22_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression22_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field22_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries136 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked23_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression23_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field23_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression23_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field23_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries136 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked23_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression23_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field23_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression23_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field23_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries136_checked (entries136.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries136 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked23_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression23_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field23_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part2.genericExpression23_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field23_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries144 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked24_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression24_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field24_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression24_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field24_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries144 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked24_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression24_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field24_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression24_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field24_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries144 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked24_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression24_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field24_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression24_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field24_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries144 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked25_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression25_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field25_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression25_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field25_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries144 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked25_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression25_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field25_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression25_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field25_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries144 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked25_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression25_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field25_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression25_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field25_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries144 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked26_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression26_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field26_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression26_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field26_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries144_checked (entries144.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries144 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked26_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression26_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field26_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression26_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field26_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries152 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked26_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression26_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field26_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression26_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field26_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries152 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked27_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression27_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field27_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression27_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field27_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries152 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked27_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression27_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field27_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression27_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field27_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries152 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked27_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression27_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field27_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression27_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field27_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries152 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked28_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression28_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field28_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression28_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field28_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries152 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked28_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression28_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field28_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression28_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field28_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries152 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked28_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression28_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field28_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression28_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field28_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries152_checked (entries152.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries152 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked29_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression29_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field29_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression29_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field29_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries160 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked29_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression29_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field29_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression29_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field29_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries160 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked29_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression29_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field29_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression29_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field29_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries160 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked30_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression30_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field30_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression30_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field30_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries160 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked30_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression30_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field30_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression30_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field30_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries160 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked30_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression30_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field30_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression30_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field30_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries160 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked31_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression31_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field31_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression31_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field31_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries160 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked31_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression31_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field31_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression31_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field31_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries160_checked (entries160.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries160 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked31_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression31_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field31_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part3.genericExpression31_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field31_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries168 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked32_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression32_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field32_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression32_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field32_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries168 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked32_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression32_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field32_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression32_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field32_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries168 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked32_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression32_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field32_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression32_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field32_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries168 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked33_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression33_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field33_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression33_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field33_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries168 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked33_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression33_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field33_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression33_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field33_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries168 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked33_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression33_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field33_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression33_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field33_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries168 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked34_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression34_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field34_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression34_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field34_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries168_checked (entries168.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries168 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked34_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression34_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field34_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression34_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field34_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries176 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked34_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression34_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field34_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression34_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field34_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries176 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked35_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression35_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field35_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression35_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field35_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries176 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked35_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression35_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field35_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression35_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field35_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries176 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked35_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression35_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field35_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression35_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field35_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries176 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked36_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression36_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field36_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression36_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field36_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries176 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked36_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression36_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field36_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression36_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field36_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries176 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked36_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression36_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field36_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression36_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field36_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries176_checked (entries176.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries176 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked37_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression37_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field37_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression37_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field37_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries184 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked37_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression37_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field37_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression37_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field37_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries184 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked37_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression37_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field37_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression37_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field37_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries184 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked38_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression38_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field38_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression38_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field38_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries184 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked38_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression38_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field38_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression38_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field38_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries184 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked38_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression38_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field38_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression38_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field38_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries184 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked39_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression39_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field39_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression39_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field39_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries184 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked39_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression39_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field39_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression39_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field39_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries184_checked (entries184.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries184 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked39_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression39_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field39_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part4.genericExpression39_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field39_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries192 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked40_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression40_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field40_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression40_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field40_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries192 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked40_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression40_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field40_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression40_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field40_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries192 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked40_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression40_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field40_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression40_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field40_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries192 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked41_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression41_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field41_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression41_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field41_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries192 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked41_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression41_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field41_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression41_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field41_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries192 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked41_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression41_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field41_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression41_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field41_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries192 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked42_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression42_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field42_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression42_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field42_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries192_checked (entries192.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries192 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked42_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression42_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field42_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression42_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field42_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries200 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked42_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression42_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field42_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression42_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field42_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries200 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked43_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression43_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field43_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression43_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field43_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries200 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked43_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression43_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field43_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression43_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field43_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries200 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked43_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression43_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field43_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression43_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field43_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries200 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked44_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression44_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field44_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression44_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field44_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries200 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked44_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression44_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field44_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression44_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field44_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries200 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked44_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression44_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field44_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression44_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field44_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries200_checked (entries200.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries200 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked45_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression45_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field45_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression45_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field45_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries208 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked45_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression45_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field45_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression45_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field45_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries208 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked45_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression45_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field45_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression45_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field45_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries208 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked46_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression46_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field46_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression46_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field46_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries208 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked46_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression46_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field46_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression46_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field46_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries208 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked46_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression46_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field46_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression46_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field46_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries208 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked47_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression47_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field47_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression47_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field47_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries208 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked47_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression47_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field47_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression47_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field47_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries208_checked (entries208.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries208 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked47_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression47_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field47_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part5.genericExpression47_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field47_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries216 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked48_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression48_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field48_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression48_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field48_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries216 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked48_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression48_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field48_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression48_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field48_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries216 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked48_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression48_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field48_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression48_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field48_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries216 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked49_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression49_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field49_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression49_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field49_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries216 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked49_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression49_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field49_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression49_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field49_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries216 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked49_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression49_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field49_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression49_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field49_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries216 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked50_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression50_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field50_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression50_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field50_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries216_checked (entries216.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries216 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked50_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression50_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field50_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression50_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field50_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries224 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked50_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression50_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field50_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression50_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field50_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries224 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked51_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression51_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field51_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression51_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field51_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries224 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked51_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression51_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field51_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression51_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field51_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries224 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked51_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression51_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field51_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression51_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field51_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries224 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked52_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression52_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field52_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression52_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field52_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries224 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked52_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression52_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field52_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression52_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field52_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries224 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked52_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression52_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field52_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression52_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field52_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries224_checked (entries224.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries224 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked53_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression53_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field53_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression53_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field53_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries232 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked53_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression53_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field53_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression53_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field53_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries232 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked53_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression53_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field53_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression53_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field53_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries232 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked54_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression54_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field54_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression54_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field54_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries232 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked54_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression54_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field54_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression54_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field54_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries232 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked54_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression54_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field54_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression54_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field54_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries232 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked55_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression55_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field55_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression55_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field55_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries232 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked55_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression55_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field55_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression55_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field55_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries232_checked (entries232.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries232 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked55_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression55_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field55_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part6.genericExpression55_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field55_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries240 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked56_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression56_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field56_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression56_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field56_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries240 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked56_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression56_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field56_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression56_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field56_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries240 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked56_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression56_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field56_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression56_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field56_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries240 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked57_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression57_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field57_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression57_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field57_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries240 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked57_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression57_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field57_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression57_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field57_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries240 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked57_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression57_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field57_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression57_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field57_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries240 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked58_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression58_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field58_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression58_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field58_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries240_checked (entries240.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries240 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked58_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression58_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field58_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression58_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field58_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨0, by decide +kernel⟩)
      (List.get_mem entries248 ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked58_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression58_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field58_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression58_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field58_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨1, by decide +kernel⟩)
      (List.get_mem entries248 ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked59_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression59_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field59_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression59_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field59_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨2, by decide +kernel⟩)
      (List.get_mem entries248 ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked59_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression59_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field59_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression59_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field59_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨3, by decide +kernel⟩)
      (List.get_mem entries248 ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked59_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression59_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field59_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression59_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field59_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨4, by decide +kernel⟩)
      (List.get_mem entries248 ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked60_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression60_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field60_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression60_0 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field60_0.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨5, by decide +kernel⟩)
      (List.get_mem entries248 ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked60_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression60_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field60_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression60_1 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field60_1.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨6, by decide +kernel⟩)
      (List.get_mem entries248 ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked60_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression60_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field60_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.BigintUncached.native.part7.genericExpression60_2 Airbender.Compiler.CleanArithmeticNative.BigintUncached.native.placement Airbender.Compiler.FullArithmeticNative.BigintUncached.native.bank Airbender.Compiler.LookupNative.BigintUncached.native.field60_2.lowered Airbender.Compiler.LookupSourceNative.BigintUncached.native.bank).check = true :=
    List.all_eq_true.mp entries248_checked (entries248.get ⟨7, by decide +kernel⟩)
      (List.get_mem entries248 ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

end Airbender.Compiler.CleanArgumentChecks.BigintUncached
