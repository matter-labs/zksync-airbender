import Airbender.Proofs.GKRProtocol.CleanArgumentChecks.AddSubUncached.Bindings

namespace Airbender.Compiler.CleanArgumentChecks.AddSubUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=
  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked

theorem rangeChecked0 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.rangeExpression0 Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank Airbender.Compiler.LookupNative.AddSubUncached.native.field0_0.lowered Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.rangeExpression0 Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank Airbender.Compiler.LookupNative.AddSubUncached.native.field0_0.lowered Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨0, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked1 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.rangeExpression1 Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank Airbender.Compiler.LookupNative.AddSubUncached.native.field1_0.lowered Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.rangeExpression1 Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank Airbender.Compiler.LookupNative.AddSubUncached.native.field1_0.lowered Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨1, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked2 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.rangeExpression2 Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank Airbender.Compiler.LookupNative.AddSubUncached.native.field2_0.lowered Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.rangeExpression2 Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank Airbender.Compiler.LookupNative.AddSubUncached.native.field2_0.lowered Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨2, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked3 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.rangeExpression3 Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank Airbender.Compiler.LookupNative.AddSubUncached.native.field3_0.lowered Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.rangeExpression3 Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank Airbender.Compiler.LookupNative.AddSubUncached.native.field3_0.lowered Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨3, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked4 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.rangeExpression4 Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank Airbender.Compiler.LookupNative.AddSubUncached.native.field4_0.lowered Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.rangeExpression4 Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank Airbender.Compiler.LookupNative.AddSubUncached.native.field4_0.lowered Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨4, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked5 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.rangeExpression5 Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank Airbender.Compiler.LookupNative.AddSubUncached.native.field5_0.lowered Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.rangeExpression5 Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank Airbender.Compiler.LookupNative.AddSubUncached.native.field5_0.lowered Airbender.Compiler.LookupSourceNative.AddSubUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨5, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked0 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression0 Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank (Airbender.Compiler.HelperNative.AddSubUncached.native.recipe6.expression Airbender.Compiler.MemoryNative.AddSubUncached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression0 Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank (Airbender.Compiler.HelperNative.AddSubUncached.native.recipe6.expression Airbender.Compiler.MemoryNative.AddSubUncached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨6, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked1 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression1 Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank (Airbender.Compiler.HelperNative.AddSubUncached.native.recipe8.expression Airbender.Compiler.MemoryNative.AddSubUncached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression1 Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank (Airbender.Compiler.HelperNative.AddSubUncached.native.recipe8.expression Airbender.Compiler.MemoryNative.AddSubUncached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨7, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked2 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression2 Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank (Airbender.Compiler.HelperNative.AddSubUncached.native.recipe9.expression Airbender.Compiler.MemoryNative.AddSubUncached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression2 Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank (Airbender.Compiler.HelperNative.AddSubUncached.native.recipe9.expression Airbender.Compiler.MemoryNative.AddSubUncached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨8, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨8, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked3 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression3 Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank (Airbender.Compiler.HelperNative.AddSubUncached.native.recipe10.expression Airbender.Compiler.MemoryNative.AddSubUncached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression3 Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank (Airbender.Compiler.HelperNative.AddSubUncached.native.recipe10.expression Airbender.Compiler.MemoryNative.AddSubUncached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨9, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨9, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked4 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression4 Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank (Airbender.Compiler.HelperNative.AddSubUncached.native.recipe11.expression Airbender.Compiler.MemoryNative.AddSubUncached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression4 Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank (Airbender.Compiler.HelperNative.AddSubUncached.native.recipe11.expression Airbender.Compiler.MemoryNative.AddSubUncached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨10, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨10, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked5 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression5 Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank (Airbender.Compiler.HelperNative.AddSubUncached.native.recipe12.expression Airbender.Compiler.MemoryNative.AddSubUncached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression5 Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank (Airbender.Compiler.HelperNative.AddSubUncached.native.recipe12.expression Airbender.Compiler.MemoryNative.AddSubUncached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨11, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨11, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked6 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression6 Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank (Airbender.Compiler.HelperNative.AddSubUncached.native.recipe13.expression Airbender.Compiler.MemoryNative.AddSubUncached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression6 Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank (Airbender.Compiler.HelperNative.AddSubUncached.native.recipe13.expression Airbender.Compiler.MemoryNative.AddSubUncached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨12, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨12, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked7 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression7 Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank (Airbender.Compiler.HelperNative.AddSubUncached.native.recipe17.expression Airbender.Compiler.MemoryNative.AddSubUncached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.AddSubUncached.native.timestampExpression7 Airbender.Compiler.CleanArithmeticNative.AddSubUncached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubUncached.native.bank (Airbender.Compiler.HelperNative.AddSubUncached.native.recipe17.expression Airbender.Compiler.MemoryNative.AddSubUncached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨13, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨13, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

end Airbender.Compiler.CleanArgumentChecks.AddSubUncached
