module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.CleanArgumentChecks.AddSubCached.Bindings

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.CleanArgumentChecks.AddSubCached
open Airbender.Compiler
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=
  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked

theorem rangeChecked0 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpression0 Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank Airbender.Compiler.LookupNative.AddSubCached.native.field0_0.lowered Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpression0 Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank Airbender.Compiler.LookupNative.AddSubCached.native.field0_0.lowered Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨0, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked1 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpression1 Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank Airbender.Compiler.LookupNative.AddSubCached.native.field1_0.lowered Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpression1 Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank Airbender.Compiler.LookupNative.AddSubCached.native.field1_0.lowered Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨1, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked2 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpression2 Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank Airbender.Compiler.LookupNative.AddSubCached.native.field2_0.lowered Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpression2 Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank Airbender.Compiler.LookupNative.AddSubCached.native.field2_0.lowered Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨2, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked3 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpression3 Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank Airbender.Compiler.LookupNative.AddSubCached.native.field3_0.lowered Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpression3 Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank Airbender.Compiler.LookupNative.AddSubCached.native.field3_0.lowered Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨3, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked4 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpression4 Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank Airbender.Compiler.LookupNative.AddSubCached.native.field4_0.lowered Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpression4 Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank Airbender.Compiler.LookupNative.AddSubCached.native.field4_0.lowered Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨4, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked5 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpression5 Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank Airbender.Compiler.LookupNative.AddSubCached.native.field5_0.lowered Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.rangeExpression5 Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank Airbender.Compiler.LookupNative.AddSubCached.native.field5_0.lowered Airbender.Compiler.LookupSourceNative.AddSubCached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨5, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked0 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression0 Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank (Airbender.Compiler.HelperNative.AddSubCached.native.recipe6.expression Airbender.Compiler.MemoryNative.AddSubCached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression0 Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank (Airbender.Compiler.HelperNative.AddSubCached.native.recipe6.expression Airbender.Compiler.MemoryNative.AddSubCached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubCached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨6, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked1 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression1 Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank (Airbender.Compiler.HelperNative.AddSubCached.native.recipe8.expression Airbender.Compiler.MemoryNative.AddSubCached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression1 Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank (Airbender.Compiler.HelperNative.AddSubCached.native.recipe8.expression Airbender.Compiler.MemoryNative.AddSubCached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubCached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨7, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked2 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression2 Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank (Airbender.Compiler.HelperNative.AddSubCached.native.recipe9.expression Airbender.Compiler.MemoryNative.AddSubCached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression2 Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank (Airbender.Compiler.HelperNative.AddSubCached.native.recipe9.expression Airbender.Compiler.MemoryNative.AddSubCached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubCached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨8, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨8, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked3 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression3 Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank (Airbender.Compiler.HelperNative.AddSubCached.native.recipe10.expression Airbender.Compiler.MemoryNative.AddSubCached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression3 Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank (Airbender.Compiler.HelperNative.AddSubCached.native.recipe10.expression Airbender.Compiler.MemoryNative.AddSubCached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubCached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨9, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨9, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked4 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression4 Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank (Airbender.Compiler.HelperNative.AddSubCached.native.recipe11.expression Airbender.Compiler.MemoryNative.AddSubCached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression4 Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank (Airbender.Compiler.HelperNative.AddSubCached.native.recipe11.expression Airbender.Compiler.MemoryNative.AddSubCached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubCached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨10, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨10, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked5 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression5 Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank (Airbender.Compiler.HelperNative.AddSubCached.native.recipe12.expression Airbender.Compiler.MemoryNative.AddSubCached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression5 Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank (Airbender.Compiler.HelperNative.AddSubCached.native.recipe12.expression Airbender.Compiler.MemoryNative.AddSubCached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubCached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨11, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨11, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked6 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression6 Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank (Airbender.Compiler.HelperNative.AddSubCached.native.recipe13.expression Airbender.Compiler.MemoryNative.AddSubCached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression6 Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank (Airbender.Compiler.HelperNative.AddSubCached.native.recipe13.expression Airbender.Compiler.MemoryNative.AddSubCached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubCached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨12, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨12, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked7 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression7 Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank (Airbender.Compiler.HelperNative.AddSubCached.native.recipe17.expression Airbender.Compiler.MemoryNative.AddSubCached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubCached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.AddSubCached.native.timestampExpression7 Airbender.Compiler.CleanArithmeticNative.AddSubCached.native.placement Airbender.Compiler.FullArithmeticNative.AddSubCached.native.bank (Airbender.Compiler.HelperNative.AddSubCached.native.recipe17.expression Airbender.Compiler.MemoryNative.AddSubCached.native.bank.placement) Airbender.Compiler.MemoryNative.AddSubCached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨13, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨13, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

end Airbender.Compiler.CleanArgumentChecks.AddSubCached
