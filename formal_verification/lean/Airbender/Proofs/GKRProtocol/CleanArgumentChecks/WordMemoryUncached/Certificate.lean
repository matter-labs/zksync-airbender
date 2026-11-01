import Airbender.Proofs.GKRProtocol.CleanArgumentChecks.WordMemoryUncached.Bindings

namespace Airbender.Compiler.CleanArgumentChecks.WordMemoryUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

private instance : NeZero babyBearModulus := ⟨by decide +kernel⟩

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem originalChecked : originalEntries.all NumericFunctionalBaseChecks.Typed.check = true :=
  NumericFunctionalBaseChecks.check_sound originalEntries data source_binding checked

theorem rangeChecked0 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.rangeExpression0 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank Airbender.Compiler.LookupNative.WordMemoryUncached.native.field1_0.lowered Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.rangeExpression0 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank Airbender.Compiler.LookupNative.WordMemoryUncached.native.field1_0.lowered Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨0, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨0, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked1 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.rangeExpression1 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank Airbender.Compiler.LookupNative.WordMemoryUncached.native.field2_0.lowered Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.rangeExpression1 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank Airbender.Compiler.LookupNative.WordMemoryUncached.native.field2_0.lowered Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨1, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨1, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem rangeChecked2 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.rangeExpression2 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank Airbender.Compiler.LookupNative.WordMemoryUncached.native.field3_0.lowered Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.rangeExpression2 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank Airbender.Compiler.LookupNative.WordMemoryUncached.native.field3_0.lowered Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨2, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨2, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked0 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestampExpression0 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank (Airbender.Compiler.HelperNative.WordMemoryUncached.native.recipe2.expression Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank.placement) Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestampExpression0 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank (Airbender.Compiler.HelperNative.WordMemoryUncached.native.recipe2.expression Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank.placement) Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨3, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨3, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked1 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestampExpression1 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank (Airbender.Compiler.HelperNative.WordMemoryUncached.native.recipe4.expression Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank.placement) Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestampExpression1 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank (Airbender.Compiler.HelperNative.WordMemoryUncached.native.recipe4.expression Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank.placement) Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨4, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨4, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked2 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestampExpression2 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank (Airbender.Compiler.HelperNative.WordMemoryUncached.native.recipe5.expression Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank.placement) Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestampExpression2 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank (Airbender.Compiler.HelperNative.WordMemoryUncached.native.recipe5.expression Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank.placement) Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨5, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨5, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked3 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestampExpression3 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank (Airbender.Compiler.HelperNative.WordMemoryUncached.native.recipe6.expression Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank.placement) Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestampExpression3 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank (Airbender.Compiler.HelperNative.WordMemoryUncached.native.recipe6.expression Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank.placement) Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨6, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨6, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked4 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestampExpression4 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank (Airbender.Compiler.HelperNative.WordMemoryUncached.native.recipe7.expression Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank.placement) Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestampExpression4 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank (Airbender.Compiler.HelperNative.WordMemoryUncached.native.recipe7.expression Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank.placement) Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨7, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨7, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked5 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestampExpression5 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank (Airbender.Compiler.HelperNative.WordMemoryUncached.native.recipe8.expression Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank.placement) Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestampExpression5 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank (Airbender.Compiler.HelperNative.WordMemoryUncached.native.recipe8.expression Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank.placement) Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨8, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨8, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked6 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestampExpression6 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank (Airbender.Compiler.HelperNative.WordMemoryUncached.native.recipe9.expression Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank.placement) Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestampExpression6 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank (Airbender.Compiler.HelperNative.WordMemoryUncached.native.recipe9.expression Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank.placement) Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨9, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨9, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem timestampChecked7 : CleanExpression.nativeCheck Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestampExpression7 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank (Airbender.Compiler.HelperNative.WordMemoryUncached.native.recipe13.expression Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank.placement) Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanArgumentsNative.WordMemoryUncached.native.timestampExpression7 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank (Airbender.Compiler.HelperNative.WordMemoryUncached.native.recipe13.expression Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank.placement) Airbender.Compiler.MemoryNative.WordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨10, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨10, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_0 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.genericExpression0_0 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_0.lowered Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.genericExpression0_0 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_0.lowered Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨11, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨11, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_1 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.genericExpression0_1 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_1.lowered Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.genericExpression0_1 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_1.lowered Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨12, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨12, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_2 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.genericExpression0_2 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_2.lowered Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.genericExpression0_2 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_2.lowered Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨13, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨13, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_3 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.genericExpression0_3 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_3.lowered Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.genericExpression0_3 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_3.lowered Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨14, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨14, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_4 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.genericExpression0_4 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_4.lowered Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.genericExpression0_4 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_4.lowered Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨15, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨15, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_5 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.genericExpression0_5 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_5.lowered Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.genericExpression0_5 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_5.lowered Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨16, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨16, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_6 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.genericExpression0_6 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_6.lowered Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.genericExpression0_6 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_6.lowered Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨17, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨17, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_7 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.genericExpression0_7 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_7.lowered Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.genericExpression0_7 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_7.lowered Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨18, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨18, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

theorem genericChecked0_8 : CleanExpression.nativeCheck Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.genericExpression0_8 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_8.lowered Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank = true := by
  have item : (NumericCleanArgumentChecks.ofNative Airbender.Compiler.CleanGenericArgumentsNative.WordMemoryUncached.native.part0.genericExpression0_8 Airbender.Compiler.CleanArithmeticNative.WordMemoryUncached.native.placement Airbender.Compiler.FullArithmeticNative.WordMemoryUncached.native.bank Airbender.Compiler.LookupNative.WordMemoryUncached.native.field0_8.lowered Airbender.Compiler.LookupSourceNative.WordMemoryUncached.native.bank).check = true :=
    List.all_eq_true.mp originalChecked (originalEntries.get ⟨19, by decide +kernel⟩)
      (List.get_mem originalEntries ⟨19, by decide +kernel⟩)
  simpa only [NumericCleanArgumentChecks.ofNative_check] using item

end Airbender.Compiler.CleanArgumentChecks.WordMemoryUncached
