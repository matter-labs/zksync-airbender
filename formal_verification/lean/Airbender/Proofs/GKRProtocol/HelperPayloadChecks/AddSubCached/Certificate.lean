import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.AddSubCached.Bindings

namespace Airbender.Compiler.HelperPayloadChecks.AddSubCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem operand6 : (Airbender.Compiler.HelperNative.AddSubCached.native.candidate6).check Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.AddSubCached.native.bank).check Airbender.Compiler.HelperNative.AddSubCached.native.recipe6 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.AddSubCached.native.recipe6).baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubCached.native.candidate6
  Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubCached.native.typing) data 0
    (row0_view.trans row0_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand8 : (Airbender.Compiler.HelperNative.AddSubCached.native.candidate8).check Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.AddSubCached.native.bank).check Airbender.Compiler.HelperNative.AddSubCached.native.recipe8 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.AddSubCached.native.recipe8).baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubCached.native.candidate8
  Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubCached.native.typing) data 1
    (row1_view.trans row1_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand9 : (Airbender.Compiler.HelperNative.AddSubCached.native.candidate9).check Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.AddSubCached.native.bank).check Airbender.Compiler.HelperNative.AddSubCached.native.recipe9 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.AddSubCached.native.recipe9).baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubCached.native.candidate9
  Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubCached.native.typing) data 2
    (row2_view.trans row2_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand10 : (Airbender.Compiler.HelperNative.AddSubCached.native.candidate10).check Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.AddSubCached.native.bank).check Airbender.Compiler.HelperNative.AddSubCached.native.recipe10 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.AddSubCached.native.recipe10).baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubCached.native.candidate10
  Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubCached.native.typing) data 3
    (row3_view.trans row3_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand11 : (Airbender.Compiler.HelperNative.AddSubCached.native.candidate11).check Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.AddSubCached.native.bank).check Airbender.Compiler.HelperNative.AddSubCached.native.recipe11 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.AddSubCached.native.recipe11).baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubCached.native.candidate11
  Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubCached.native.typing) data 4
    (row4_view.trans row4_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand12 : (Airbender.Compiler.HelperNative.AddSubCached.native.candidate12).check Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.AddSubCached.native.bank).check Airbender.Compiler.HelperNative.AddSubCached.native.recipe12 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.AddSubCached.native.recipe12).baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubCached.native.candidate12
  Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubCached.native.typing) data 5
    (row5_view.trans row5_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand13 : (Airbender.Compiler.HelperNative.AddSubCached.native.candidate13).check Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.AddSubCached.native.bank).check Airbender.Compiler.HelperNative.AddSubCached.native.recipe13 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.AddSubCached.native.recipe13).baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubCached.native.candidate13
  Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubCached.native.typing) data 6
    (row6_view.trans row6_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand17 : (Airbender.Compiler.HelperNative.AddSubCached.native.candidate17).check Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.AddSubCached.native.bank).check Airbender.Compiler.HelperNative.AddSubCached.native.recipe17 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.AddSubCached.native.recipe17).baseCheck Airbender.Compiler.ConsumerNative.AddSubCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.AddSubCached.native.candidate17
  Airbender.Compiler.HelperNative.AddSubCached.native.placement Airbender.Compiler.MemoryNative.AddSubCached.native.bank
  Airbender.Compiler.ConsumerNative.AddSubCached.native.typing) data 7
    (row7_view.trans row7_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

end Airbender.Compiler.HelperPayloadChecks.AddSubCached
