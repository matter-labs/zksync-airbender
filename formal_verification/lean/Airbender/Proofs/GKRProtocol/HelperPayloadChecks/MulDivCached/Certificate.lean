import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.MulDivCached.Bindings

namespace Airbender.Compiler.HelperPayloadChecks.MulDivCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem operand8 : (Airbender.Compiler.HelperNative.MulDivCached.native.candidate8).check Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.MulDivCached.native.bank).check Airbender.Compiler.HelperNative.MulDivCached.native.recipe8 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.MulDivCached.native.recipe8).baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate8
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing) data 0
    (row0_view.trans row0_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand10 : (Airbender.Compiler.HelperNative.MulDivCached.native.candidate10).check Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.MulDivCached.native.bank).check Airbender.Compiler.HelperNative.MulDivCached.native.recipe10 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.MulDivCached.native.recipe10).baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate10
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing) data 1
    (row1_view.trans row1_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand11 : (Airbender.Compiler.HelperNative.MulDivCached.native.candidate11).check Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.MulDivCached.native.bank).check Airbender.Compiler.HelperNative.MulDivCached.native.recipe11 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.MulDivCached.native.recipe11).baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate11
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing) data 2
    (row2_view.trans row2_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand12 : (Airbender.Compiler.HelperNative.MulDivCached.native.candidate12).check Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.MulDivCached.native.bank).check Airbender.Compiler.HelperNative.MulDivCached.native.recipe12 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.MulDivCached.native.recipe12).baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate12
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing) data 3
    (row3_view.trans row3_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand13 : (Airbender.Compiler.HelperNative.MulDivCached.native.candidate13).check Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.MulDivCached.native.bank).check Airbender.Compiler.HelperNative.MulDivCached.native.recipe13 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.MulDivCached.native.recipe13).baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate13
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing) data 4
    (row4_view.trans row4_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand14 : (Airbender.Compiler.HelperNative.MulDivCached.native.candidate14).check Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.MulDivCached.native.bank).check Airbender.Compiler.HelperNative.MulDivCached.native.recipe14 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.MulDivCached.native.recipe14).baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate14
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing) data 5
    (row5_view.trans row5_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand15 : (Airbender.Compiler.HelperNative.MulDivCached.native.candidate15).check Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.MulDivCached.native.bank).check Airbender.Compiler.HelperNative.MulDivCached.native.recipe15 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.MulDivCached.native.recipe15).baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate15
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing) data 6
    (row6_view.trans row6_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand25 : (Airbender.Compiler.HelperNative.MulDivCached.native.candidate25).check Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.MulDivCached.native.bank).check Airbender.Compiler.HelperNative.MulDivCached.native.recipe25 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.MulDivCached.native.recipe25).baseCheck Airbender.Compiler.ConsumerNative.MulDivCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.MulDivCached.native.candidate25
  Airbender.Compiler.HelperNative.MulDivCached.native.placement Airbender.Compiler.MemoryNative.MulDivCached.native.bank
  Airbender.Compiler.ConsumerNative.MulDivCached.native.typing) data 7
    (row7_view.trans row7_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

end Airbender.Compiler.HelperPayloadChecks.MulDivCached
