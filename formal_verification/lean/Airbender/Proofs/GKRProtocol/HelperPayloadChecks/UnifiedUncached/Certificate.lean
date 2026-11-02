import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.UnifiedUncached.Bindings

namespace Airbender.Compiler.HelperPayloadChecks.UnifiedUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem operand12 : (Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate12).check Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank).check Airbender.Compiler.HelperNative.UnifiedUncached.native.recipe12 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.UnifiedUncached.native.recipe12).baseCheck Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate12
  Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing) data 0
    (row0_view.trans row0_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand14 : (Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate14).check Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank).check Airbender.Compiler.HelperNative.UnifiedUncached.native.recipe14 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.UnifiedUncached.native.recipe14).baseCheck Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate14
  Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing) data 1
    (row1_view.trans row1_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand15 : (Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate15).check Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank).check Airbender.Compiler.HelperNative.UnifiedUncached.native.recipe15 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.UnifiedUncached.native.recipe15).baseCheck Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate15
  Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing) data 2
    (row2_view.trans row2_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand16 : (Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate16).check Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank).check Airbender.Compiler.HelperNative.UnifiedUncached.native.recipe16 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.UnifiedUncached.native.recipe16).baseCheck Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate16
  Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing) data 3
    (row3_view.trans row3_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand17 : (Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate17).check Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank).check Airbender.Compiler.HelperNative.UnifiedUncached.native.recipe17 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.UnifiedUncached.native.recipe17).baseCheck Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate17
  Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing) data 4
    (row4_view.trans row4_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand18 : (Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate18).check Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank).check Airbender.Compiler.HelperNative.UnifiedUncached.native.recipe18 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.UnifiedUncached.native.recipe18).baseCheck Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate18
  Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing) data 5
    (row5_view.trans row5_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand19 : (Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate19).check Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank).check Airbender.Compiler.HelperNative.UnifiedUncached.native.recipe19 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.UnifiedUncached.native.recipe19).baseCheck Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate19
  Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing) data 6
    (row6_view.trans row6_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand24 : (Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate24).check Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank).check Airbender.Compiler.HelperNative.UnifiedUncached.native.recipe24 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.UnifiedUncached.native.recipe24).baseCheck Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedUncached.native.candidate24
  Airbender.Compiler.HelperNative.UnifiedUncached.native.placement Airbender.Compiler.MemoryNative.UnifiedUncached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedUncached.native.typing) data 7
    (row7_view.trans row7_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

end Airbender.Compiler.HelperPayloadChecks.UnifiedUncached
