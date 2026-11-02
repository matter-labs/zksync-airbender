import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.BlakeGUncached.Bindings

namespace Airbender.Compiler.HelperPayloadChecks.BlakeGUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem operand0 : (Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate0).check Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank).check Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe0 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe0).baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate0
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing) data 0
    (row0_view.trans row0_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand2 : (Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate2).check Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank).check Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe2 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe2).baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate2
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing) data 1
    (row1_view.trans row1_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand3 : (Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate3).check Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank).check Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe3 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe3).baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate3
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing) data 2
    (row2_view.trans row2_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand4 : (Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate4).check Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank).check Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe4 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe4).baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate4
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing) data 3
    (row3_view.trans row3_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand5 : (Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate5).check Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank).check Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe5 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe5).baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate5
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing) data 4
    (row4_view.trans row4_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand6 : (Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate6).check Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank).check Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe6 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe6).baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate6
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing) data 5
    (row5_view.trans row5_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand7 : (Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate7).check Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank).check Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe7 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe7).baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate7
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing) data 6
    (row6_view.trans row6_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand8 : (Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate8).check Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank).check Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe8 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe8).baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate8
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing) data 7
    (row7_view.trans row7_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand9 : (Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate9).check Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank).check Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe9 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe9).baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate9
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing) data 8
    (row8_view.trans row8_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand10 : (Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate10).check Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank).check Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe10 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe10).baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate10
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing) data 9
    (row9_view.trans row9_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand11 : (Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate11).check Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank).check Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe11 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe11).baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate11
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing) data 10
    (row10_view.trans row10_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand12 : (Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate12).check Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank).check Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe12 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe12).baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate12
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing) data 11
    (row11_view.trans row11_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand13 : (Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate13).check Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank).check Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe13 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe13).baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate13
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing) data 12
    (row12_view.trans row12_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand14 : (Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate14).check Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank).check Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe14 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe14).baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate14
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing) data 13
    (row13_view.trans row13_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand15 : (Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate15).check Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank).check Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe15 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe15).baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate15
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing) data 14
    (row14_view.trans row14_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand16 : (Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate16).check Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank).check Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe16 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe16).baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate16
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing) data 15
    (row15_view.trans row15_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand17 : (Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate17).check Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank).check Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe17 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe17).baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate17
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing) data 16
    (row16_view.trans row16_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand18 : (Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate18).check Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank).check Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe18 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe18).baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate18
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing) data 17
    (row17_view.trans row17_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand19 : (Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate19).check Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank).check Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe19 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe19).baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate19
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing) data 18
    (row18_view.trans row18_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand20 : (Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate20).check Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank).check Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe20 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe20).baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate20
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing) data 19
    (row19_view.trans row19_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand21 : (Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate21).check Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank).check Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe21 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeGUncached.native.recipe21).baseCheck Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeGUncached.native.candidate21
  Airbender.Compiler.HelperNative.BlakeGUncached.native.placement Airbender.Compiler.MemoryNative.BlakeGUncached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeGUncached.native.typing) data 20
    (row20_view.trans row20_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

end Airbender.Compiler.HelperPayloadChecks.BlakeGUncached
