import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.BlakeRoundCached.Bindings

namespace Airbender.Compiler.HelperPayloadChecks.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem operand0 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate0).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe0 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe0).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate0
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 0
    (row0_view.trans row0_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand2 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate2).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe2 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe2).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate2
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 1
    (row1_view.trans row1_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand3 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate3).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe3 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe3).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate3
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 2
    (row2_view.trans row2_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand4 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate4).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe4 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe4).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate4
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 3
    (row3_view.trans row3_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand5 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate5).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe5 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe5).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate5
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 4
    (row4_view.trans row4_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand6 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate6).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe6 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe6).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate6
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 5
    (row5_view.trans row5_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand7 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate7).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe7 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe7).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate7
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 6
    (row6_view.trans row6_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand8 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate8).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe8 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe8).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate8
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 7
    (row7_view.trans row7_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand9 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate9).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe9 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe9).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate9
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 8
    (row8_view.trans row8_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand10 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate10).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe10 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe10).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate10
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 9
    (row9_view.trans row9_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand11 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate11).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe11 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe11).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate11
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 10
    (row10_view.trans row10_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand12 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate12).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe12 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe12).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate12
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 11
    (row11_view.trans row11_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand13 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate13).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe13 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe13).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate13
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 12
    (row12_view.trans row12_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand14 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate14).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe14 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe14).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate14
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 13
    (row13_view.trans row13_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand15 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate15).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe15 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe15).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate15
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 14
    (row14_view.trans row14_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand16 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate16).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe16 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe16).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate16
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 15
    (row15_view.trans row15_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand17 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate17).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe17 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe17).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate17
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 16
    (row16_view.trans row16_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand18 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate18).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe18 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe18).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate18
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 17
    (row17_view.trans row17_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand19 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate19).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe19 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe19).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate19
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 18
    (row18_view.trans row18_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand20 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate20).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe20 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe20).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate20
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 19
    (row19_view.trans row19_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand21 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate21).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe21 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe21).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate21
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 20
    (row20_view.trans row20_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand22 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate22).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe22 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe22).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate22
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 21
    (row21_view.trans row21_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand23 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate23).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe23 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe23).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate23
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 22
    (row22_view.trans row22_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand24 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate24).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe24 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe24).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate24
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 23
    (row23_view.trans row23_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand25 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate25).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe25 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe25).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate25
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 24
    (row24_view.trans row24_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand26 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate26).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe26 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe26).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate26
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 25
    (row25_view.trans row25_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand27 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate27).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe27 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe27).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate27
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 26
    (row26_view.trans row26_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand28 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate28).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe28 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe28).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate28
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 27
    (row27_view.trans row27_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand29 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate29).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe29 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe29).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate29
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 28
    (row28_view.trans row28_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand30 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate30).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe30 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe30).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate30
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 29
    (row29_view.trans row29_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand31 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate31).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe31 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe31).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate31
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 30
    (row30_view.trans row30_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand32 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate32).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe32 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe32).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate32
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 31
    (row31_view.trans row31_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand33 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate33).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe33 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe33).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate33
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 32
    (row32_view.trans row32_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand34 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate34).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe34 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe34).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate34
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 33
    (row33_view.trans row33_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand35 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate35).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe35 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe35).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate35
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 34
    (row34_view.trans row34_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand36 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate36).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe36 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe36).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate36
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 35
    (row35_view.trans row35_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand37 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate37).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe37 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe37).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate37
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 36
    (row36_view.trans row36_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand38 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate38).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe38 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe38).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate38
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 37
    (row37_view.trans row37_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand39 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate39).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe39 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe39).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate39
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 38
    (row38_view.trans row38_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand40 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate40).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe40 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe40).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate40
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 39
    (row39_view.trans row39_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand41 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate41).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe41 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe41).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate41
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 40
    (row40_view.trans row40_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand42 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate42).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe42 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe42).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate42
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 41
    (row41_view.trans row41_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand43 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate43).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe43 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe43).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate43
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 42
    (row42_view.trans row42_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand44 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate44).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe44 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe44).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate44
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 43
    (row43_view.trans row43_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand45 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate45).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe45 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe45).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate45
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 44
    (row44_view.trans row44_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand46 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate46).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe46 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe46).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate46
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 45
    (row45_view.trans row45_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand47 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate47).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe47 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe47).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate47
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 46
    (row46_view.trans row46_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand48 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate48).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe48 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe48).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate48
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 47
    (row47_view.trans row47_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand49 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate49).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe49 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe49).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate49
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 48
    (row48_view.trans row48_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand50 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate50).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe50 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe50).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate50
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 49
    (row49_view.trans row49_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand51 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate51).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe51 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe51).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate51
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 50
    (row50_view.trans row50_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand52 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate52).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe52 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe52).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate52
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 51
    (row51_view.trans row51_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand53 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate53).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe53 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe53).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate53
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 52
    (row52_view.trans row52_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand54 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate54).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe54 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe54).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate54
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 53
    (row53_view.trans row53_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand55 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate55).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe55 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe55).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate55
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 54
    (row54_view.trans row54_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand56 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate56).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe56 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe56).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate56
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 55
    (row55_view.trans row55_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand57 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate57).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe57 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe57).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate57
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 56
    (row56_view.trans row56_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand58 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate58).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe58 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe58).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate58
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 57
    (row57_view.trans row57_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand59 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate59).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe59 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe59).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate59
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 58
    (row58_view.trans row58_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand60 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate60).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe60 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe60).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate60
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 59
    (row59_view.trans row59_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand61 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate61).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe61 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe61).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate61
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 60
    (row60_view.trans row60_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand62 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate62).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe62 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe62).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate62
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 61
    (row61_view.trans row61_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand63 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate63).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe63 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe63).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate63
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 62
    (row62_view.trans row62_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand64 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate64).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe64 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe64).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate64
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 63
    (row63_view.trans row63_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand65 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate65).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe65 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe65).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate65
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 64
    (row64_view.trans row64_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand66 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate66).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe66 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe66).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate66
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 65
    (row65_view.trans row65_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand67 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate67).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe67 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe67).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate67
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 66
    (row66_view.trans row66_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand68 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate68).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe68 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe68).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate68
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 67
    (row67_view.trans row67_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand69 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate69).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe69 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe69).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate69
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 68
    (row68_view.trans row68_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand70 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate70).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe70 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe70).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate70
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 69
    (row69_view.trans row69_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand71 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate71).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe71 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe71).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate71
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 70
    (row70_view.trans row70_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand72 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate72).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe72 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe72).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate72
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 71
    (row71_view.trans row71_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand73 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate73).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe73 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe73).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate73
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 72
    (row72_view.trans row72_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand74 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate74).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe74 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe74).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate74
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 73
    (row73_view.trans row73_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand75 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate75).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe75 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe75).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate75
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 74
    (row74_view.trans row74_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand76 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate76).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe76 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe76).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate76
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 75
    (row75_view.trans row75_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand77 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate77).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe77 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe77).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate77
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 76
    (row76_view.trans row76_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand78 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate78).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe78 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe78).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate78
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 77
    (row77_view.trans row77_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand79 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate79).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe79 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe79).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate79
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 78
    (row78_view.trans row78_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand80 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate80).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe80 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe80).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate80
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 79
    (row79_view.trans row79_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand81 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate81).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe81 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe81).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate81
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 80
    (row80_view.trans row80_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand82 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate82).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe82 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe82).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate82
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 81
    (row81_view.trans row81_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand83 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate83).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe83 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe83).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate83
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 82
    (row82_view.trans row82_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand84 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate84).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe84 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe84).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate84
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 83
    (row83_view.trans row83_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand85 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate85).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe85 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe85).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate85
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 84
    (row84_view.trans row84_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand86 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate86).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe86 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe86).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate86
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 85
    (row85_view.trans row85_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand87 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate87).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe87 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe87).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate87
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 86
    (row86_view.trans row86_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand88 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate88).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe88 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe88).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate88
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 87
    (row87_view.trans row87_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand89 : (Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate89).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank).check Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe89 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BlakeRoundCached.native.recipe89).baseCheck Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BlakeRoundCached.native.candidate89
  Airbender.Compiler.HelperNative.BlakeRoundCached.native.placement Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank
  Airbender.Compiler.ConsumerNative.BlakeRoundCached.native.typing) data 88
    (row88_view.trans row88_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

end Airbender.Compiler.HelperPayloadChecks.BlakeRoundCached
