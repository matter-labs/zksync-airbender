module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.HelperPayloadChecks.JumpBranchCached.Bindings

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.HelperPayloadChecks.JumpBranchCached
open Airbender Airbender.Compiler
set_option maxRecDepth 8192

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem operand4 : (Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate4).check Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank).check Airbender.Compiler.HelperNative.JumpBranchCached.native.recipe4 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.JumpBranchCached.native.recipe4).baseCheck Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate4
  Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing) data 0
    (row0_view.trans row0_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand6 : (Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate6).check Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank).check Airbender.Compiler.HelperNative.JumpBranchCached.native.recipe6 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.JumpBranchCached.native.recipe6).baseCheck Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate6
  Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing) data 1
    (row1_view.trans row1_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand7 : (Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate7).check Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank).check Airbender.Compiler.HelperNative.JumpBranchCached.native.recipe7 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.JumpBranchCached.native.recipe7).baseCheck Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate7
  Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing) data 2
    (row2_view.trans row2_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand8 : (Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate8).check Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank).check Airbender.Compiler.HelperNative.JumpBranchCached.native.recipe8 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.JumpBranchCached.native.recipe8).baseCheck Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate8
  Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing) data 3
    (row3_view.trans row3_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand9 : (Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate9).check Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank).check Airbender.Compiler.HelperNative.JumpBranchCached.native.recipe9 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.JumpBranchCached.native.recipe9).baseCheck Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate9
  Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing) data 4
    (row4_view.trans row4_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand10 : (Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate10).check Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank).check Airbender.Compiler.HelperNative.JumpBranchCached.native.recipe10 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.JumpBranchCached.native.recipe10).baseCheck Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate10
  Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing) data 5
    (row5_view.trans row5_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand11 : (Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate11).check Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank).check Airbender.Compiler.HelperNative.JumpBranchCached.native.recipe11 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.JumpBranchCached.native.recipe11).baseCheck Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate11
  Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing) data 6
    (row6_view.trans row6_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand19 : (Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate19).check Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank).check Airbender.Compiler.HelperNative.JumpBranchCached.native.recipe19 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.JumpBranchCached.native.recipe19).baseCheck Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.JumpBranchCached.native.candidate19
  Airbender.Compiler.HelperNative.JumpBranchCached.native.placement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank
  Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing) data 7
    (row7_view.trans row7_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

end Airbender.Compiler.HelperPayloadChecks.JumpBranchCached
