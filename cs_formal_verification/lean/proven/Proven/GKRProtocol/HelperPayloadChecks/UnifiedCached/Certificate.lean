module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.HelperPayloadChecks.UnifiedCached.Bindings

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.HelperPayloadChecks.UnifiedCached
open Airbender Airbender.Compiler
set_option maxRecDepth 8192

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem operand12 : (Airbender.Compiler.HelperNative.UnifiedCached.native.candidate12).check Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.UnifiedCached.native.bank).check Airbender.Compiler.HelperNative.UnifiedCached.native.recipe12 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.UnifiedCached.native.recipe12).baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedCached.native.candidate12
  Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing) data 0
    (row0_view.trans row0_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand14 : (Airbender.Compiler.HelperNative.UnifiedCached.native.candidate14).check Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.UnifiedCached.native.bank).check Airbender.Compiler.HelperNative.UnifiedCached.native.recipe14 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.UnifiedCached.native.recipe14).baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedCached.native.candidate14
  Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing) data 1
    (row1_view.trans row1_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand15 : (Airbender.Compiler.HelperNative.UnifiedCached.native.candidate15).check Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.UnifiedCached.native.bank).check Airbender.Compiler.HelperNative.UnifiedCached.native.recipe15 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.UnifiedCached.native.recipe15).baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedCached.native.candidate15
  Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing) data 2
    (row2_view.trans row2_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand16 : (Airbender.Compiler.HelperNative.UnifiedCached.native.candidate16).check Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.UnifiedCached.native.bank).check Airbender.Compiler.HelperNative.UnifiedCached.native.recipe16 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.UnifiedCached.native.recipe16).baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedCached.native.candidate16
  Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing) data 3
    (row3_view.trans row3_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand17 : (Airbender.Compiler.HelperNative.UnifiedCached.native.candidate17).check Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.UnifiedCached.native.bank).check Airbender.Compiler.HelperNative.UnifiedCached.native.recipe17 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.UnifiedCached.native.recipe17).baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedCached.native.candidate17
  Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing) data 4
    (row4_view.trans row4_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand18 : (Airbender.Compiler.HelperNative.UnifiedCached.native.candidate18).check Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.UnifiedCached.native.bank).check Airbender.Compiler.HelperNative.UnifiedCached.native.recipe18 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.UnifiedCached.native.recipe18).baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedCached.native.candidate18
  Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing) data 5
    (row5_view.trans row5_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand19 : (Airbender.Compiler.HelperNative.UnifiedCached.native.candidate19).check Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.UnifiedCached.native.bank).check Airbender.Compiler.HelperNative.UnifiedCached.native.recipe19 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.UnifiedCached.native.recipe19).baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedCached.native.candidate19
  Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing) data 6
    (row6_view.trans row6_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand24 : (Airbender.Compiler.HelperNative.UnifiedCached.native.candidate24).check Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.UnifiedCached.native.bank).check Airbender.Compiler.HelperNative.UnifiedCached.native.recipe24 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.UnifiedCached.native.recipe24).baseCheck Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.UnifiedCached.native.candidate24
  Airbender.Compiler.HelperNative.UnifiedCached.native.placement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank
  Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing) data 7
    (row7_view.trans row7_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

end Airbender.Compiler.HelperPayloadChecks.UnifiedCached
