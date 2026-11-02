import Airbender.Proofs.GKRProtocol.HelperPayloadChecks.BigintUncached.Bindings

namespace Airbender.Compiler.HelperPayloadChecks.BigintUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem operand16 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate16).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe16 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe16).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate16
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 0
    (row0_view.trans row0_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand18 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate18).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe18 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe18).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate18
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 1
    (row1_view.trans row1_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand19 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate19).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe19 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe19).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate19
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 2
    (row2_view.trans row2_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand20 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate20).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe20 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe20).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate20
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 3
    (row3_view.trans row3_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand21 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate21).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe21 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe21).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate21
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 4
    (row4_view.trans row4_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand22 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate22).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe22 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe22).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate22
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 5
    (row5_view.trans row5_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand23 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate23).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe23 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe23).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate23
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 6
    (row6_view.trans row6_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand24 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate24).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe24 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe24).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate24
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 7
    (row7_view.trans row7_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand25 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate25).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe25 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe25).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate25
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 8
    (row8_view.trans row8_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand26 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate26).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe26 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe26).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate26
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 9
    (row9_view.trans row9_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand27 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate27).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe27 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe27).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate27
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 10
    (row10_view.trans row10_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand28 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate28).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe28 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe28).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate28
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 11
    (row11_view.trans row11_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand29 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate29).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe29 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe29).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate29
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 12
    (row12_view.trans row12_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand30 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate30).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe30 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe30).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate30
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 13
    (row13_view.trans row13_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand31 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate31).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe31 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe31).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate31
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 14
    (row14_view.trans row14_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand32 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate32).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe32 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe32).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate32
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 15
    (row15_view.trans row15_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand33 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate33).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe33 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe33).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate33
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 16
    (row16_view.trans row16_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand34 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate34).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe34 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe34).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate34
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 17
    (row17_view.trans row17_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand35 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate35).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe35 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe35).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate35
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 18
    (row18_view.trans row18_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand36 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate36).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe36 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe36).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate36
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 19
    (row19_view.trans row19_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand37 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate37).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe37 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe37).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate37
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 20
    (row20_view.trans row20_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand38 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate38).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe38 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe38).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate38
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 21
    (row21_view.trans row21_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand39 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate39).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe39 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe39).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate39
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 22
    (row22_view.trans row22_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand40 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate40).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe40 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe40).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate40
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 23
    (row23_view.trans row23_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand41 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate41).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe41 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe41).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate41
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 24
    (row24_view.trans row24_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand42 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate42).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe42 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe42).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate42
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 25
    (row25_view.trans row25_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand43 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate43).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe43 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe43).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate43
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 26
    (row26_view.trans row26_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand44 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate44).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe44 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe44).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate44
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 27
    (row27_view.trans row27_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand45 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate45).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe45 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe45).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate45
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 28
    (row28_view.trans row28_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand46 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate46).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe46 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe46).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate46
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 29
    (row29_view.trans row29_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand47 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate47).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe47 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe47).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate47
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 30
    (row30_view.trans row30_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand48 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate48).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe48 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe48).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate48
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 31
    (row31_view.trans row31_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand49 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate49).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe49 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe49).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate49
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 32
    (row32_view.trans row32_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand50 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate50).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe50 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe50).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate50
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 33
    (row33_view.trans row33_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand51 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate51).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe51 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe51).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate51
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 34
    (row34_view.trans row34_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand52 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate52).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe52 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe52).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate52
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 35
    (row35_view.trans row35_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand53 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate53).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe53 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe53).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate53
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 36
    (row36_view.trans row36_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand54 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate54).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe54 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe54).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate54
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 37
    (row37_view.trans row37_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand55 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate55).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe55 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe55).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate55
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 38
    (row38_view.trans row38_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand56 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate56).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe56 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe56).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate56
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 39
    (row39_view.trans row39_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

theorem operand57 : (Airbender.Compiler.HelperNative.BigintUncached.native.candidate57).check Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank = true ∧
    (Airbender.Compiler.MemoryNative.BigintUncached.native.bank).check Airbender.Compiler.HelperNative.BigintUncached.native.recipe57 = true ∧
    (NativeLookupEncoding.scalar Airbender.Compiler.HelperNative.BigintUncached.native.recipe57).baseCheck Airbender.Compiler.ConsumerNative.BigintUncached.native.typing = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofHelper Airbender.Compiler.HelperNative.BigintUncached.native.candidate57
  Airbender.Compiler.HelperNative.BigintUncached.native.placement Airbender.Compiler.MemoryNative.BigintUncached.native.bank
  Airbender.Compiler.ConsumerNative.BigintUncached.native.typing) data 40
    (row40_view.trans row40_source) checked
  rw [NumericNativePayloadChecks.ofHelper_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact ⟨valid.2, valid.1.1, valid.1.2⟩

end Airbender.Compiler.HelperPayloadChecks.BigintUncached
