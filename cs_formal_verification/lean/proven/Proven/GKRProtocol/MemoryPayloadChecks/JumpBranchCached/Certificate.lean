module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.MemoryPayloadChecks.JumpBranchCached.Bindings

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.MemoryPayloadChecks.JumpBranchCached
open Airbender Airbender.Compiler
set_option maxRecDepth 8192

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem projection : Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank.inputCheck Airbender.Compiler.MemoryNative.JumpBranchCached.native.projectionInputs = true ∧
    Airbender.Compiler.MemoryNative.JumpBranchCached.native.projectionInputs.all (fun address => Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing Airbender.Compiler.MemoryNative.JumpBranchCached.native.projectionInputs) data 0
    (row0_view.trans row0_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion0 : (LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchCached.native.definitions [0] Airbender.Compiler.MemoryNative.JumpBranchCached.native.leaf0).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchCached.native.definitions [0] Airbender.Compiler.MemoryNative.JumpBranchCached.native.leaf0).isSome)) data 1
    (row1_view.trans row1_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports0 : Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw0).inputs = true ∧
    (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw0).inputs.all (fun address => Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw0).inputs) data 2
    (row2_view.trans row2_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion1 : (LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchCached.native.definitions [1] Airbender.Compiler.MemoryNative.JumpBranchCached.native.leaf1).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchCached.native.definitions [1] Airbender.Compiler.MemoryNative.JumpBranchCached.native.leaf1).isSome)) data 3
    (row3_view.trans row3_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports1 : Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw1).inputs = true ∧
    (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw1).inputs.all (fun address => Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw1).inputs) data 4
    (row4_view.trans row4_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion2 : (LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchCached.native.definitions [2] Airbender.Compiler.MemoryNative.JumpBranchCached.native.leaf2).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchCached.native.definitions [2] Airbender.Compiler.MemoryNative.JumpBranchCached.native.leaf2).isSome)) data 5
    (row5_view.trans row5_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports2 : Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw2).inputs = true ∧
    (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw2).inputs.all (fun address => Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw2).inputs) data 6
    (row6_view.trans row6_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion3 : (LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchCached.native.definitions [3] Airbender.Compiler.MemoryNative.JumpBranchCached.native.leaf3).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchCached.native.definitions [3] Airbender.Compiler.MemoryNative.JumpBranchCached.native.leaf3).isSome)) data 7
    (row7_view.trans row7_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports3 : Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw3).inputs = true ∧
    (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw3).inputs.all (fun address => Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw3).inputs) data 8
    (row8_view.trans row8_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion4 : (LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchCached.native.definitions [4] Airbender.Compiler.MemoryNative.JumpBranchCached.native.leaf4).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchCached.native.definitions [4] Airbender.Compiler.MemoryNative.JumpBranchCached.native.leaf4).isSome)) data 9
    (row9_view.trans row9_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports4 : Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw4).inputs = true ∧
    (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw4).inputs.all (fun address => Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw4).inputs) data 10
    (row10_view.trans row10_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion5 : (LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchCached.native.definitions [5] Airbender.Compiler.MemoryNative.JumpBranchCached.native.leaf5).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchCached.native.definitions [5] Airbender.Compiler.MemoryNative.JumpBranchCached.native.leaf5).isSome)) data 11
    (row11_view.trans row11_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports5 : Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw5).inputs = true ∧
    (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw5).inputs.all (fun address => Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw5).inputs) data 12
    (row12_view.trans row12_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion6 : (LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchCached.native.definitions [6] Airbender.Compiler.MemoryNative.JumpBranchCached.native.leaf6).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchCached.native.definitions [6] Airbender.Compiler.MemoryNative.JumpBranchCached.native.leaf6).isSome)) data 13
    (row13_view.trans row13_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports6 : Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw6).inputs = true ∧
    (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw6).inputs.all (fun address => Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw6).inputs) data 14
    (row14_view.trans row14_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion7 : (LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchCached.native.definitions [7] Airbender.Compiler.MemoryNative.JumpBranchCached.native.leaf7).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.JumpBranchCached.native.definitions [7] Airbender.Compiler.MemoryNative.JumpBranchCached.native.leaf7).isSome)) data 15
    (row15_view.trans row15_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports7 : Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw7).inputs = true ∧
    (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw7).inputs.all (fun address => Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing (Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw7).inputs) data 16
    (row16_view.trans row16_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem memoryReadFingerprint0 : Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryReadCertificate0.check
    (((Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw0 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryReadCertificate0 (((Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw0 Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing) data 17
    (row17_view.trans row17_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint1 : Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryReadCertificate1.check
    (((Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw1 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryReadCertificate1 (((Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw1 Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing) data 18
    (row18_view.trans row18_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint2 : Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryReadCertificate2.check
    (((Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryReadRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw4 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryReadCertificate2 (((Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryReadRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw4 Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing) data 19
    (row19_view.trans row19_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint3 : Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryReadCertificate3.check
    (((Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryReadRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw5 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryReadCertificate3 (((Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryReadRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw5 Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing) data 20
    (row20_view.trans row20_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadMask : (Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank.inputCheck [(GKRAddress.InnerLayer 2 0)] = true ∧
      Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing.compatible ((GKRAddress.InnerLayer 2 0), .base) = true) ∧
    Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryReadMaskField.check Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryReadMaskField Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing [(GKRAddress.InnerLayer 2 0)]) data 21
    (row21_view.trans row21_source) checked
  rw [NumericMemoryPayloadChecks.ofField_check] at valid
  simpa only [Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true] using valid

theorem memoryWriteFingerprint0 : Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryWriteCertificate0.check
    (((Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw2 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryWriteCertificate0 (((Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw2 Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing) data 22
    (row22_view.trans row22_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint1 : Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryWriteCertificate1.check
    (((Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw3 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryWriteCertificate1 (((Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw3 Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing) data 23
    (row23_view.trans row23_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint2 : Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryWriteCertificate2.check
    (((Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryWriteRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw6 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryWriteCertificate2 (((Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryWriteRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw6 Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing) data 24
    (row24_view.trans row24_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint3 : Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryWriteCertificate3.check
    (((Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryWriteRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw7 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryWriteCertificate3 (((Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryWriteRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.MemoryNative.JumpBranchCached.native.raw7 Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing) data 25
    (row25_view.trans row25_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteMask : (Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank.inputCheck [(GKRAddress.InnerLayer 2 0)] = true ∧
      Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing.compatible ((GKRAddress.InnerLayer 2 0), .base) = true) ∧
    Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryWriteMaskField.check Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.JumpBranchCached.native.memoryWriteMaskField Airbender.Compiler.MemoryNative.JumpBranchCached.native.sourcePlacement Airbender.Compiler.MemoryNative.JumpBranchCached.native.bank Airbender.Compiler.ConsumerNative.JumpBranchCached.native.typing [(GKRAddress.InnerLayer 2 0)]) data 26
    (row26_view.trans row26_source) checked
  rw [NumericMemoryPayloadChecks.ofField_check] at valid
  simpa only [Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true] using valid

end Airbender.Compiler.MemoryPayloadChecks.JumpBranchCached
