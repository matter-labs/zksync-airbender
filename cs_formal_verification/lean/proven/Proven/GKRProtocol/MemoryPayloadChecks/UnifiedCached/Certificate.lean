module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.MemoryPayloadChecks.UnifiedCached.Bindings

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.MemoryPayloadChecks.UnifiedCached
open Airbender Airbender.Compiler
set_option maxRecDepth 8192

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem projection : Airbender.Compiler.MemoryNative.UnifiedCached.native.bank.inputCheck Airbender.Compiler.MemoryNative.UnifiedCached.native.projectionInputs = true ∧
    Airbender.Compiler.MemoryNative.UnifiedCached.native.projectionInputs.all (fun address => Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing Airbender.Compiler.MemoryNative.UnifiedCached.native.projectionInputs) data 0
    (row0_view.trans row0_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion0 : (LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [0] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf0).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [0] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf0).isSome)) data 1
    (row1_view.trans row1_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports0 : Airbender.Compiler.MemoryNative.UnifiedCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw0).inputs = true ∧
    (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw0).inputs.all (fun address => Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw0).inputs) data 2
    (row2_view.trans row2_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion1 : (LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [1] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf1).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [1] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf1).isSome)) data 3
    (row3_view.trans row3_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports1 : Airbender.Compiler.MemoryNative.UnifiedCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw1).inputs = true ∧
    (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw1).inputs.all (fun address => Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw1).inputs) data 4
    (row4_view.trans row4_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion2 : (LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [2] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf2).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [2] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf2).isSome)) data 5
    (row5_view.trans row5_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports2 : Airbender.Compiler.MemoryNative.UnifiedCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw2).inputs = true ∧
    (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw2).inputs.all (fun address => Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw2).inputs) data 6
    (row6_view.trans row6_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion3 : (LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [3] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf3).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [3] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf3).isSome)) data 7
    (row7_view.trans row7_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports3 : Airbender.Compiler.MemoryNative.UnifiedCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw3).inputs = true ∧
    (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw3).inputs.all (fun address => Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw3).inputs) data 8
    (row8_view.trans row8_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion4 : (LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [4] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf4).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [4] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf4).isSome)) data 9
    (row9_view.trans row9_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports4 : Airbender.Compiler.MemoryNative.UnifiedCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw4).inputs = true ∧
    (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw4).inputs.all (fun address => Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw4).inputs) data 10
    (row10_view.trans row10_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion5 : (LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [5] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf5).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [5] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf5).isSome)) data 11
    (row11_view.trans row11_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports5 : Airbender.Compiler.MemoryNative.UnifiedCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw5).inputs = true ∧
    (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw5).inputs.all (fun address => Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw5).inputs) data 12
    (row12_view.trans row12_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion6 : (LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [6] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf6).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [6] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf6).isSome)) data 13
    (row13_view.trans row13_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports6 : Airbender.Compiler.MemoryNative.UnifiedCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw6).inputs = true ∧
    (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw6).inputs.all (fun address => Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw6).inputs) data 14
    (row14_view.trans row14_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion7 : (LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [7] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf7).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [7] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf7).isSome)) data 15
    (row15_view.trans row15_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports7 : Airbender.Compiler.MemoryNative.UnifiedCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw7).inputs = true ∧
    (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw7).inputs.all (fun address => Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw7).inputs) data 16
    (row16_view.trans row16_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion8 : (LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf8).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf8).isSome)) data 17
    (row17_view.trans row17_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports8 : Airbender.Compiler.MemoryNative.UnifiedCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw8).inputs = true ∧
    (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw8).inputs.all (fun address => Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw8).inputs) data 18
    (row18_view.trans row18_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion9 : (LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf9).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf9).isSome)) data 19
    (row19_view.trans row19_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports9 : Airbender.Compiler.MemoryNative.UnifiedCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw9).inputs = true ∧
    (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw9).inputs.all (fun address => Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw9).inputs) data 20
    (row20_view.trans row20_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion10 : (LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf10).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf10).isSome)) data 21
    (row21_view.trans row21_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports10 : Airbender.Compiler.MemoryNative.UnifiedCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw10).inputs = true ∧
    (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw10).inputs.all (fun address => Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw10).inputs) data 22
    (row22_view.trans row22_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion11 : (LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf11).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.UnifiedCached.native.definitions [] Airbender.Compiler.MemoryNative.UnifiedCached.native.leaf11).isSome)) data 23
    (row23_view.trans row23_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports11 : Airbender.Compiler.MemoryNative.UnifiedCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw11).inputs = true ∧
    (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw11).inputs.all (fun address => Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing (Airbender.Compiler.MemoryNative.UnifiedCached.native.raw11).inputs) data 24
    (row24_view.trans row24_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem initializationReadFingerprint0 : Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationReadCertificate0.check
    (((Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw10 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationReadCertificate0 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw10 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing) data 25
    (row25_view.trans row25_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem initializationReadFingerprint1 : Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationReadCertificate1.check
    (((Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw11 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationReadCertificate1 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw11 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing) data 26
    (row26_view.trans row26_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem initializationWriteFingerprint0 : Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationWriteCertificate0.check
    (((Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw8 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationWriteCertificate0 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw8 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing) data 27
    (row27_view.trans row27_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem initializationWriteFingerprint1 : Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationWriteCertificate1.check
    (((Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw9 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationWriteCertificate1 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.initializationWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw9 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing) data 28
    (row28_view.trans row28_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint0 : Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadCertificate0.check
    (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw0 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadCertificate0 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw0 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing) data 29
    (row29_view.trans row29_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint1 : Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadCertificate1.check
    (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw1 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadCertificate1 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw1 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing) data 30
    (row30_view.trans row30_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint2 : Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadCertificate2.check
    (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw4 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadCertificate2 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw4 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing) data 31
    (row31_view.trans row31_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint3 : Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadCertificate3.check
    (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw5 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadCertificate3 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw5 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing) data 32
    (row32_view.trans row32_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadMask : (Airbender.Compiler.MemoryNative.UnifiedCached.native.bank.inputCheck [(GKRAddress.InnerLayer 2 0)] = true ∧
      Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing.compatible ((GKRAddress.InnerLayer 2 0), .base) = true) ∧
    Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadMaskField.check Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryReadMaskField Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing [(GKRAddress.InnerLayer 2 0)]) data 33
    (row33_view.trans row33_source) checked
  rw [NumericMemoryPayloadChecks.ofField_check] at valid
  simpa only [Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true] using valid

theorem memoryWriteFingerprint0 : Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteCertificate0.check
    (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw2 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteCertificate0 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw2 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing) data 34
    (row34_view.trans row34_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint1 : Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteCertificate1.check
    (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw3 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteCertificate1 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw3 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing) data 35
    (row35_view.trans row35_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint2 : Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteCertificate2.check
    (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw6 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteCertificate2 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw6 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing) data 36
    (row36_view.trans row36_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint3 : Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteCertificate3.check
    (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw7 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteCertificate3 (((Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.MemoryNative.UnifiedCached.native.raw7 Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing) data 37
    (row37_view.trans row37_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteMask : (Airbender.Compiler.MemoryNative.UnifiedCached.native.bank.inputCheck [(GKRAddress.InnerLayer 2 0)] = true ∧
      Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing.compatible ((GKRAddress.InnerLayer 2 0), .base) = true) ∧
    Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteMaskField.check Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.UnifiedCached.native.memoryWriteMaskField Airbender.Compiler.MemoryNative.UnifiedCached.native.sourcePlacement Airbender.Compiler.MemoryNative.UnifiedCached.native.bank Airbender.Compiler.ConsumerNative.UnifiedCached.native.typing [(GKRAddress.InnerLayer 2 0)]) data 38
    (row38_view.trans row38_source) checked
  rw [NumericMemoryPayloadChecks.ofField_check] at valid
  simpa only [Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true] using valid

end Airbender.Compiler.MemoryPayloadChecks.UnifiedCached
