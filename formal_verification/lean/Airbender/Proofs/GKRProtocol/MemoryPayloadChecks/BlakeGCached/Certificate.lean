import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.BlakeGCached.Bindings

namespace Airbender.Compiler.MemoryPayloadChecks.BlakeGCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem projection : Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.inputCheck Airbender.Compiler.MemoryNative.BlakeGCached.native.projectionInputs = true ∧
    Airbender.Compiler.MemoryNative.BlakeGCached.native.projectionInputs.all (fun address => Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing Airbender.Compiler.MemoryNative.BlakeGCached.native.projectionInputs) data 0
    (row0_view.trans row0_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion0 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [0] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf0).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [0] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf0).isSome)) data 1
    (row1_view.trans row1_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports0 : Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw0).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw0).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw0).inputs) data 2
    (row2_view.trans row2_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion1 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [1] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf1).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [1] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf1).isSome)) data 3
    (row3_view.trans row3_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports1 : Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw1).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw1).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw1).inputs) data 4
    (row4_view.trans row4_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion2 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [2] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf2).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [2] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf2).isSome)) data 5
    (row5_view.trans row5_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports2 : Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw2).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw2).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw2).inputs) data 6
    (row6_view.trans row6_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion3 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [3] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf3).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [3] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf3).isSome)) data 7
    (row7_view.trans row7_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports3 : Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw3).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw3).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw3).inputs) data 8
    (row8_view.trans row8_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion4 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [4] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf4).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [4] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf4).isSome)) data 9
    (row9_view.trans row9_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports4 : Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw4).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw4).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw4).inputs) data 10
    (row10_view.trans row10_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion5 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [5] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf5).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [5] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf5).isSome)) data 11
    (row11_view.trans row11_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports5 : Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw5).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw5).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw5).inputs) data 12
    (row12_view.trans row12_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion6 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [6] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf6).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [6] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf6).isSome)) data 13
    (row13_view.trans row13_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports6 : Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw6).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw6).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw6).inputs) data 14
    (row14_view.trans row14_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion7 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [7] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf7).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [7] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf7).isSome)) data 15
    (row15_view.trans row15_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports7 : Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw7).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw7).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw7).inputs) data 16
    (row16_view.trans row16_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion8 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [8] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf8).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [8] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf8).isSome)) data 17
    (row17_view.trans row17_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports8 : Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw8).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw8).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw8).inputs) data 18
    (row18_view.trans row18_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion9 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [9] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf9).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [9] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf9).isSome)) data 19
    (row19_view.trans row19_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports9 : Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw9).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw9).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw9).inputs) data 20
    (row20_view.trans row20_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion10 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [10] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf10).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [10] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf10).isSome)) data 21
    (row21_view.trans row21_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports10 : Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw10).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw10).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw10).inputs) data 22
    (row22_view.trans row22_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion11 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [11] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf11).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [11] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf11).isSome)) data 23
    (row23_view.trans row23_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports11 : Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw11).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw11).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw11).inputs) data 24
    (row24_view.trans row24_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion12 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [12] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf12).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [12] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf12).isSome)) data 25
    (row25_view.trans row25_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports12 : Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw12).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw12).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw12).inputs) data 26
    (row26_view.trans row26_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion13 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [13] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf13).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [13] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf13).isSome)) data 27
    (row27_view.trans row27_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports13 : Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw13).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw13).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw13).inputs) data 28
    (row28_view.trans row28_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion14 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [14] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf14).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [14] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf14).isSome)) data 29
    (row29_view.trans row29_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports14 : Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw14).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw14).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw14).inputs) data 30
    (row30_view.trans row30_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion15 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [15] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf15).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [15] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf15).isSome)) data 31
    (row31_view.trans row31_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports15 : Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw15).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw15).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw15).inputs) data 32
    (row32_view.trans row32_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion16 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [16] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf16).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [16] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf16).isSome)) data 33
    (row33_view.trans row33_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports16 : Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw16).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw16).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw16).inputs) data 34
    (row34_view.trans row34_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion17 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [17] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf17).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [17] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf17).isSome)) data 35
    (row35_view.trans row35_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports17 : Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw17).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw17).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw17).inputs) data 36
    (row36_view.trans row36_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion18 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [18] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf18).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [18] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf18).isSome)) data 37
    (row37_view.trans row37_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports18 : Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw18).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw18).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw18).inputs) data 38
    (row38_view.trans row38_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion19 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [19] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf19).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BlakeGCached.native.definitions [19] Airbender.Compiler.MemoryNative.BlakeGCached.native.leaf19).isSome)) data 39
    (row39_view.trans row39_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports19 : Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw19).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw19).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing (Airbender.Compiler.MemoryNative.BlakeGCached.native.raw19).inputs) data 40
    (row40_view.trans row40_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem memoryReadFingerprint0 : Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadCertificate0.check
    (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw0 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadCertificate0 (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw0 Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing) data 41
    (row41_view.trans row41_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint1 : Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadCertificate1.check
    (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw1 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadCertificate1 (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw1 Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing) data 42
    (row42_view.trans row42_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint2 : Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadCertificate2.check
    (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw4 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadCertificate2 (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw4 Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing) data 43
    (row43_view.trans row43_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint3 : Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadCertificate3.check
    (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw5 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadCertificate3 (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw5 Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing) data 44
    (row44_view.trans row44_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint4 : Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadCertificate4.check
    (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadRows)[4]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw8 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadCertificate4 (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadRows)[4]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw8 Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing) data 45
    (row45_view.trans row45_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint5 : Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadCertificate5.check
    (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadRows)[5]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw9 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadCertificate5 (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadRows)[5]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw9 Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing) data 46
    (row46_view.trans row46_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint6 : Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadCertificate6.check
    (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadRows)[6]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw12 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadCertificate6 (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadRows)[6]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw12 Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing) data 47
    (row47_view.trans row47_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint7 : Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadCertificate7.check
    (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadRows)[7]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw13 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadCertificate7 (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadRows)[7]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw13 Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing) data 48
    (row48_view.trans row48_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint8 : Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadCertificate8.check
    (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadRows)[8]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw16 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadCertificate8 (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadRows)[8]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw16 Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing) data 49
    (row49_view.trans row49_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint9 : Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadCertificate9.check
    (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadRows)[9]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw17 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadCertificate9 (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadRows)[9]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw17 Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing) data 50
    (row50_view.trans row50_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadMask : (Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.inputCheck [(GKRAddress.InnerLayer 4 0)] = true ∧
      Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing.compatible ((GKRAddress.InnerLayer 4 0), .base) = true) ∧
    Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadMaskField.check Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryReadMaskField Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing [(GKRAddress.InnerLayer 4 0)]) data 51
    (row51_view.trans row51_source) checked
  rw [NumericMemoryPayloadChecks.ofField_check] at valid
  simpa only [Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true] using valid

theorem memoryWriteFingerprint0 : Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteCertificate0.check
    (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw2 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteCertificate0 (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw2 Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing) data 52
    (row52_view.trans row52_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint1 : Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteCertificate1.check
    (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw3 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteCertificate1 (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw3 Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing) data 53
    (row53_view.trans row53_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint2 : Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteCertificate2.check
    (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw6 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteCertificate2 (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw6 Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing) data 54
    (row54_view.trans row54_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint3 : Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteCertificate3.check
    (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw7 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteCertificate3 (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw7 Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing) data 55
    (row55_view.trans row55_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint4 : Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteCertificate4.check
    (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteRows)[4]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw10 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteCertificate4 (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteRows)[4]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw10 Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing) data 56
    (row56_view.trans row56_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint5 : Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteCertificate5.check
    (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteRows)[5]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw11 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteCertificate5 (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteRows)[5]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw11 Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing) data 57
    (row57_view.trans row57_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint6 : Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteCertificate6.check
    (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteRows)[6]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw14 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteCertificate6 (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteRows)[6]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw14 Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing) data 58
    (row58_view.trans row58_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint7 : Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteCertificate7.check
    (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteRows)[7]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw15 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteCertificate7 (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteRows)[7]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw15 Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing) data 59
    (row59_view.trans row59_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint8 : Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteCertificate8.check
    (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteRows)[8]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw18 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteCertificate8 (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteRows)[8]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw18 Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing) data 60
    (row60_view.trans row60_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint9 : Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteCertificate9.check
    (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteRows)[9]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw19 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteCertificate9 (((Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteRows)[9]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.MemoryNative.BlakeGCached.native.raw19 Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing) data 61
    (row61_view.trans row61_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteMask : (Airbender.Compiler.MemoryNative.BlakeGCached.native.bank.inputCheck [(GKRAddress.InnerLayer 4 0)] = true ∧
      Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing.compatible ((GKRAddress.InnerLayer 4 0), .base) = true) ∧
    Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteMaskField.check Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.BlakeGCached.native.memoryWriteMaskField Airbender.Compiler.MemoryNative.BlakeGCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BlakeGCached.native.bank Airbender.Compiler.ConsumerNative.BlakeGCached.native.typing [(GKRAddress.InnerLayer 4 0)]) data 62
    (row62_view.trans row62_source) checked
  rw [NumericMemoryPayloadChecks.ofField_check] at valid
  simpa only [Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true] using valid

end Airbender.Compiler.MemoryPayloadChecks.BlakeGCached
