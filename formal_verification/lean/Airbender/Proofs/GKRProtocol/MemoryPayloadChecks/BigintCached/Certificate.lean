import Airbender.Proofs.GKRProtocol.MemoryPayloadChecks.BigintCached.Bindings

namespace Airbender.Compiler.MemoryPayloadChecks.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericFunctionalBaseChecks.check babyBearModulus data = true := by decide +kernel

theorem projection : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck Airbender.Compiler.MemoryNative.BigintCached.native.projectionInputs = true ∧
    Airbender.Compiler.MemoryNative.BigintCached.native.projectionInputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing Airbender.Compiler.MemoryNative.BigintCached.native.projectionInputs) data 0
    (row0_view.trans row0_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion0 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [0] Airbender.Compiler.MemoryNative.BigintCached.native.leaf0).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [0] Airbender.Compiler.MemoryNative.BigintCached.native.leaf0).isSome)) data 1
    (row1_view.trans row1_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports0 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw0).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw0).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw0).inputs) data 2
    (row2_view.trans row2_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion1 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [1] Airbender.Compiler.MemoryNative.BigintCached.native.leaf1).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [1] Airbender.Compiler.MemoryNative.BigintCached.native.leaf1).isSome)) data 3
    (row3_view.trans row3_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports1 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw1).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw1).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw1).inputs) data 4
    (row4_view.trans row4_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion2 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [2] Airbender.Compiler.MemoryNative.BigintCached.native.leaf2).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [2] Airbender.Compiler.MemoryNative.BigintCached.native.leaf2).isSome)) data 5
    (row5_view.trans row5_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports2 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw2).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw2).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw2).inputs) data 6
    (row6_view.trans row6_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion3 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [3] Airbender.Compiler.MemoryNative.BigintCached.native.leaf3).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [3] Airbender.Compiler.MemoryNative.BigintCached.native.leaf3).isSome)) data 7
    (row7_view.trans row7_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports3 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw3).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw3).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw3).inputs) data 8
    (row8_view.trans row8_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion4 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [4] Airbender.Compiler.MemoryNative.BigintCached.native.leaf4).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [4] Airbender.Compiler.MemoryNative.BigintCached.native.leaf4).isSome)) data 9
    (row9_view.trans row9_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports4 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw4).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw4).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw4).inputs) data 10
    (row10_view.trans row10_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion5 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [5] Airbender.Compiler.MemoryNative.BigintCached.native.leaf5).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [5] Airbender.Compiler.MemoryNative.BigintCached.native.leaf5).isSome)) data 11
    (row11_view.trans row11_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports5 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw5).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw5).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw5).inputs) data 12
    (row12_view.trans row12_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion6 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [6] Airbender.Compiler.MemoryNative.BigintCached.native.leaf6).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [6] Airbender.Compiler.MemoryNative.BigintCached.native.leaf6).isSome)) data 13
    (row13_view.trans row13_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports6 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw6).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw6).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw6).inputs) data 14
    (row14_view.trans row14_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion7 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [7] Airbender.Compiler.MemoryNative.BigintCached.native.leaf7).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [7] Airbender.Compiler.MemoryNative.BigintCached.native.leaf7).isSome)) data 15
    (row15_view.trans row15_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports7 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw7).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw7).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw7).inputs) data 16
    (row16_view.trans row16_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion8 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [8] Airbender.Compiler.MemoryNative.BigintCached.native.leaf8).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [8] Airbender.Compiler.MemoryNative.BigintCached.native.leaf8).isSome)) data 17
    (row17_view.trans row17_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports8 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw8).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw8).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw8).inputs) data 18
    (row18_view.trans row18_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion9 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [9] Airbender.Compiler.MemoryNative.BigintCached.native.leaf9).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [9] Airbender.Compiler.MemoryNative.BigintCached.native.leaf9).isSome)) data 19
    (row19_view.trans row19_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports9 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw9).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw9).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw9).inputs) data 20
    (row20_view.trans row20_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion10 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [10] Airbender.Compiler.MemoryNative.BigintCached.native.leaf10).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [10] Airbender.Compiler.MemoryNative.BigintCached.native.leaf10).isSome)) data 21
    (row21_view.trans row21_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports10 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw10).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw10).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw10).inputs) data 22
    (row22_view.trans row22_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion11 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [11] Airbender.Compiler.MemoryNative.BigintCached.native.leaf11).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [11] Airbender.Compiler.MemoryNative.BigintCached.native.leaf11).isSome)) data 23
    (row23_view.trans row23_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports11 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw11).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw11).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw11).inputs) data 24
    (row24_view.trans row24_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion12 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [12] Airbender.Compiler.MemoryNative.BigintCached.native.leaf12).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [12] Airbender.Compiler.MemoryNative.BigintCached.native.leaf12).isSome)) data 25
    (row25_view.trans row25_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports12 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw12).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw12).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw12).inputs) data 26
    (row26_view.trans row26_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion13 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [13] Airbender.Compiler.MemoryNative.BigintCached.native.leaf13).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [13] Airbender.Compiler.MemoryNative.BigintCached.native.leaf13).isSome)) data 27
    (row27_view.trans row27_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports13 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw13).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw13).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw13).inputs) data 28
    (row28_view.trans row28_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion14 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [14] Airbender.Compiler.MemoryNative.BigintCached.native.leaf14).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [14] Airbender.Compiler.MemoryNative.BigintCached.native.leaf14).isSome)) data 29
    (row29_view.trans row29_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports14 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw14).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw14).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw14).inputs) data 30
    (row30_view.trans row30_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion15 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [15] Airbender.Compiler.MemoryNative.BigintCached.native.leaf15).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [15] Airbender.Compiler.MemoryNative.BigintCached.native.leaf15).isSome)) data 31
    (row31_view.trans row31_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports15 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw15).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw15).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw15).inputs) data 32
    (row32_view.trans row32_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion16 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [16] Airbender.Compiler.MemoryNative.BigintCached.native.leaf16).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [16] Airbender.Compiler.MemoryNative.BigintCached.native.leaf16).isSome)) data 33
    (row33_view.trans row33_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports16 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw16).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw16).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw16).inputs) data 34
    (row34_view.trans row34_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion17 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [17] Airbender.Compiler.MemoryNative.BigintCached.native.leaf17).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [17] Airbender.Compiler.MemoryNative.BigintCached.native.leaf17).isSome)) data 35
    (row35_view.trans row35_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports17 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw17).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw17).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw17).inputs) data 36
    (row36_view.trans row36_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion18 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [18] Airbender.Compiler.MemoryNative.BigintCached.native.leaf18).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [18] Airbender.Compiler.MemoryNative.BigintCached.native.leaf18).isSome)) data 37
    (row37_view.trans row37_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports18 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw18).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw18).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw18).inputs) data 38
    (row38_view.trans row38_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion19 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [19] Airbender.Compiler.MemoryNative.BigintCached.native.leaf19).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [19] Airbender.Compiler.MemoryNative.BigintCached.native.leaf19).isSome)) data 39
    (row39_view.trans row39_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports19 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw19).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw19).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw19).inputs) data 40
    (row40_view.trans row40_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion20 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [20] Airbender.Compiler.MemoryNative.BigintCached.native.leaf20).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [20] Airbender.Compiler.MemoryNative.BigintCached.native.leaf20).isSome)) data 41
    (row41_view.trans row41_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports20 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw20).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw20).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw20).inputs) data 42
    (row42_view.trans row42_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion21 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [21] Airbender.Compiler.MemoryNative.BigintCached.native.leaf21).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [21] Airbender.Compiler.MemoryNative.BigintCached.native.leaf21).isSome)) data 43
    (row43_view.trans row43_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports21 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw21).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw21).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw21).inputs) data 44
    (row44_view.trans row44_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion22 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [22] Airbender.Compiler.MemoryNative.BigintCached.native.leaf22).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [22] Airbender.Compiler.MemoryNative.BigintCached.native.leaf22).isSome)) data 45
    (row45_view.trans row45_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports22 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw22).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw22).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw22).inputs) data 46
    (row46_view.trans row46_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion23 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [23] Airbender.Compiler.MemoryNative.BigintCached.native.leaf23).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [23] Airbender.Compiler.MemoryNative.BigintCached.native.leaf23).isSome)) data 47
    (row47_view.trans row47_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports23 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw23).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw23).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw23).inputs) data 48
    (row48_view.trans row48_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion24 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [24] Airbender.Compiler.MemoryNative.BigintCached.native.leaf24).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [24] Airbender.Compiler.MemoryNative.BigintCached.native.leaf24).isSome)) data 49
    (row49_view.trans row49_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports24 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw24).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw24).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw24).inputs) data 50
    (row50_view.trans row50_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion25 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [25] Airbender.Compiler.MemoryNative.BigintCached.native.leaf25).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [25] Airbender.Compiler.MemoryNative.BigintCached.native.leaf25).isSome)) data 51
    (row51_view.trans row51_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports25 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw25).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw25).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw25).inputs) data 52
    (row52_view.trans row52_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion26 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [26] Airbender.Compiler.MemoryNative.BigintCached.native.leaf26).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [26] Airbender.Compiler.MemoryNative.BigintCached.native.leaf26).isSome)) data 53
    (row53_view.trans row53_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports26 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw26).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw26).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw26).inputs) data 54
    (row54_view.trans row54_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion27 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [27] Airbender.Compiler.MemoryNative.BigintCached.native.leaf27).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [27] Airbender.Compiler.MemoryNative.BigintCached.native.leaf27).isSome)) data 55
    (row55_view.trans row55_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports27 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw27).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw27).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw27).inputs) data 56
    (row56_view.trans row56_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion28 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [28] Airbender.Compiler.MemoryNative.BigintCached.native.leaf28).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [28] Airbender.Compiler.MemoryNative.BigintCached.native.leaf28).isSome)) data 57
    (row57_view.trans row57_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports28 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw28).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw28).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw28).inputs) data 58
    (row58_view.trans row58_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion29 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [29] Airbender.Compiler.MemoryNative.BigintCached.native.leaf29).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [29] Airbender.Compiler.MemoryNative.BigintCached.native.leaf29).isSome)) data 59
    (row59_view.trans row59_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports29 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw29).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw29).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw29).inputs) data 60
    (row60_view.trans row60_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion30 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [30] Airbender.Compiler.MemoryNative.BigintCached.native.leaf30).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [30] Airbender.Compiler.MemoryNative.BigintCached.native.leaf30).isSome)) data 61
    (row61_view.trans row61_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports30 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw30).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw30).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw30).inputs) data 62
    (row62_view.trans row62_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion31 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [31] Airbender.Compiler.MemoryNative.BigintCached.native.leaf31).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [31] Airbender.Compiler.MemoryNative.BigintCached.native.leaf31).isSome)) data 63
    (row63_view.trans row63_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports31 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw31).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw31).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw31).inputs) data 64
    (row64_view.trans row64_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion32 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [32] Airbender.Compiler.MemoryNative.BigintCached.native.leaf32).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [32] Airbender.Compiler.MemoryNative.BigintCached.native.leaf32).isSome)) data 65
    (row65_view.trans row65_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports32 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw32).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw32).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw32).inputs) data 66
    (row66_view.trans row66_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion33 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [33] Airbender.Compiler.MemoryNative.BigintCached.native.leaf33).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [33] Airbender.Compiler.MemoryNative.BigintCached.native.leaf33).isSome)) data 67
    (row67_view.trans row67_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports33 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw33).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw33).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw33).inputs) data 68
    (row68_view.trans row68_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion34 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [34] Airbender.Compiler.MemoryNative.BigintCached.native.leaf34).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [34] Airbender.Compiler.MemoryNative.BigintCached.native.leaf34).isSome)) data 69
    (row69_view.trans row69_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports34 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw34).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw34).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw34).inputs) data 70
    (row70_view.trans row70_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion35 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [35] Airbender.Compiler.MemoryNative.BigintCached.native.leaf35).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [35] Airbender.Compiler.MemoryNative.BigintCached.native.leaf35).isSome)) data 71
    (row71_view.trans row71_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports35 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw35).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw35).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw35).inputs) data 72
    (row72_view.trans row72_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion36 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [36] Airbender.Compiler.MemoryNative.BigintCached.native.leaf36).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [36] Airbender.Compiler.MemoryNative.BigintCached.native.leaf36).isSome)) data 73
    (row73_view.trans row73_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports36 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw36).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw36).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw36).inputs) data 74
    (row74_view.trans row74_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion37 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [37] Airbender.Compiler.MemoryNative.BigintCached.native.leaf37).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [37] Airbender.Compiler.MemoryNative.BigintCached.native.leaf37).isSome)) data 75
    (row75_view.trans row75_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports37 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw37).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw37).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw37).inputs) data 76
    (row76_view.trans row76_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion38 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [38] Airbender.Compiler.MemoryNative.BigintCached.native.leaf38).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [38] Airbender.Compiler.MemoryNative.BigintCached.native.leaf38).isSome)) data 77
    (row77_view.trans row77_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports38 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw38).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw38).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw38).inputs) data 78
    (row78_view.trans row78_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem expansion39 : (LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [39] Airbender.Compiler.MemoryNative.BigintCached.native.leaf39).isSome = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericLookupSourceChecks.ofFlag (n := 0) ((LookupPayload.expand Airbender.Compiler.MemoryNative.BigintCached.native.definitions [39] Airbender.Compiler.MemoryNative.BigintCached.native.leaf39).isSome)) data 79
    (row79_view.trans row79_source) checked
  exact (NumericLookupSourceChecks.ofFlag_check _).symm.trans valid

theorem ports39 : Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck (Airbender.Compiler.MemoryNative.BigintCached.native.raw39).inputs = true ∧
    (Airbender.Compiler.MemoryNative.BigintCached.native.raw39).inputs.all (fun address => Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible (address, .base)) = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofInputs Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing (Airbender.Compiler.MemoryNative.BigintCached.native.raw39).inputs) data 80
    (row80_view.trans row80_source) checked
  rw [NumericMemoryPayloadChecks.ofInputs_check] at valid
  simpa only [Bool.and_eq_true] using valid

theorem memoryReadFingerprint0 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate0.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw0 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate0 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw0 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 81
    (row81_view.trans row81_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint1 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate1.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw1 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate1 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw1 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 82
    (row82_view.trans row82_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint2 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate2.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw4 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate2 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw4 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 83
    (row83_view.trans row83_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint3 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate3.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw5 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate3 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw5 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 84
    (row84_view.trans row84_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint4 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate4.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[4]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw8 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate4 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[4]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw8 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 85
    (row85_view.trans row85_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint5 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate5.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[5]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw9 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate5 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[5]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw9 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 86
    (row86_view.trans row86_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint6 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate6.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[6]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw12 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate6 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[6]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw12 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 87
    (row87_view.trans row87_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint7 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate7.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[7]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw13 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate7 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[7]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw13 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 88
    (row88_view.trans row88_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint8 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate8.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[8]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw16 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate8 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[8]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw16 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 89
    (row89_view.trans row89_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint9 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate9.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[9]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw17 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate9 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[9]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw17 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 90
    (row90_view.trans row90_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint10 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate10.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[10]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw20 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate10 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[10]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw20 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 91
    (row91_view.trans row91_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint11 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate11.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[11]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw21 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate11 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[11]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw21 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 92
    (row92_view.trans row92_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint12 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate12.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[12]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw24 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate12 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[12]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw24 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 93
    (row93_view.trans row93_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint13 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate13.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[13]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw25 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate13 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[13]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw25 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 94
    (row94_view.trans row94_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint14 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate14.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[14]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw28 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate14 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[14]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw28 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 95
    (row95_view.trans row95_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint15 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate15.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[15]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw29 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate15 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[15]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw29 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 96
    (row96_view.trans row96_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint16 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate16.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[16]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw32 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate16 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[16]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw32 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 97
    (row97_view.trans row97_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint17 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate17.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[17]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw33 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate17 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[17]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw33 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 98
    (row98_view.trans row98_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint18 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate18.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[18]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw36 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate18 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[18]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw36 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 99
    (row99_view.trans row99_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadFingerprint19 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate19.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[19]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw37 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadCertificate19 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows)[19]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw37 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 100
    (row100_view.trans row100_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryReadMask : (Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck [(GKRAddress.InnerLayer 5 0)] = true ∧
      Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible ((GKRAddress.InnerLayer 5 0), .base) = true) ∧
    Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadMaskField.check Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadMaskField Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing [(GKRAddress.InnerLayer 5 0)]) data 101
    (row101_view.trans row101_source) checked
  rw [NumericMemoryPayloadChecks.ofField_check] at valid
  simpa only [Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true] using valid

theorem memoryWriteFingerprint0 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate0.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw2 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate0 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[0]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw2 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 102
    (row102_view.trans row102_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint1 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate1.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw3 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate1 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[1]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw3 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 103
    (row103_view.trans row103_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint2 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate2.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw6 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate2 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[2]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw6 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 104
    (row104_view.trans row104_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint3 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate3.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw7 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate3 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[3]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw7 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 105
    (row105_view.trans row105_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint4 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate4.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[4]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw10 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate4 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[4]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw10 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 106
    (row106_view.trans row106_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint5 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate5.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[5]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw11 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate5 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[5]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw11 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 107
    (row107_view.trans row107_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint6 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate6.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[6]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw14 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate6 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[6]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw14 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 108
    (row108_view.trans row108_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint7 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate7.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[7]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw15 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate7 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[7]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw15 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 109
    (row109_view.trans row109_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint8 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate8.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[8]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw18 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate8 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[8]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw18 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 110
    (row110_view.trans row110_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint9 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate9.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[9]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw19 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate9 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[9]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw19 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 111
    (row111_view.trans row111_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint10 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate10.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[10]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw22 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate10 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[10]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw22 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 112
    (row112_view.trans row112_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint11 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate11.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[11]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw23 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate11 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[11]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw23 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 113
    (row113_view.trans row113_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint12 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate12.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[12]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw26 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate12 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[12]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw26 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 114
    (row114_view.trans row114_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint13 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate13.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[13]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw27 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate13 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[13]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw27 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 115
    (row115_view.trans row115_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint14 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate14.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[14]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw30 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate14 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[14]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw30 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 116
    (row116_view.trans row116_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint15 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate15.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[15]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw31 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate15 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[15]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw31 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 117
    (row117_view.trans row117_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint16 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate16.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[16]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw34 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate16 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[16]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw34 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 118
    (row118_view.trans row118_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint17 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate17.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[17]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw35 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate17 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[17]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw35 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 119
    (row119_view.trans row119_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint18 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate18.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[18]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw38 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate18 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[18]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw38 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 120
    (row120_view.trans row120_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteFingerprint19 : Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate19.check
    (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[19]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
    Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw39 = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericNativePayloadChecks.ofMemory Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteCertificate19 (((Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows)[19]?).getD (Source.MemoryRow.mk (.constant 0) .zero .zero .zero))
  Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.MemoryNative.BigintCached.native.raw39 Airbender.Compiler.ConsumerNative.BigintCached.native.typing) data 121
    (row121_view.trans row121_source) checked
  rw [NumericNativePayloadChecks.ofMemory_check] at valid
  simp only [Bool.and_eq_true] at valid
  exact valid.2

theorem memoryWriteMask : (Airbender.Compiler.MemoryNative.BigintCached.native.bank.inputCheck [(GKRAddress.InnerLayer 5 0)] = true ∧
      Airbender.Compiler.ConsumerNative.BigintCached.native.typing.compatible ((GKRAddress.InnerLayer 5 0), .base) = true) ∧
    Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteMaskField.check Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement = true := by
  have valid := NumericNativePayloadChecks.checked_at (NumericMemoryPayloadChecks.ofField Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteMaskField Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement Airbender.Compiler.MemoryNative.BigintCached.native.bank Airbender.Compiler.ConsumerNative.BigintCached.native.typing [(GKRAddress.InnerLayer 5 0)]) data 122
    (row122_view.trans row122_source) checked
  rw [NumericMemoryPayloadChecks.ofField_check] at valid
  simpa only [Bool.and_eq_true, List.all_cons, List.all_nil, Bool.and_true] using valid

end Airbender.Compiler.MemoryPayloadChecks.BigintCached
