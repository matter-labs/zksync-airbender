import Airbender.Proofs.Keccak.SplitParityIotaOperation

namespace Airbender.Keccak.Split.Native.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

/-- Actual native parity lanes, padded only in the unused seventh slot. -/
def parityReferenceLanes (cached writing : Bool) (w : Nat → ZMod babyBearModulus) : Vector Nat 7 :=
  Vector.ofFn fun lane => if active : lane.val < 6 then
    parityLaneValue cached writing w ⟨lane.val, active⟩ else 0

/-- The original controller selects iota only on the first column. -/
def paritySelectedRound (index : Fin 361) : Fin 32 :=
  ⟨if index.val % 5 = 0 then index.val / 15 else 0, by have := index.isLt; split <;> omega⟩

variable [Fact babyBearModulus.Prime]

/-- The actual first lane follows the original delayed-iota condition. -/
theorem parity_native_first_lane (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable
        else ColumnParity.clockConstraints columnParityFixedTable)) (index : Fin 361)
    (selected : (parityQueryRow cached w 1)[3] = ((paritySelectedRound index).val : ZMod babyBearModulus)) :
    parityLaneValue cached true w 0 =
      if index.val % 5 = 0 then parityLaneValue cached false w 0 ^^^ Call.roundConstant (index.val / 15)
      else parityLaneValue cached false w 0 := by
  have effect := parity_iota_lane_operation cached w holds (paritySelectedRound index) selected
  by_cases first : index.val % 5 = 0
  · simpa only [paritySelectedRound, first, ↓reduceIte] using effect
  · simpa [paritySelectedRound, first, Call.roundConstant] using effect

omit [Fact babyBearModulus.Prime] in
set_option maxHeartbeats 80000 in
private theorem reference_result_of_values (input output : Fin 6 → Nat) (index : Fin 361)
    (kind : kindAt index.val = .columnParity)
    (first : output 0 = if index.val % 5 = 0 then input 0 ^^^ Call.roundConstant (index.val / 15) else input 0)
    (same : ∀ lane : Fin 4, output ⟨1 + lane.val, by omega⟩ = input ⟨1 + lane.val, by omega⟩)
    (parity : output 5 = output 0 ^^^ output 1 ^^^ output 2 ^^^ output 3 ^^^ output 4) :
    Call.result index (Vector.ofFn fun lane : Fin 7 => if live : lane.val < 6 then input ⟨lane.val, live⟩ else 0) =
      (Vector.ofFn fun lane : Fin 7 => if live : lane.val < 6 then output ⟨lane.val, live⟩ else 0) := by
  have same1 : output 1 = input 1 := same 0
  have same2 : output 2 = input 2 := same 1
  have same3 : output 3 = input 3 := same 2
  have same4 : output 4 = input 4 := same 3
  have operands := congrArg₂ Nat.xor (congrArg₂ Nat.xor
    (congrArg₂ Nat.xor (congrArg₂ Nat.xor first same1) same2) same3) same4
  have parity := parity.trans operands
  simp only [Call.result, kind]
  apply Vector.ext
  intro lane bound
  interval_cases lane <;>
    simp [Vector.getElem_ofFn, first, same1, same2, same3, same4, parity]

/-- The complete actual parity output equals the unchanged blessed call reference. -/
theorem parity_native_reference_result (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable
        else ColumnParity.clockConstraints columnParityFixedTable)) (index : Fin 361)
    (kind : kindAt index.val = .columnParity)
    (selected : (parityQueryRow cached w 1)[3] = ((paritySelectedRound index).val : ZMod babyBearModulus)) :
    Call.result index (parityReferenceLanes cached false w) = parityReferenceLanes cached true w := by
  exact reference_result_of_values (parityLaneValue cached false w) (parityLaneValue cached true w)
    index kind (parity_native_first_lane cached w holds index selected)
    (parity_readonly_lane cached w) (parity_native_lane_operation cached w holds)

/-- An actual active native parity row binds the original transition, all physical slots and full lane result. -/
theorem parity_native_reference_schedule (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable
        else ColumnParity.clockConstraints columnParityFixedTable)) (active : w 0 = 1) :
    ∃ index : Fin 361, kindAt index.val = .columnParity ∧
      (parityQueryRow cached w 1)[0] = (controlAt index.val : ZMod babyBearModulus) ∧
      (parityQueryRow cached w 1)[2] = (bump (controlAt index.val) : ZMod babyBearModulus) ∧
      (∀ lane : Fin 6, (parityQueryRow cached w 0)[1 + lane.val] =
        ((Call.slots index)[lane.val].val : ZMod babyBearModulus)) ∧
      Call.result index (parityReferenceLanes cached false w) = parityReferenceLanes cached true w := by
  obtain ⟨index, kind, before, after, selected⟩ := parity_native_controller_schedule cached w holds active
  exact ⟨index, kind, before, after, parity_native_slots cached w holds active index before,
    parity_native_reference_result cached w holds index kind selected⟩

end Airbender.Keccak.Split.Native.Proofs
