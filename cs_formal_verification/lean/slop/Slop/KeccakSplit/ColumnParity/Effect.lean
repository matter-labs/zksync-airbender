module
public import Slop.KeccakSplit.ColumnParity.Iota
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/- The column-parity call result on its six lanes (ported from PR #585's
   SplitParityReferenceEffect). -/

namespace Airbender.Keccak.Split.ColumnParity.Proofs
open Airbender.Trace Airbender.Arithmetic Airbender.Keccak.Split.RowProofs
set_option warningAsError true

/-- Lane values padded to the seven call positions. -/
def refLanes (w : Nat → ZMod babyBearModulus) (writing : Bool) : Vector Nat 7 :=
  Vector.ofFn fun lane => if active : lane.val < 6 then laneValue w writing ⟨lane.val, active⟩ else 0

/-- The round whose iota call `index` applies: the previous round on the first column. -/
def selectedRound (index : Fin 361) : Fin 32 :=
  ⟨if index.val % 5 = 0 then index.val / 15 else 0, by have := index.isLt; split <;> omega⟩

theorem first_lane {w : Nat → ZMod babyBearModulus} (h : Holds w) (index : Fin 361)
    (selected : (row w 1)[3] = ((selectedRound index).val : ZMod babyBearModulus)) :
    laneValue w true 0 =
      if index.val % 5 = 0 then laneValue w false 0 ^^^ Call.roundConstant (index.val / 15)
      else laneValue w false 0 := by
  have effect := iota_lane_operation h (selectedRound index) selected
  by_cases first : index.val % 5 = 0
  · simpa only [selectedRound, first, ↓reduceIte] using effect
  · simpa [selectedRound, first, Call.roundConstant] using effect

theorem reference_result_of_values (input output : Fin 6 → Nat) (index : Fin 361)
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

theorem reference_result {w : Nat → ZMod babyBearModulus} (h : Holds w) (index : Fin 361)
    (kind : kindAt index.val = .columnParity)
    (selected : (row w 1)[3] = ((selectedRound index).val : ZMod babyBearModulus)) :
    Call.result index (refLanes w false) = refLanes w true :=
  reference_result_of_values (laneValue w false) (laneValue w true) index kind
    (first_lane h index selected) (readonly_lane w) (lane_operation h)

end Airbender.Keccak.Split.ColumnParity.Proofs
