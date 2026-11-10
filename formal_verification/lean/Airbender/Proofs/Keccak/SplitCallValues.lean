import Airbender.Proofs.Keccak.SplitCallReference
import Clean.Utils.Rotation

namespace Airbender.Keccak.Split.Call.Proofs
open Trace Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option Elab.async false

/-- All original delayed-iota constants are complete sixty-four-bit values. -/
theorem round_constant_bound (round : Nat) : roundConstant round < 2 ^ 64 := by
  unfold roundConstant
  split
  · exact BitVec.isLt _
  · decide

/-- The original call result only uses its declared live input lanes. -/
theorem result_live_congr (index : Fin 361) (input other : Vector Nat 7)
    (agree : ∀ lane : Fin 7, lane.val < slotCount (kindAt index.val) → input[lane] = other[lane]) :
    ∀ lane : Fin 7, lane.val < slotCount (kindAt index.val) →
      (result index input)[lane] = (result index other)[lane] := by
  intro lane live
  cases kind : kindAt index.val with
  | columnParity =>
    have same (digit : Fin 6) : input[(⟨digit.val, by omega⟩ : Fin 7)] = other[(⟨digit.val, by omega⟩ : Fin 7)] :=
      agree ⟨digit.val, by omega⟩ (by simpa only [kind, slotCount] using digit.isLt)
    have a := same 0; have b := same 1; have c := same 2
    have d := same 3; have e := same 4; have f := same 5
    fin_cases lane <;> simp_all [result, slotCount]
  | thetaRho =>
    have same : input = other := by
      apply Vector.ext
      intro digit bound
      exact agree ⟨digit, bound⟩ (by simpa only [kind, slotCount] using bound)
    rw [same]
  | chi5 =>
    have same (digit : Fin 5) : input[(⟨digit.val, by omega⟩ : Fin 7)] = other[(⟨digit.val, by omega⟩ : Fin 7)] :=
      agree ⟨digit.val, by omega⟩ (by simpa only [kind, slotCount] using digit.isLt)
    have a := same 0; have b := same 1; have c := same 2
    have d := same 3; have e := same 4
    fin_cases lane <;> simp_all [result, slotCount]

/-- Canonical complete inputs give canonical complete reference output lanes. -/
theorem result_lane_bound (index : Fin 361) (input : Vector Nat 7)
    (bounds : ∀ lane : Fin 7, input[lane] < 2 ^ 64) (lane : Fin 7) :
    (result index input)[lane] < 2 ^ 64 := by
  cases kind : kindAt index.val with
  | columnParity =>
    have first : (if index.val % 5 = 0 then input[0] ^^^ roundConstant (index.val / 15) else input[0]) < 2 ^ 64 := by
      split
      · exact Nat.xor_lt_two_pow (bounds 0) (round_constant_bound _)
      · exact bounds 0
    simp only [result, kind]
    fin_cases lane
    · exact first
    · exact bounds 1
    · exact bounds 2
    · exact bounds 3
    · exact bounds 4
    · exact Nat.xor_lt_two_pow
        (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow first (bounds 1)) (bounds 2)) (bounds 3)) (bounds 4)
    · exact bounds 6
  | thetaRho =>
    have rotated : rotLeft64 input[6] 1 < 2 ^ 64 := Utils.Rotation.rotRight64_lt _ _ (bounds 6)
    have delta := Nat.xor_lt_two_pow (bounds 5) rotated
    simp only [result, kind, Fin.getElem_fin, Vector.getElem_ofFn]
    split
    · exact Utils.Rotation.rotRight64_lt _ _ (Nat.xor_lt_two_pow (bounds lane) delta)
    · exact bounds lane
  | chi5 =>
    simp only [result, kind, Fin.getElem_fin, Vector.getElem_ofFn]
    split
    · exact Nat.xor_lt_two_pow (bounds lane)
        (lt_of_le_of_lt Nat.and_le_right (bounds ⟨(lane.val + 2) % 5, by omega⟩))
    · exact bounds lane

/-- Equal declared output lanes give the exact same complete reference write list. -/
theorem writes_live_congr (index : Fin 361) (pointer : BitVec 32) (output other : Vector Nat 7)
    (agree : ∀ lane : Fin 7, lane.val < slotCount (kindAt index.val) → output[lane] = other[lane]) :
    writes index pointer output = writes index pointer other := by
  unfold writes
  congr 1
  apply List.flatMap_congr
  intro lane member
  split_ifs with valid
  · have same : output[lane] = other[lane] := by
      simpa only [Fin.getElem_fin] using agree ⟨lane, valid⟩ (List.mem_range.mp member)
    rw [same]
  · rfl

end Airbender.Keccak.Split.Call.Proofs
