import Airbender.Proofs.Keccak.SplitCallMemoryProjection
import Airbender.Proofs.Keccak.SplitPermutationDefinitions

namespace Airbender.Keccak.Split.Call.Proofs
open Trace Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option Elab.async false

/-- A complete physical snapshot reads the thirty real lane slots. The unused
padding slot has value zero and requires no Sail memory cell. -/
def PhysicalSnapshot (state : State) (pointer : BitVec 32) (lanes : LaneState) : Prop :=
  lanes 30 = 0 ∧ ∀ physical : Fin 31, physical.val < 30 →
    lanes physical < 2 ^ 64 ∧ ∀ high : Bool,
      (laneCell pointer physical high).read state = .ok (half (lanes physical) high) state

/-- Both exact word halves identify the complete canonical sixty-four-bit lane. -/
theorem lane_eq_of_halves {one two : Nat} (first : one < 2 ^ 64) (second : two < 2 ^ 64)
    (low : half one false = half two false) (high : half one true = half two true) : one = two := by
  have lower := congrArg BitVec.toNat low
  have upper := congrArg BitVec.toNat high
  simp only [half, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat] at lower upper
  norm_num only [Nat.reducePow] at first second lower upper
  have firstHigh : one / 4294967296 < 4294967296 := by omega
  have secondHigh : two / 4294967296 < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt firstHigh, Nat.mod_eq_of_lt secondHigh] at upper
  omega

/-- No declared live slot uses the unused physical padding lane. -/
theorem active_slot_bound (index : Fin 361) (lane : Fin 7)
    (live : lane.val < slotCount (kindAt index.val)) : (slots index)[lane].val < 30 := by
  by_cases small : lane.val < 5
  · have bound : (slots index)[lane].val < 25 := by
      simp only [slots, Fin.getElem_fin, Vector.getElem_ofFn, dif_pos small]
      exact Fin.isLt _
    omega
  · simp only [slots, Fin.getElem_fin, Vector.getElem_ofFn, dif_neg small]
    by_cases parity : kindAt index.val = .columnParity ∧ lane.val = 5
    · rw [if_pos parity]
      change 25 + index.val % 5 < 30
      omega
    · rw [if_neg parity]
      by_cases theta : kindAt index.val = .thetaRho
      · rw [if_pos theta]
        change 25 + (if lane.val = 5 then (index.val % 5 + 4) % 5 else (index.val % 5 + 1) % 5) < 30
        split <;> omega
      · rw [if_neg theta]
        change (30 : Nat) < 30
        cases kind : kindAt index.val with
        | columnParity =>
          have same : lane.val = 5 := by simp only [kind, slotCount] at live; omega
          exact False.elim (parity ⟨kind, same⟩)
        | thetaRho => exact False.elim (theta kind)
        | chi5 => simp only [kind, slotCount] at live; omega

end Airbender.Keccak.Split.Call.Proofs
