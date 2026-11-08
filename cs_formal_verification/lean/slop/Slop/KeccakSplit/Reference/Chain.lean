module
public import Slop.KeccakSplit.Reference.SnapshotStep

@[expose] public section

namespace Airbender.Keccak.Split.Call.Proofs
open Trace Trace.Proofs
set_option warningAsError true

/-- The physical lanes after `count` calls, starting from `initial`. -/
def chainLanes (initial : LaneState) : Nat → LaneState
  | 0 => initial
  | count + 1 => microStep (Fin.ofNat 361 count) (chainLanes initial count)

/-- Two 32-bit words combine into the 64-bit lane whose halves they are. -/
theorem half_combine (low high : BitVec 32) (upper : Bool) :
    half (low.toNat + 2 ^ 32 * high.toNat) upper = if upper then high else low := by
  have lowBound := low.isLt
  have highBound := high.isLt
  apply BitVec.eq_of_toNat_eq
  cases upper
  · simp only [half, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat]
    omega
  · simp only [half, ↓reduceIte, BitVec.toNat_ofNat]
    have quotient : (low.toNat + 2 ^ 32 * high.toNat) / 2 ^ 32 = high.toNat := by omega
    rw [quotient]
    omega

end Airbender.Keccak.Split.Call.Proofs
