import Airbender.Review.Helpers.Tables.SubwordROMData
import Airbender.Proofs.Tables.PeriodicColumns
import Mathlib.Tactic.IntervalCases

namespace Airbender.Verification.SubwordROMGeometry
open Setup Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

private def storedPeriod (column : Column) : Array Nat :=
  match column.blocks[0]? with
  | some (Block.periodic _ _ values) => values
  | _ => #[]
private def keyValues (byte : Bool) : Array Nat := storedPeriod (subwordROMData byte).columns[0]
private def groupSize (byte : Bool) : Nat := if byte then 8 else 4
private theorem values_size (byte : Bool) : (keyValues byte).size = groupSize byte := by
  cases byte <;> decide +kernel
private theorem key_shape (byte : Bool) : (subwordROMData byte).columns[0] =
    Column.mk #[.periodic 1048576 4 (keyValues byte)] := by cases byte <;> rfl
def key (byte : Bool) (n : Nat) : Nat :=
  if byte then 4 * (n / 8) + 4194304 * (n / 4 % 2) + 8388608 * (n / 2 % 2) +
    16777216 * (n % 2)
  else 4 * (n / 4) + 4194304 * (n / 2 % 2) + 8388608 * (n % 2)
private theorem key_samples (byte : Bool) (q : Fin (groupSize byte)) :
    (keyValues byte)[q.val]'(by rw [values_size]; exact q.isLt) = key byte q.val := by
  cases byte <;> revert q <;> decide +kernel

private theorem actual_key (byte : Bool) (n : Nat) (bound : n < (subwordROMData byte).length) :
    (subwordROMData byte).columns[0].get? n = some (key byte n) := by
  rw [key_shape]
  have positive : 0 < (keyValues byte).size := by rw [values_size]; cases byte <;> decide
  have extent : n < 1048576 * (keyValues byte).size := by
    rw [values_size]
    cases byte
    · change n < 4194304 at bound ⊢
      exact bound
    · change n < 8388608 at bound ⊢
      exact bound
  have actual := periodic_get (keyValues byte) 1048576 4 n positive extent
  simp only [Nat.cast_ofNat] at actual
  have sample := key_samples byte ⟨n % groupSize byte,
    Nat.mod_lt _ (by cases byte <;> decide)⟩
  have formula : key byte (n % groupSize byte) + 4 * (n / groupSize byte) = key byte n := by
    cases byte <;> simp only [key, groupSize, Bool.false_eq_true, reduceIte] <;> omega
  simp only [Column.get?, getFromBlocks, Block.length, if_pos extent]
  rw [actual]
  simp only [values_size, sample, formula]

private theorem padding (byte : Bool) (lane : Fin 5) (n : Nat)
    (bound : n < (subwordROMData byte).length) :
    (subwordROMData byte).columns[lane.val + 3].get? n = some 0 := by
  have shape : (subwordROMData byte).columns[lane.val + 3] =
      Column.mk #[.affine (subwordROMData byte).length 0 0] := by
    cases byte <;> fin_cases lane <;> rfl
  rw [shape]
  simp [Column.get?, getFromBlocks, Block.get?, Block.length, bound]
private theorem tag (byte : Bool) (n : Nat) (bound : n < (subwordROMData byte).length) :
    (subwordROMData byte).columns[8].get? n = some (subwordROMRegion byte).id := by
  have shape : (subwordROMData byte).columns[8] =
      Column.mk #[.affine (subwordROMData byte).length (subwordROMRegion byte).id 0] := by
    cases byte <;> rfl
  rw [shape]
  simp [Column.get?, getFromBlocks, Block.get?, Block.length, bound]

/-- Imported address/control packing and every non-output field, independent
    of the generalized public program's supplied load results. -/
theorem row (byte : Bool) (n lo hi : Nat) (bound : n < (subwordROMData byte).length) :
    ((subwordROMRow byte n).set 1 lo).set 2 hi =
      #v[key byte n, lo, hi, 0, 0, 0, 0, 0, (subwordROMRegion byte).id] := by
  apply Vector.ext
  intro lane hLane
  interval_cases lane
  all_goals simp only [Vector.getElem_set, subwordROMRow, Vector.getElem_map,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  · exact congrArg (fun value => value.getD 0) (actual_key byte n bound)
  · rfl
  · rfl
  · exact congrArg (fun value => value.getD 0) (padding byte 0 n bound)
  · exact congrArg (fun value => value.getD 0) (padding byte 1 n bound)
  · exact congrArg (fun value => value.getD 0) (padding byte 2 n bound)
  · exact congrArg (fun value => value.getD 0) (padding byte 3 n bound)
  · exact congrArg (fun value => value.getD 0) (padding byte 4 n bound)
  · exact congrArg (fun value => value.getD 0) (tag byte n bound)

end Airbender.Verification.SubwordROMGeometry
