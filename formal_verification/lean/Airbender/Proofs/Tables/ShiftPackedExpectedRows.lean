import Airbender.Proofs.Tables.ShiftPackedBasis

namespace Airbender.Verification.ShiftPackedReference
open Airbender.Setup.Proofs PackedSignedRun PackedWordBounds PackedWordColumn
set_option warningAsError true
set_option Elab.async false

def expectedRow (lane row : Nat) : Nat :=
  wordSum (basisRow (row / 256) lane) (row % 256) (List.range 8) % 65536 ^ 256

theorem wordFold_congr (left right : Nat → Nat) (byte : Nat) (bits : List Nat)
    (agreement : ∀ bit ∈ bits, left bit = right bit) :
    wordFold left byte bits = wordFold right byte bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
    simp only [wordFold, List.foldr_cons] at *
    rw [agreement bit (by simp), ih (by intro value member; exact agreement value (by simp [member]))]

theorem expectedRow_digit (lane row control : Nat) (laneBound : lane < 4)
    (rowBound : row < 1024) (controlBound : control < 256) :
    digit 65536 (expectedRow lane row) control = rowByte lane (row / 256) (row % 256) control := by
  have projection := segment_digit 65536
    (wordFold (basisRow (row / 256) lane) (row % 256) (List.range 8)) 0 256 control controlBound
  simp only [pow_zero, Nat.div_one, Nat.zero_add] at projection
  have same := wordFold_eq_sum (basisRow (row / 256) lane) (row % 256) (List.range 8)
    (basis_disjoint (row / 256) lane (by omega) laneBound)
  rw [expectedRow, ← same, projection, wordFold_digit, rowByte_decomposition _ _ _ _ (Nat.mod_lt _ (by omega))]
  apply wordFold_congr
  intro bit member
  exact basis_digit _ _ _ _ (by omega) laneBound (List.mem_range.mp member) controlBound

end Airbender.Verification.ShiftPackedReference
