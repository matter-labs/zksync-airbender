import Airbender.Proofs.Tables.PackedColumn
import Airbender.Proofs.Tables.PackedRadix
import Mathlib.Tactic.Ring

namespace Airbender.Setup.Proofs.PackedRun
open PackedColumn PackedRadix
set_option warningAsError true

def ones (standard count : Nat) : Nat := Nat.ofDigits standard (List.replicate count 1)
def positions (standard count : Nat) : Nat := Nat.ofDigits standard (List.range count)

theorem linear_digits (standard count first stride : Nat) :
    Nat.ofDigits standard ((List.range count).map (fun index => first + stride * index)) =
      first * ones standard count + stride * positions standard count := by
  induction count with
  | zero => simp [ones, positions]
  | succ count ih =>
    simp only [List.range_succ, List.map_append, List.map_singleton, Nat.ofDigits_append]
    rw [ih]
    simp only [ones, List.replicate_succ', positions, List.range_succ,
      Nat.ofDigits_append, List.length_replicate, List.length_range, Nat.ofDigits,
      mul_zero, add_zero, Nat.cast_id, List.length_map]
    ring

theorem translated_digits (values : List Nat) (shift : Nat) :
    Nat.ofDigits 256 (values.map (fun value => value + shift)) =
      Nat.ofDigits 256 values + shift * ones 256 values.length := by
  induction values with
  | nil => simp [ones, Nat.ofDigits]
  | cons value rest ih =>
    simp only [List.map_cons, Nat.ofDigits, List.length_cons, ones,
      List.replicate_succ, Nat.cast_id] at *
    rw [ih]
    ring

/-- Nonnegative affine and repeated source blocks share this lossless form. -/
structure Run where
  count : Nat
  stride : Nat
  values : Array Nat

def Run.length (data : Run) : Nat := data.count * data.values.size
def Run.value (data : Run) (index : Nat) : Nat :=
  data.values[index % data.values.size]?.getD 0 + data.stride * (index / data.values.size)
def Run.valid (data : Run) : Bool :=
  data.values.all (fun value => value + data.stride * (data.count - 1) < 256)
def Run.row (data : Run) (index : Nat) : Nat :=
  Nat.ofDigits 256 (data.values.toList.map (fun value => value + data.stride * index))
def Run.packed (data : Run) : Nat :=
  (Nat.ofDigits 256 data.values.toList) * ones (256 ^ data.values.size) data.count +
    (data.stride * ones 256 data.values.size) * positions (256 ^ data.values.size) data.count

theorem row_linear (data : Run) (index : Nat) :
    data.row index = Nat.ofDigits 256 data.values.toList +
      (data.stride * ones 256 data.values.size) * index := by
  rw [Run.row, translated_digits]
  simp only [Array.length_toList]
  ring

theorem packed_rows (data : Run) :
    data.packed = Nat.ofDigits (256 ^ data.values.size)
      ((List.range data.count).map data.row) := by
  rw [show data.row = (fun index => Nat.ofDigits 256 data.values.toList +
    (data.stride * ones 256 data.values.size) * index) from funext (row_linear data)]
  exact (linear_digits _ _ _ _).symm

theorem row_values_bounded (data : Run) (valid : data.valid = true)
    (row : Nat) (within : row < data.count) :
    ∀ value ∈ data.values.toList, value + data.stride * row < 256 := by
  intro value member
  obtain ⟨position, positionBound, positionValue⟩ := Array.mem_iff_getElem.mp (by simpa using member : value ∈ data.values)
  have last := of_decide_eq_true ((Array.all_eq_true.mp valid) position positionBound)
  rw [positionValue] at last
  have earlier : data.stride * row ≤ data.stride * (data.count - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

theorem packed_byte (data : Run) (valid : data.valid = true)
    (index : Nat) (within : index < data.length) :
    digit data.packed index = data.value index := by
  have periodPositive : 0 < data.values.size := by unfold Run.length at within; nlinarith
  have rowWithin : index / data.values.size < data.count := by
    apply (Nat.div_lt_iff_lt_mul periodPositive).mpr
    simpa only [Run.length, Nat.mul_comm] using within
  have columnWithin : index % data.values.size < data.values.size := Nat.mod_lt _ periodPositive
  have rowBound : ∀ value ∈ (List.range data.count).map data.row,
      value < 256 ^ data.values.size := by
    intro value member
    obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
    have result := Nat.ofDigits_lt_base_pow_length (b := 256) (l := data.values.toList.map (fun value => value + data.stride * row)) (by omega) (by
      intro shifted shiftedMember
      obtain ⟨raw, rawMember, rfl⟩ := List.mem_map.mp shiftedMember
      exact row_values_bounded data valid row (List.mem_range.mp rowMember) raw rawMember)
    simpa [Run.row] using result
  have whole := extractDigitBase (256 ^ data.values.size)
    ((List.range data.count).map data.row) (index / data.values.size)
    (by positivity) rowBound (by simpa using rowWithin)
  simp only [List.getElem_map, List.getElem_range] at whole
  rw [← packed_rows] at whole
  have power : (256 ^ data.values.size) ^ (index / data.values.size) =
      256 ^ (data.values.size * (index / data.values.size)) := by rw [pow_mul]
  have segment := segment_digit data.packed (data.values.size * (index / data.values.size))
    data.values.size (index % data.values.size) columnWithin
  rw [← power, whole] at segment
  have compose : data.values.size * (index / data.values.size) + index % data.values.size = index := by
    exact Nat.div_add_mod index data.values.size
  rw [compose] at segment
  rw [← segment]
  unfold digit Run.row Run.value
  rw [extractDigitBase 256 _ _ (by omega)]
  · simp [List.getElem_map, columnWithin]
  · intro shifted shiftedMember
    obtain ⟨raw, rawMember, rfl⟩ := List.mem_map.mp shiftedMember
    exact row_values_bounded data valid _ rowWithin raw rawMember
  · simpa using columnWithin

end Airbender.Setup.Proofs.PackedRun
