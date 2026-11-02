import Airbender.Proofs.Tables.PackedRunArithmetic

namespace Airbender.Setup.Proofs.PackedSignedRun
open PackedRadix PackedRun
set_option warningAsError true

def digit (radix payload index : Nat) : Nat := payload / radix ^ index % radix

theorem segment_digit (radix payload origin length index : Nat) (within : index < length) :
    digit radix ((payload / radix ^ origin) % radix ^ length) index =
      digit radix payload (origin + index) := by
  have splitPower : radix ^ length = radix ^ index * radix ^ (length - index) := by
    rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt within)]
  have tailPower : radix ^ (length - index) = radix * radix ^ (length - index - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ length - index)]
  simp only [digit]
  rw [splitPower, Nat.mod_mul_right_div_self, tailPower, Nat.mod_mul_right_mod,
    Nat.div_div_eq_div_mul, ← pow_add]

theorem shifted_digits (radix : Nat) (values : List Nat) (shift : Int)
    (nonnegative : ∀ value ∈ values, 0 ≤ (value : Int) + shift) :
    ((Nat.ofDigits radix (values.map (fun (value : Nat) => ((value : Int) + shift).toNat)) : Nat) : Int) =
      ((Nat.ofDigits radix values : Nat) : Int) + shift * (ones radix values.length : Int) := by
  induction values with
  | nil => simp [ones, Nat.ofDigits]
  | cons value rest ih =>
    have head := nonnegative value (by simp)
    have tail : ∀ value ∈ rest, 0 ≤ (value : Int) + shift := by
      intro value member
      exact nonnegative value (by simp [member])
    simp only [List.map_cons, Nat.ofDigits, List.length_cons, ones,
      List.replicate_succ, Nat.cast_id, Nat.cast_add, Nat.cast_mul,
      Int.toNat_of_nonneg head] at *
    rw [ih tail]
    ring

theorem linear_rows (radix count : Nat) (rows : Nat → Nat) (first stride : Int)
    (values : ∀ index < count, (rows index : Int) = first + stride * index) :
    ((Nat.ofDigits radix ((List.range count).map rows) : Nat) : Int) =
      first * (ones radix count : Int) + stride * (positions radix count : Int) := by
  induction count with
  | zero => simp [ones, positions]
  | succ count ih =>
    have earlier : ∀ index < count, (rows index : Int) = first + stride * index := by
      intro index within
      exact values index (by omega)
    rw [List.range_succ, List.map_append, List.map_singleton, Nat.ofDigits_append,
      List.length_map, List.length_range, ones_succ, positions_succ]
    simp only [Nat.ofDigits, mul_zero, add_zero, Nat.cast_id, Nat.cast_add,
      Nat.cast_mul, Nat.cast_pow]
    rw [ih earlier, values count (by omega)]
    ring

structure Run where
  count : Nat
  stride : Int
  values : Array Nat

def Run.length (data : Run) : Nat := data.count * data.values.size
def Run.value (data : Run) (index : Nat) : Nat :=
  ((data.values[index % data.values.size]?.getD 0 : Int) +
    data.stride * (index / data.values.size)).toNat
def Run.valid (radix : Nat) (data : Run) : Bool :=
  data.values.all (fun value => decide (value < radix ∧
    0 ≤ (value : Int) + data.stride * ((data.count - 1 : Nat) : Int) ∧
    (value : Int) + data.stride * ((data.count - 1 : Nat) : Int) < radix))
def Run.row (radix : Nat) (data : Run) (index : Nat) : Nat :=
  Nat.ofDigits radix (data.values.toList.map
    (fun (value : Nat) => ((value : Int) + data.stride * index).toNat))
def Run.packed (radix : Nat) (data : Run) : Nat :=
  Nat.ofDigits (radix ^ data.values.size) ((List.range data.count).map (data.row radix))

theorem value_bounds (radix : Nat) (data : Run) (valid : data.valid radix = true)
    (row : Nat) (within : row < data.count) (value : Nat) (member : value ∈ data.values.toList) :
    0 ≤ (value : Int) + data.stride * row ∧
      (value : Int) + data.stride * row < radix := by
  obtain ⟨position, bound, same⟩ := Array.mem_iff_getElem.mp (by simpa using member : value ∈ data.values)
  have endpoints := of_decide_eq_true (Array.all_eq_true.mp valid position bound)
  rw [same] at endpoints
  have rowBound : (row : Int) ≤ (data.count - 1 : Nat) := by omega
  by_cases positive : 0 ≤ data.stride
  · have lower := mul_nonneg positive (Int.natCast_nonneg row)
    have upper := mul_le_mul_of_nonneg_left rowBound positive
    constructor <;> omega
  · have lower := mul_le_mul_of_nonpos_left rowBound (by omega : data.stride ≤ 0)
    have upper := mul_nonpos_of_nonpos_of_nonneg (by omega : data.stride ≤ 0) (Int.natCast_nonneg row)
    constructor <;> omega

theorem row_linear (radix : Nat) (data : Run) (valid : data.valid radix = true)
    (row : Nat) (within : row < data.count) :
    (data.row radix row : Int) = ((Nat.ofDigits radix data.values.toList : Nat) : Int) +
      data.stride * (ones radix data.values.size : Int) * row := by
  unfold Run.row
  rw [shifted_digits]
  · simp only [Array.length_toList]
    ring
  · intro value member
    exact (value_bounds radix data valid row within value member).1

theorem packed_linear (radix : Nat) (data : Run) (valid : data.valid radix = true) :
    (data.packed radix : Int) =
      ((Nat.ofDigits radix data.values.toList : Nat) : Int) * (ones (radix ^ data.values.size) data.count : Int) +
      data.stride * (ones radix data.values.size : Int) * (positions (radix ^ data.values.size) data.count : Int) := by
  exact linear_rows _ _ _ _ _ (row_linear radix data valid)

theorem packed_digit (radix : Nat) (positive : 1 < radix) (data : Run)
    (valid : data.valid radix = true) (index : Nat) (within : index < data.length) :
    digit radix (data.packed radix) index = data.value index := by
  have periodPositive : 0 < data.values.size := by unfold Run.length at within; nlinarith
  have rowWithin : index / data.values.size < data.count := by
    apply (Nat.div_lt_iff_lt_mul periodPositive).mpr
    simpa only [Run.length, Nat.mul_comm] using within
  have columnWithin : index % data.values.size < data.values.size := Nat.mod_lt _ periodPositive
  have rowBound : ∀ value ∈ (List.range data.count).map (data.row radix),
      value < radix ^ data.values.size := by
    intro value member
    obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
    have result := Nat.ofDigits_lt_base_pow_length (b := radix)
      (l := data.values.toList.map (fun (value : Nat) => ((value : Int) + data.stride * row).toNat)) positive (by
        intro shifted shiftedMember
        obtain ⟨raw, rawMember, rfl⟩ := List.mem_map.mp shiftedMember
        have bounds := value_bounds radix data valid row (List.mem_range.mp rowMember) raw rawMember
        omega)
    simpa [Run.row] using result
  have whole := extractDigitBase (radix ^ data.values.size)
    ((List.range data.count).map (data.row radix)) (index / data.values.size)
    (by positivity) rowBound (by simpa using rowWithin)
  simp only [List.getElem_map, List.getElem_range] at whole
  have power : (radix ^ data.values.size) ^ (index / data.values.size) =
      radix ^ (data.values.size * (index / data.values.size)) := by rw [pow_mul]
  have segment := segment_digit radix (data.packed radix) (data.values.size * (index / data.values.size))
    data.values.size (index % data.values.size) columnWithin
  rw [← power, show data.packed radix = Nat.ofDigits (radix ^ data.values.size)
    ((List.range data.count).map (data.row radix)) from rfl, whole] at segment
  have compose : data.values.size * (index / data.values.size) + index % data.values.size = index :=
    Nat.div_add_mod index data.values.size
  rw [compose] at segment
  change digit radix (Nat.ofDigits (radix ^ data.values.size)
    ((List.range data.count).map (data.row radix))) index = _
  rw [← segment]
  unfold digit Run.row Run.value
  rw [extractDigitBase radix _ _ (by omega)]
  · simp [List.getElem_map, columnWithin]
  · intro shifted shiftedMember
    obtain ⟨raw, rawMember, rfl⟩ := List.mem_map.mp shiftedMember
    have bounds := value_bounds radix data valid _ rowWithin raw rawMember
    omega
  · simpa using columnWithin

def Run.packedArithmetic (radix : Nat) (data : Run) : Nat :=
  if data.values.size = 0 then 0 else
  let standard := radix ^ data.values.size
  let extent := standard ^ data.count
  let geometric := (extent - 1) / (standard - 1)
  let moment := (data.count * extent + 1 - (geometric + extent)) / (standard - 1)
  (((Nat.ofDigits radix data.values.toList : Nat) : Int) * geometric +
    data.stride * (((standard - 1) / (radix - 1) : Nat) : Int) * moment).toNat

theorem packedArithmetic_eq (radix : Nat) (positive : 1 < radix) (data : Run)
    (valid : data.valid radix = true) (nonempty : 0 < data.values.size) :
    data.packedArithmetic radix = data.packed radix := by
  have big : 1 < radix ^ data.values.size := one_lt_pow₀ positive (by omega)
  simp only [Run.packedArithmetic, ite_eq_right (Nat.ne_of_gt nonempty)]
  rw [geometric_closed _ _ big, moment_closed _ _ big, geometric_closed _ _ positive]
  rw [← packed_linear radix data valid, Int.toNat_natCast]

theorem packedArithmetic_digit (radix : Nat) (positive : 1 < radix) (data : Run)
    (valid : data.valid radix = true) (index : Nat) (within : index < data.length) :
    digit radix (data.packedArithmetic radix) index = data.value index := by
  have nonempty : 0 < data.values.size := by unfold Run.length at within; nlinarith
  rw [packedArithmetic_eq radix positive data valid nonempty]
  exact packed_digit radix positive data valid index within

end Airbender.Setup.Proofs.PackedSignedRun
