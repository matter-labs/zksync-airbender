import Airbender.Proofs.Tables.PackedRun

namespace Airbender.Setup.Proofs.PackedRun
open PackedColumn
set_option warningAsError true

theorem ones_succ (standard count : Nat) :
    ones standard (count + 1) = ones standard count + standard ^ count := by
  simp [ones, List.replicate_succ', Nat.ofDigits_append, Nat.ofDigits]

theorem positions_succ (standard count : Nat) :
    positions standard (count + 1) = positions standard count + standard ^ count * count := by
  simp [positions, List.range_succ, Nat.ofDigits_append, Nat.ofDigits]

theorem geometric_identity (standard count : Nat) (positive : 1 ≤ standard) :
    ones standard count * (standard - 1) + 1 = standard ^ count := by
  have splitStandard : standard - 1 + 1 = standard := Nat.sub_add_cancel positive
  induction count with
  | zero => simp [ones]
  | succ count ih =>
    rw [ones_succ, pow_succ]
    calc
      (ones standard count + standard ^ count) * (standard - 1) + 1 =
          (ones standard count * (standard - 1) + 1) + standard ^ count * (standard - 1) := by ring
      _ = standard ^ count + standard ^ count * (standard - 1) := by rw [ih]
      _ = standard ^ count * ((standard - 1) + 1) := by ring
      _ = standard ^ count * standard := by rw [splitStandard]

theorem moment_identity (standard count : Nat) (positive : 1 ≤ standard) :
    positions standard count * (standard - 1) + ones standard count + standard ^ count =
      count * standard ^ count + 1 := by
  have splitStandard : standard - 1 + 1 = standard := Nat.sub_add_cancel positive
  induction count with
  | zero => simp [positions, ones]
  | succ count ih =>
    rw [positions_succ, ones_succ, pow_succ]
    calc
      (positions standard count + standard ^ count * count) * (standard - 1) +
          (ones standard count + standard ^ count) + standard ^ count * standard =
          (positions standard count * (standard - 1) + ones standard count + standard ^ count) +
            count * standard ^ count * (standard - 1) + standard ^ count * standard := by ring
      _ = (count * standard ^ count + 1) + count * standard ^ count * (standard - 1) +
          standard ^ count * standard := by rw [ih]
      _ = count * standard ^ count * ((standard - 1) + 1) +
          standard ^ count * standard + 1 := by ring
      _ = (count + 1) * (standard ^ count * standard) + 1 := by rw [splitStandard]; ring

theorem geometric_closed (standard count : Nat) (positive : 1 < standard) :
    (standard ^ count - 1) / (standard - 1) = ones standard count := by
  have identity := geometric_identity standard count (by omega)
  have product : standard ^ count - 1 = ones standard count * (standard - 1) := by omega
  rw [product]
  simp [Nat.ne_of_gt (show 0 < standard - 1 by omega)]

theorem moment_closed (standard count : Nat) (positive : 1 < standard) :
    (count * standard ^ count + 1 - (ones standard count + standard ^ count)) /
      (standard - 1) = positions standard count := by
  have identity := moment_identity standard count (by omega)
  have product : count * standard ^ count + 1 - (ones standard count + standard ^ count) =
      positions standard count * (standard - 1) := by omega
  rw [product]
  simp [Nat.ne_of_gt (show 0 < standard - 1 by omega)]

/-- Evaluate repetitions with a fixed number of large-integer operations.
The source pattern remains unchanged. No repetition is unfolded by the checker. -/
def Run.packedArithmetic (data : Run) : Nat :=
  if data.values.size = 0 then 0 else
  let standard := bytePower data.values.size
  let extent := bytePower data.length
  let geometric := (extent - 1) / (standard - 1)
  let moment := (data.count * extent + 1 - (geometric + extent)) / (standard - 1)
  (Nat.ofDigits 256 data.values.toList) * geometric +
    (data.stride * ((standard - 1) / 255)) * moment

theorem packedArithmetic_eq (data : Run) (positive : 0 < data.values.size) :
    data.packedArithmetic = data.packed := by
  have big : 1 < 256 ^ data.values.size := one_lt_pow₀ (by omega) (by omega)
  have total : (256 ^ data.values.size) ^ data.count =
      256 ^ (data.count * data.values.size) := by rw [← pow_mul, Nat.mul_comm]
  simp only [Run.packedArithmetic, if_neg (Nat.ne_of_gt positive), bytePower_eq, Run.length]
  rw [← total, geometric_closed _ _ big, moment_closed _ _ big]
  have units := geometric_closed 256 data.values.size (by omega)
  norm_num only [show 256 - 1 = 255 from rfl] at units
  rw [units]
  rfl

theorem packedArithmetic_byte (data : Run) (valid : data.valid = true)
    (index : Nat) (within : index < data.length) :
    digit data.packedArithmetic index = data.value index := by
  have positive : 0 < data.values.size := by unfold Run.length at within; nlinarith
  rw [packedArithmetic_eq data positive]
  exact packed_byte data valid index within

end Airbender.Setup.Proofs.PackedRun
