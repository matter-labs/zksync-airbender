import Airbender.Proofs.Keccak.SplitParityControllerQuery
import Airbender.Proofs.Keccak.SplitParityLaneOperation
import Mathlib.Tactic.ReduceModChar

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable [Fact babyBearModulus.Prime]

/-- The three actual input limbs that the native circuit splits into bytes. -/
def parityIotaLimb (index : Fin 3) : Fin 4 :=
  ⟨if index.val < 2 then index.val else 3, by split <;> omega⟩

/-- The four native byte-iota query positions. -/
def parityIotaPosition (index : Fin 4) : Nat :=
  if index.val = 0 then 0 else if index.val = 1 then 1 else if index.val = 2 then 3 else 7

/-- One actual low input byte retained by the native byte split. -/
def parityIotaInputLow (w : Nat → ZMod babyBearModulus) (index : Fin 3) : ZMod babyBearModulus :=
  w (48 + index.val)

/-- One actual high input byte in its native iota query. -/
def parityIotaInputHigh (cached : Bool) (w : Nat → ZMod babyBearModulus) (index : Fin 3) :
    ZMod babyBearModulus :=
  (parityQueryRow cached w ⟨3 + index.val, by omega⟩)[0]

/-- One actual written first-lane byte, packed from its queried nibbles. -/
def parityIotaOutputByte (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (limb : Fin 4) (high : Bool) : ZMod babyBearModulus :=
  parityNibble cached w 0 ⟨4 * limb.val + if high then 2 else 0, by split <;> omega⟩ +
    16 * parityNibble cached w 0 ⟨4 * limb.val + (if high then 2 else 0) + 1, by split <;> omega⟩

/-- Each actual input byte split recombines to its native read limb. -/
theorem parity_iota_read_packing (cached : Bool) (w : Nat → ZMod babyBearModulus) (index : Fin 3) :
    parityLaneLimb cached false w 0 (parityIotaLimb index) =
      parityIotaInputLow w index + 256 * parityIotaInputHigh cached w index := by
  cases cached <;> fin_cases index <;>
    dsimp only [parityLaneLimb, parityIotaLimb, parityIotaInputLow, parityIotaInputHigh,
      parityQueryRow, Row.ports, WordColumns.evaluate,
      ColumnParity.importedConstraintsMemoryPorts, ColumnParityCached.importedConstraintsMemoryPorts,
      columnParityQueryEntry, columnParityQuery, ColumnParity.importedConstraints,
      ColumnParityCached.importedConstraints, FlatOperation.lookups, List.get, Expression.eval,
      Verification.environment] <;>
    norm_num [Fin.getElem_fin, Expression.eval, Verification.environment] <;> ring_nf <;>
    unfold babyBearModulus at * <;> reduce_mod_char <;> ring_nf <;> reduce_mod_char

/-- The actual written bytes recombine to the complete native written limb. -/
theorem parity_iota_write_packing (cached : Bool) (w : Nat → ZMod babyBearModulus) (limb : Fin 4) :
    parityLaneLimb cached true w 0 limb =
      parityIotaOutputByte cached w limb false + 256 * parityIotaOutputByte cached w limb true := by
  rw [parity_write_limb_packing]
  simp only [parityIotaOutputByte, Bool.false_eq_true, ite_true, ite_false,
    Nat.add_zero]
  ring

/-- The first actual iota query reads and writes the low byte of limb zero. -/
theorem parity_iota_low_query (cached : Bool) (w : Nat → ZMod babyBearModulus) :
    (parityQueryRow cached w 2)[0] = parityIotaInputLow w 0 ∧
      (parityQueryRow cached w 2)[2] = parityIotaOutputByte cached w 0 false := by
  cases cached <;> constructor <;>
    norm_num [parityIotaOutputByte] <;>
    dsimp only [parityIotaInputLow, parityIotaOutputByte, parityNibble, parityQueryRow,
      columnParityQueryEntry, columnParityQuery, ColumnParity.importedConstraints,
      ColumnParityCached.importedConstraints, FlatOperation.lookups, List.get, Expression.eval,
      Verification.environment] <;>
    norm_num [Fin.getElem_fin, Expression.eval, Verification.environment, ite_true, ite_false]

/-- The other three actual iota queries write the high bytes of their native limbs. -/
theorem parity_iota_high_query (cached : Bool) (w : Nat → ZMod babyBearModulus) (index : Fin 3) :
    (parityQueryRow cached w ⟨3 + index.val, by omega⟩)[2] =
      parityIotaOutputByte cached w (parityIotaLimb index) true := by
  cases cached <;> fin_cases index <;>
    norm_num [parityIotaOutputByte, parityIotaLimb] <;>
    dsimp only [parityIotaLimb, parityIotaOutputByte, parityNibble, parityQueryRow,
      columnParityQueryEntry, columnParityQuery, ColumnParity.importedConstraints,
      ColumnParityCached.importedConstraints, FlatOperation.lookups, List.get, Expression.eval,
      Verification.environment] <;>
    norm_num [Fin.getElem_fin, Expression.eval, Verification.environment, ite_true, ite_false] <;> ring_nf <;>
    unfold babyBearModulus at * <;> reduce_mod_char

/-- Every actual byte query uses the selected controller round and original byte position. -/
theorem parity_iota_query_control (cached : Bool) (w : Nat → ZMod babyBearModulus) (index : Fin 4) :
    (parityQueryRow cached w ⟨2 + index.val, by omega⟩)[1] =
      (parityQueryRow cached w 1)[3] + 32 * (parityIotaPosition index : ZMod babyBearModulus) := by
  cases cached <;> fin_cases index <;>
    dsimp only [parityIotaPosition, parityQueryRow, columnParityQueryEntry, columnParityQuery,
      ColumnParity.importedConstraints, ColumnParityCached.importedConstraints,
      FlatOperation.lookups, List.get, Expression.eval, Verification.environment] <;>
    norm_num [Fin.getElem_fin, Expression.eval, Verification.environment] <;> ring

/-- Every actual written byte has its canonical bounded nibble expansion. -/
theorem parity_iota_output_byte_value (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable
        else ColumnParity.clockConstraints columnParityFixedTable)) (limb : Fin 4) (high : Bool) :
    (parityIotaOutputByte cached w limb high).val < 256 := by
  have low := parity_nibble_bound cached w holds 0
    ⟨4 * limb.val + if high then 2 else 0, by split <;> omega⟩
  have upper := parity_nibble_bound cached w holds 0
    ⟨4 * limb.val + (if high then 2 else 0) + 1, by split <;> omega⟩
  have value := value_of_bounded_pair (radix := 16) (capacity := 16) (by decide) low upper
    (show _ = parityIotaOutputByte cached w limb high from rfl)
  rw [value]
  omega

end Airbender.Keccak.Split.Native.Proofs
