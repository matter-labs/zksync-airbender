import Airbender.Proofs.Keccak.SplitParityNativeQueries
import Airbender.Review.Trace.Workers.Keccak.SplitNative
import Airbender.Proofs.Arithmetic.Nibbles
import Mathlib.Tactic.ReduceModChar

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 65536
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable [Fact babyBearModulus.Prime]

/-- One actual native parity read or write limb, including readonly refreshes. -/
def parityLaneLimb (cached writing : Bool) (w : Nat → ZMod babyBearModulus)
    (lane : Fin 6) (limb : Fin 4) : ZMod babyBearModulus :=
  let ports := (⟨.columnParity, w⟩ : Row babyBearModulus).ports cached
  let port := ports[2 + 2 * lane.val + limb.val / 2]'(by
    have size : ports.size = 14 := by cases cached <;> rfl
    rw [size]
    have := lane.isLt
    have := limb.isLt
    omega)
  let columns := if writing then port.writeValue.getD port.readValue else port.readValue
  (columns.evaluate w)[limb.val % 2]'(Nat.mod_lt _ (by decide))

/-- An actual queried nibble of the five live parity operands or their output. -/
def parityNibble (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (operand : Fin 6) (digit : Fin 16) : ZMod babyBearModulus :=
  (columnParityQueryEntry cached ⟨6 + digit.val, by omega⟩)[operand.val]'(by have := operand.isLt; omega)
    |>.eval (Verification.environment w)

/-- Each native written lane limb equals its four actual queried nibbles. -/
theorem parity_write_limb_packing (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (lane : Fin 6) (limb : Fin 4) :
    parityLaneLimb cached true w lane limb =
      parityNibble cached w lane ⟨4 * limb.val, by omega⟩ +
        16 * parityNibble cached w lane ⟨4 * limb.val + 1, by omega⟩ +
        256 * parityNibble cached w lane ⟨4 * limb.val + 2, by omega⟩ +
        4096 * parityNibble cached w lane ⟨4 * limb.val + 3, by omega⟩ := by
  cases cached <;> fin_cases lane <;> fin_cases limb <;>
    dsimp only [parityLaneLimb, parityNibble, Row.ports, WordColumns.evaluate,
      ColumnParity.importedConstraintsMemoryPorts, ColumnParityCached.importedConstraintsMemoryPorts,
      columnParityQueryEntry, columnParityQuery, ColumnParity.importedConstraints,
      ColumnParityCached.importedConstraints, FlatOperation.lookups, List.get, Expression.eval,
      Verification.environment] <;>
    norm_num [Fin.getElem_fin, Expression.eval, Verification.environment] <;> ring_nf <;>
    unfold babyBearModulus at * <;> reduce_mod_char <;> ring_nf <;> reduce_mod_char

/-- Native membership bounds all five nibble operands and the actual parity output. -/
theorem parity_nibble_bound (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable
        else ColumnParity.clockConstraints columnParityFixedTable)) (operand : Fin 6) (digit : Fin 16) :
    (parityNibble cached w operand digit).val < 16 := by
  have facts := column_parity_native_xor5_queries cached w holds digit
  by_cases input : operand.val < 5
  · simpa only [parityNibble, Vector.getElem_map] using facts.1 ⟨operand.val, input⟩
  · have same : operand.val = 5 := by have := operand.isLt; omega
    simpa only [parityNibble, Vector.getElem_map, same] using facts.2.1

/-- Each native written limb has its canonical bounded sixteen-bit nibble expansion. -/
theorem parity_write_limb_value (cached : Bool) (w : Nat → ZMod babyBearModulus)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (if cached then ColumnParityCached.clockConstraints columnParityFixedTable
        else ColumnParity.clockConstraints columnParityFixedTable)) (lane : Fin 6) (limb : Fin 4) :
    (parityLaneLimb cached true w lane limb).val < 65536 ∧
      (parityLaneLimb cached true w lane limb).val =
        (parityNibble cached w lane ⟨4 * limb.val, by omega⟩).val +
          16 * ((parityNibble cached w lane ⟨4 * limb.val + 1, by omega⟩).val +
            16 * ((parityNibble cached w lane ⟨4 * limb.val + 2, by omega⟩).val +
              16 * (parityNibble cached w lane ⟨4 * limb.val + 3, by omega⟩).val)) := by
  have h0 := parity_nibble_bound cached w holds lane ⟨4 * limb.val, by omega⟩
  have h1 := parity_nibble_bound cached w holds lane ⟨4 * limb.val + 1, by omega⟩
  have h2 := parity_nibble_bound cached w holds lane ⟨4 * limb.val + 2, by omega⟩
  have h3 := parity_nibble_bound cached w holds lane ⟨4 * limb.val + 3, by omega⟩
  have value := value_of_four_nibbles (by decide) h0 h1 h2 h3 (parity_write_limb_packing cached w lane limb)
  exact ⟨by rw [value]; omega, value⟩

end Airbender.Keccak.Split.Native.Proofs
