import Airbender.Proofs.Tables.PackedColumn
import Airbender.Proofs.Tables.PackedBitwise

namespace Airbender.Setup.Proofs.PackedWindows
open PackedColumn PackedBitwise
set_option warningAsError true

def window (row : Nat) : Nat :=
  expectedRow .bitAnd row + bytePower 256 * expectedRow .bitAnd (row + 1)

def span (origin length : Nat) : Nat :=
  (window (origin / 256) / bytePower (origin % 256)) % bytePower length

def legal (origin length : Nat) : Bool :=
  origin + length ≤ 65536 && origin % 256 + length ≤ 512

theorem window_low (row index : Nat) (rowBound : row < 256) (within : index < 256) :
    digit (window row) index = row &&& index := by
  have bounded : expectedRow .bitAnd row < 256 ^ 256 :=
    lt_of_le_of_lt Nat.and_le_left (by decide +kernel : indexPacked < 256 ^ 256)
  have reduced : window row % 256 ^ 256 = expectedRow .bitAnd row := by
    simp only [window, bytePower_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt bounded]
  have projected := segment_digit (window row) 0 256 index within
  simp only [Nat.pow_zero, Nat.div_one, Nat.zero_add, reduced] at projected
  rw [← projected]
  exact expected_byte .bitAnd row index rowBound within

theorem window_high (row index : Nat) (rowBound : row + 1 < 256) (within : index < 256) :
    digit (window row) (256 + index) = (row + 1) &&& index := by
  have bounded : expectedRow .bitAnd row < 256 ^ 256 :=
    lt_of_le_of_lt Nat.and_le_left (by decide +kernel : indexPacked < 256 ^ 256)
  have divided : window row / 256 ^ 256 = expectedRow .bitAnd (row + 1) := by
    simp only [window, bytePower_eq, Nat.add_mul_div_left _ _ (show 0 < 256 ^ 256 by positivity), Nat.div_eq_of_lt bounded, Nat.zero_add]
  unfold digit
  rw [pow_add, ← Nat.div_div_eq_div_mul, divided]
  exact expected_byte .bitAnd (row + 1) index rowBound within

theorem span_byte (origin length index : Nat) (accepted : legal origin length = true)
    (within : index < length) :
    digit (span origin length) index = (origin + index) / 256 &&& (origin + index) % 256 := by
  simp only [legal, Bool.and_eq_true, decide_eq_true_eq] at accepted
  have originParts := Nat.div_add_mod origin 256
  have totalParts := Nat.div_add_mod (origin + index) 256
  have projected := segment_digit (window (origin / 256)) (origin % 256) length index within
  simp only [span, bytePower_eq] at *
  rw [projected]
  by_cases first : origin % 256 + index < 256
  · have rowBound : origin / 256 < 256 := by omega
    rw [window_low (origin / 256) (origin % 256 + index) rowBound first]
    exact congrArg₂ Nat.land (by omega) (by omega)
  · have rowBound : origin / 256 + 1 < 256 := by omega
    have columnBound : origin % 256 + index - 256 < 256 := by omega
    have indexSplit : origin % 256 + index = 256 + (origin % 256 + index - 256) := by omega
    rw [indexSplit, window_high (origin / 256) _ rowBound columnBound]
    exact congrArg₂ Nat.land (by omega) (by omega)


end Airbender.Setup.Proofs.PackedWindows
