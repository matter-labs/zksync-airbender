module
public import Human.Helpers.Core.CircuitField
public import Proven.Arithmetic.Lemmas
public import Proven.AddSub.Modular.RVArithmetic
public import Proven.Arithmetic.Word

@[expose] public section
namespace Airbender.UnifiedReduced.Modular.Quotient
open Arithmetic

variable {host : Nat} [CircuitField host]

local notation "Outer" => ZMod host
local notation "Inner" => ZMod babyBearModulus

/-- Lift the wrap's addition quotient equation to the integers, then reduce it modulo BabyBear. -/
theorem add_residue {a b out q : Nat} (capacity : 2^67 ≤ host)
    (ha : a < 2^32) (hb : b < 2^32) (ho : out < babyBearModulus) (hq : q < 8)
    (equation : (a : Outer) + b = out + 2013265921 * q) :
    (out : Inner) = a + b := by
  have eq := bounded_nat_eq (F := Outer) (p := host)
    (a := a + b) (b := out + 2013265921 * q)
    (by omega)
    (by unfold babyBearModulus at ho; omega)
    (by push_cast; exact equation)
  have h := congrArg (fun n : Nat => (n : Inner)) eq
  simpa [show (2013265921 : Inner) = 0 from ZMod.natCast_self babyBearModulus] using h.symm

/-- The subtraction branch adds three moduli so every permitted source word has a nonnegative representative. -/
theorem sub_residue {a b out q : Nat} (capacity : 2^67 ≤ host)
    (ha : a < 2^32) (hb : b < 2^32) (ho : out < babyBearModulus) (hq : q < 8)
    (equation : (a : Outer) + 6039797763 = b + out + 2013265921 * q) :
    (out : Inner) = a - b := by
  have eq := bounded_nat_eq (F := Outer) (p := host)
    (a := a + 6039797763) (b := b + out + 2013265921 * q)
    (by omega)
    (by unfold babyBearModulus at ho; omega)
    (by push_cast; exact equation)
  have h := congrArg (fun n : Nat => (n : Inner)) eq
  have shifted : (6039797763 : Inner) = 0 := by decide +kernel
  simp [shifted, show (2013265921 : Inner) = 0 from ZMod.natCast_self babyBearModulus] at h
  linear_combination -h

/-- The product branch encodes a 35-bit quotient and a canonical 32-bit output.
    Both sides are below the Proth120 modulus, so reducing in BabyBear preserves the equation. -/
theorem mul_residue {a b old out q : Nat} (capacity : 2^67 ≤ host)
    (ha : a < 2^32) (hb : b < 2^32) (hd : old < 2^32)
    (ho : out < babyBearModulus) (hq : q < 2^35)
    (equation : (a : Outer) * b + 4294967296 * old + 8646911288846319616 =
      2013265921 * q + 4294967296 * out) :
    (out : Inner) = a * b * (4294967296 : Inner)⁻¹ + old := by
  have product : a * b ≤ (2^32) * (2^32) := Nat.mul_le_mul ha.le hb.le
  have eq := bounded_nat_eq (F := Outer) (p := host)
    (a := a * b + 4294967296 * old + 8646911288846319616)
    (b := 2013265921 * q + 4294967296 * out)
    (by omega)
    (by unfold babyBearModulus at ho; omega)
    (by push_cast; exact equation)
  have h := congrArg (fun n : Nat => (n : Inner)) eq
  have bias : (8646911288846319616 : Inner) = 0 := by decide +kernel
  simp [bias, show (2013265921 : Inner) = 0 from ZMod.natCast_self babyBearModulus] at h
  have unit : (4294967296 : Inner) * (4294967296 : Inner)⁻¹ = 1 :=
    mul_inv_cancel₀ (by decide +kernel)
  linear_combination -((4294967296 : Inner)⁻¹ * h) - ((out : Inner) - old) * unit

/-- The quotient low word is range-checked by the two added Proth120 lookups.
    The high three bits are shared Boolean witness columns. -/
theorem row_residue (capacity : 2^67 ≤ host) (op : AddSub.Modular.Opcode) (left right old out : Word)
    (hl : left.Bounded) (hr : right.Bounded) (hd : old.Bounded)
    (canonical : out.value < babyBearModulus)
    {qLow qHigh : Nat} (qLowBound : qLow < 2^32) (qHighBound : qHigh < 8)
    {scratch : Outer}
    (prod :
      (left.value : Outer) * right.value + 4294967296 * (if op = .fma then (old.value : Outer) else 0) +
        8646911288846319616 -
        2013265921 * (qLow + 4294967296 * (qHigh : Outer)) * (if op = .mul ∨ op = .fma then 1 else 0) -
        4294967296 * scratch = 0)
    (selected : match op with
      | .add => (left.value : Outer) + right.value = out.value + 2013265921 * qHigh
      | .sub => (left.value : Outer) + 6039797763 = right.value + out.value + 2013265921 * qHigh
      | .mul | .fma => (out.value : Outer) = scratch) :
    (out.value : Inner) = AddSub.Modular.arithmeticResult op left.toBitVec right.toBitVec old.toBitVec := by
  have ha := Word.value_lt hl
  have hb := Word.value_lt hr
  have ho := Word.value_lt hd
  cases op <;> simp only [AddSub.Modular.arithmeticResult, Word.toBitVec_toNat hl,
    Word.toBitVec_toNat hr, Word.toBitVec_toNat hd]
  · exact add_residue capacity ha hb canonical qHighBound selected
  · exact sub_residue capacity ha hb canonical qHighBound selected
  · have h := mul_residue (old := 0) (q := qLow + 4294967296 * qHigh) capacity ha hb (by decide)
      canonical (by omega)
    simp only [reduceCtorEq, ↓reduceIte, true_or, mul_zero, add_zero, mul_one] at prod
    apply (by simpa only [Nat.cast_zero, add_zero] using h : _ → _)
    push_cast
    linear_combination prod - 4294967296 * selected
  · apply mul_residue (q := qLow + 4294967296 * qHigh) capacity ha hb ho canonical (by omega)
    simp only [↓reduceIte, or_true, mul_one] at prod
    push_cast
    linear_combination prod - 4294967296 * selected

end Airbender.UnifiedReduced.Modular.Quotient
