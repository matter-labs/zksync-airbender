module
public import Human.Circuits.AddSub.Modular.Model
public import Proven.AddSub.ArtifactChecks
public import Proven.AddSub.OpIndex
public import Proven.Arithmetic.Word
public import Proven.Arithmetic.Lemmas
public import Proven.Constraints
public import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace Airbender.AddSub.Proofs
open Airbender.Arithmetic

theorem modular_result_of_equations {input : Modular.Input} {output : Circuit.Output}
    {w : Nat → ZMod babyBearModulus}
    (interfaces : Modular.InterfaceAssumptions input output w)
    (mapping : Modular.WordMapping input output w)
    (nonzero : input.rd ≠ 0)
    (canonical : output.destination.value < babyBearModulus)
    (intermediate : (w 25 + 65536 * w 26) * (w 29 + 65536 * w 30) * 943718400 +
      (w 31 + 65536 * w 32) * w 16 - w 41 = 0)
    (result : (w 33 + 65536 * w 34 - (w 25 + 65536 * w 26 + w 29 + 65536 * w 30)) * w 13 +
      (w 33 + 65536 * w 34 - (w 25 + 65536 * w 26 - (w 29 + 65536 * w 30))) * w 14 +
      (w 33 + 65536 * w 34 - w 41) * (w 15 + w 16) = 0) :
    output.destination.value = (Modular.arithmeticResult input.opcode input.left input.right input.oldDestination).val := by
  have s13 := interfaces.selection 13 (by omega) (by omega)
  have s14 := interfaces.selection 14 (by omega) (by omega)
  have s15 := interfaces.selection 15 (by omega) (by omega)
  have s16 := interfaces.selection 16 (by omega) (by omega)
  have outputCast : (output.destination.value : ZMod babyBearModulus) = w 33 + 65536 * w 34 := by
    simp [Word.value, limbBase, mapping.outputLo, mapping.outputHi]
  simp only [mapping.left nonzero, mapping.right nonzero] at intermediate result
  simp only [ite_eq_right nonzero] at s13 s14 s15 s16
  have inverse : (943718400 : ZMod babyBearModulus) = (4294967296 : ZMod babyBearModulus)⁻¹ := by
    have unit : (943718400 : ZMod babyBearModulus) * 4294967296 = 1 := by decide
    have radixNonzero : (4294967296 : ZMod babyBearModulus) ≠ 0 := by decide
    calc
      (943718400 : ZMod babyBearModulus) =
          943718400 * (4294967296 * (4294967296 : ZMod babyBearModulus)⁻¹) := by
        rw [mul_inv_cancel₀ radixNonzero, mul_one]
      _ = _ := by rw [← mul_assoc, unit, one_mul]
  unfold Modular.arithmeticResult
  rw [← ZMod.val_natCast_of_lt canonical]
  apply congrArg ZMod.val
  rw [outputCast]
  cases hop : input.opcode <;>
    simp [hop, Modular.Opcode.selector] at s13 s14 s15 s16 ⊢
  · simp [s13, s14, s15, s16] at result
    linear_combination result + mapping.right nonzero
  · simp [s13, s14, s15, s16] at result
    linear_combination result
  · simp [s13, s14, s15, s16] at result intermediate
    rw [← inverse]
    linear_combination result - intermediate
  · simp [s13, s14, s15, s16, mapping.oldDestination nonzero hop] at result intermediate
    rw [← inverse]
    linear_combination result - intermediate


end Airbender.AddSub.Proofs
