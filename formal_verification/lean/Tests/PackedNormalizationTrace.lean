import Airbender.Proofs.GKRProtocol.PackedNormalizationTrace

namespace Tests.PackedNormalizationTrace
open Airbender.Compiler.NumericPolynomialChecks
open PackedNormalization
set_option warningAsError true

def input : Data := [(3, [1, 0]), (5, [0, 1]), (6, []), (1, [2])]
def expected : Data := [(6, []), (1, [0, 1]), (1, [2])]
def encoded (terms : Data) : Packed := pack (KeyedNormalization.encodeRows terms)
def trace : List (Nat × Packed) := [
  (1, encoded expected),
  (1, encoded [(6, []), (5, [0, 1]), (1, [2])]),
  (0, encoded [(6, []), (1, [2])]),
  (0, encoded [(1, [2])]),
  (0, encoded [])]
def row : PolynomialRow := ⟨encoded expected, encoded input, trace⟩

theorem accepted : check 7 [row] = true := by decide +kernel

theorem binding : row.Binding expected input := by
  refine ⟨rfl, rfl, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · exact boundsCheck_sound _ (by decide +kernel)
  · exact boundsCheck_sound _ (by decide +kernel)

theorem original_normalization : normalize 7 input = expected :=
  check_sound 7 [row] accepted row (by simp) expected input binding

theorem coefficient_wrap : check 7 [⟨encoded [], encoded [(1, [0]), (6, [0])],
    [(0, encoded []), (0, encoded [(6, [0])]), (0, encoded [])]⟩] = true := by decide +kernel

def wrongPosition : PolynomialRow := {row with trace := (0, encoded expected) :: trace.tail}
def wrongInput : PolynomialRow := {row with input := encoded [(2, [1, 0]), (5, [0, 1]), (6, []), (1, [2])]}
def wrongExpected : PolynomialRow := {row with expected := encoded [(6, []), (2, [0, 1]), (1, [2])]}
def missingStep : PolynomialRow := {row with trace := trace.tail}
def extraStep : PolynomialRow := {row with trace := trace ++ [(0, encoded [])]}
def wrongLength : PolynomialRow := {row with input := ⟨input.length + 1, row.input.value⟩}

theorem wrong_position_rejected : check 7 [wrongPosition] = false := by decide +kernel
theorem wrong_input_rejected : check 7 [wrongInput] = false := by decide +kernel
theorem wrong_expected_rejected : check 7 [wrongExpected] = false := by decide +kernel
theorem missing_step_rejected : check 7 [missingStep] = false := by decide +kernel
theorem extra_step_rejected : check 7 [extraStep] = false := by decide +kernel
theorem wrong_length_rejected : check 7 [wrongLength] = false := by decide +kernel
theorem coefficient_bound_rejected : boundsCheck [(coefficientBase, 0)] = false := by decide +kernel
theorem key_bound_rejected : boundsCheck [(1, coefficientBase)] = false := by decide +kernel
theorem zero_modulus_rejected : check 0 [row] = false := by decide +kernel
theorem large_modulus_rejected : check (coefficientBase + 1) [row] = false := by decide +kernel

end Tests.PackedNormalizationTrace
