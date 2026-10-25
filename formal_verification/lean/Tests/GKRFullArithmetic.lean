import GKRProtocol.FullArithmeticNative.AddSubCached

namespace Tests.GKRFullArithmetic
open Airbender Airbender.Compiler
open Airbender.Compiler.FullArithmeticNative.AddSubCached
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

private noncomputable def badExtension (coordinate : Fin 58) : Polynomial 48 Source.BaseField :=
  if coordinate.val = 48 then Compiler.constant 0 else native.artifact.extension coordinate

theorem bad_computed_value_still_preserves_inputs :
    (List.finRange 48).all (fun wire =>
      equal (badExtension (native.artifact.projection wire)) (Compiler.atom wire)) = true := by decide +kernel

theorem rejects_bad_computed_value :
    (List.finRange native.artifact.gates.length).any (fun index =>
      !equal (substitute badExtension (native.artifact.gates.get index).inputResidual)
        (combination native.artifact.source (native.certificate.forward index))) = true := by decide +kernel

theorem rejects_dropped_helper_boolean :
    equal (rename native.artifact.projection (native.artifact.source.get ⟨27, by decide⟩))
      (combination (native.artifact.translation.lowered.set 36 [])
        (native.certificate.backward ⟨27, by decide⟩)) = false := by decide +kernel

/-- The new backward theorem supplies the borrow bit needed by timestamp
soundness; it is not an additional assumption on an accepted native row. -/
theorem derives_borrow_bit_from_native (values : Fin 58 → Source.BaseField)
    (holds : ∀ gate ∈ native.artifact.gates, gate.expressionResidual values = 0) :
    let helpers := native.helperPlacement.project (values ∘ native.artifact.projection)
    helpers.borrow 0 * (helpers.borrow 0 - 1) = 0 := by
  have preserved := native.full_arithmetic_preserved values holds
  have bit := preserved _ (List.get_mem native.artifact.source ⟨27, by decide⟩)
  change evaluate (values ∘ native.artifact.projection)
    ((Source.HelperAssertion.boolean (.borrow 0)).polynomial native.helperPlacement) = 0 at bit
  rw [Source.HelperAssertion.polynomial_value] at bit
  exact bit

theorem materializes_actual_input_cells (values : Fin 48 → Source.BaseField)
    (holds : Satisfies native.artifact.source values) (fallback : GKRAddress → Source.BaseField) (wire : Fin 48) :
    native.bank.materialize (native.artifact.translation.extend values) fallback (native.inputBank.address wire) = values wire := by
  exact WireBank.materialize_source_input native.bank native.inputBank native.artifact.projection
    native.inputCoordinates native.bankRoundTrip values _ (native.full_arithmetic_extends values holds).1 fallback wire

end Tests.GKRFullArithmetic
