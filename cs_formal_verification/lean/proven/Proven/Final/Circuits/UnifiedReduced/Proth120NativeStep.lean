module
public import Human.Circuits.UnifiedReduced.Proth120NativeStep
public import Proven.Final.Circuits.UnifiedReduced.Proth120Native
public import Proven.Final.Circuits.UnifiedReduced.Proth120Execution
public import Proven.Constraints

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120

theorem native_step_soundness : NativeStepSoundnessClaim := by
  intro cells epoch before after physical w tables ctx arithmetic matched
  obtain ⟨holds, decoded⟩ := native_row _ _ tables physical w arithmetic matched
  apply row_soundness cells epoch w before after
  exact { ctx with
    constraints := Verification.holds_of_sublist holds (List.sublist_append_left _ _)
    decoded := decoded ctx.active }

theorem native_step_soundness_satisfiable : NativeStepSoundnessSatisfiableClaim :=
  ⟨_, _, _, _, _, _, Witness.nativeRows, Witness.fma_inputs.toRowContext,
    Witness.nativeArithmetic, Witness.nativeMatched⟩

end Airbender.UnifiedReduced.Proth120
