module
public import Proven.UnifiedReduced.Proth120.PaddingWitness

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120

theorem padded_trace_soundness : PaddedTraceSoundnessClaim :=
  fun _ _ _ h => native_trace_soundness _ _ _ h.project

theorem padded_trace_soundness_satisfiable : PaddedTraceSoundnessSatisfiableClaim :=
  ⟨_, _, _, Witness.padded_inputs, rfl, rfl, rfl⟩

end Airbender.UnifiedReduced.Proth120
