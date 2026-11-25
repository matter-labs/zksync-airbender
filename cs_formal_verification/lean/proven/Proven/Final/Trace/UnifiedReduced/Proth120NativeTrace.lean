module
public import Human.Trace.UnifiedReduced.Proth120NativeTrace
public import Proven.UnifiedReduced.Proth120.Permutation
public import Proven.UnifiedReduced.Proth120.TraceWitness
public import Proven.Final.Circuits.UnifiedReduced.Proth120Native
public import Proven.Final.Trace.UnifiedReduced.Proth120Trace

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open Trace

theorem native_trace_soundness : NativeTraceSoundnessClaim := by
  intro trace initial cells inputs
  have derived (row) (mem : row ∈ trace.rows) :
      FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints trace.rom) ∧
      (row.assignment row.columns.execute = 1 →
        PublicDecode {initial with pc := row.start.word.toBitVec} (isRead row)
          (nativeDecoderQuery row.columns row.decoderColumns row.assignment)) := by
    obtain ⟨lo, hi, active, publicRows, physical, arithmetic, matched⟩ := inputs.rows row mem
    exact native_row _ _ publicRows physical _ arithmetic matched
  apply trace_soundness trace initial cells
  · refine ⟨inputs.toTraceBoundary, ?_⟩
    intro row mem
    obtain ⟨lo, hi, active, _⟩ := inputs.rows row mem
    exact ⟨lo, hi, (derived row mem).2 active⟩
  · have cs := fun r hr => (derived r hr).1
    obtain ⟨states, memory⟩ := inputs.permutation.split inputs.image cs
    exact ⟨cs, fun r hr => (inputs.rows r hr).2.2.1, states, memory⟩

theorem native_trace_soundness_satisfiable : NativeTraceSoundnessSatisfiableClaim := by
  refine ⟨Witness.trace, Witness.initial, Witness.cells,
    ⟨Witness.trace_inputs.toTraceBoundary, WrapPermutation.of_parts Witness.trace_accepted.states Witness.trace_accepted.memory, ?_⟩,
    by simp [Witness.trace]⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨Witness.fma_inputs.fetch.1, Witness.fma_inputs.fetch.2, Witness.fma_inputs.active,
    ⟨Witness.nativeRows.generic, Witness.nativeRows.pooled,
      fun v h => Or.inl ⟨by decide +kernel, Witness.nativeRows.decoder v h⟩⟩, Witness.nativePhysical, Witness.nativeArithmetic, Witness.nativeMatched⟩

end Airbender.UnifiedReduced.Proth120
