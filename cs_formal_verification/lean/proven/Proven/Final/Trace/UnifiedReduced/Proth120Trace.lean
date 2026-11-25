module
public import Proven.Final.Circuits.UnifiedReduced.Proth120Execution
public import Proven.Final.Circuits.UnifiedReduced.Proth120Input
public import Proven.UnifiedReduced.Proth120.TraceBoot
public import Proven.UnifiedReduced.Proth120.TraceComposition
public import Proven.UnifiedReduced.Proth120.TraceZero
public import Proven.UnifiedReduced.Proth120.TraceReadWitness

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120

theorem trace_soundness : TraceSoundnessClaim := by
  intro trace initial cells inputs accepted
  exact trace_of_rows row_soundness csr_row_soundness inputs accepted (zero_writes inputs accepted)

theorem trace_soundness_satisfiable : TraceSoundnessSatisfiableClaim :=
  ⟨CSRWitness.trace, CSRWitness.initial true, CSRWitness.cells, CSRWitness.trace_inputs,
    CSRWitness.trace_accepted, by decide +kernel⟩

end Airbender.UnifiedReduced.Proth120
