import Human.Circuits.AddSub.Artifact
import Human.Circuits.WordMemory.Artifact
import Human.Helpers.Context.Model

namespace Airbender.Trace

/-- The restricted scope's registry entries (`Family`, in `Model.lean`): each family's imported artifact. Kept apart
    from the generic model so that only the modules that use these two artifacts are rebuilt when they change. -/
instance : CircuitLayout Family where
  columns
    | .addSub => AddSub.importedConstraintsTraceColumns
    | .wordMemory => WordMemory.importedConstraintsTraceColumns
  ports
    | .addSub => AddSub.importedConstraintsMemoryPorts
    | .wordMemory => WordMemory.importedConstraintsMemoryPorts
  decoderColumns
    | .addSub => AddSub.importedConstraintsDecoderColumns
    | .wordMemory => WordMemory.importedConstraintsDecoderColumns
  constraints
    | .addSub, _ => AddSub.clockConstraints
    | .wordMemory, rom => WordMemory.clockConstraints rom

end Airbender.Trace
