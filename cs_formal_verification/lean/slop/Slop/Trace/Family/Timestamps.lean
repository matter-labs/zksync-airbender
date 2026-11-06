import Slop.Trace.Timestamps

namespace Airbender.Trace

@[simp] theorem family_columns (family : Family) :
    CircuitLayout.columns family = (match family with
      | .addSub => AddSub.importedConstraintsTraceColumns
      | .wordMemory => WordMemory.importedConstraintsTraceColumns) := rfl

@[simp] theorem family_ports (family : Family) :
    CircuitLayout.ports family = (match family with
      | .addSub => AddSub.importedConstraintsMemoryPorts
      | .wordMemory => WordMemory.importedConstraintsMemoryPorts) := rfl

@[simp] theorem family_decoder_columns (family : Family) :
    CircuitLayout.decoderColumns family = (match family with
      | .addSub => AddSub.importedConstraintsDecoderColumns
      | .wordMemory => WordMemory.importedConstraintsDecoderColumns) := rfl

@[simp] theorem family_constraints [Fact p.Prime] (family : Family)
    (rom : Table (ZMod p) (fields 9)) :
    CircuitLayout.constraints family rom = (match family with
      | .addSub => AddSub.clockConstraints
      | .wordMemory => WordMemory.clockConstraints rom) := by
  cases family <;> rfl

end Airbender.Trace
