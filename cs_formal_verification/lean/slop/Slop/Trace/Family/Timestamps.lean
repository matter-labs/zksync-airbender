module
public import Slop.Trace.Timestamps
public import Human.Helpers.Context.FamilyLayout

@[expose] public section

namespace Airbender.Trace

@[simp] theorem family_ports (family : Family) :
    CircuitLayout.ports family = (match family with
      | .addSub => AddSub.importedConstraintsMemoryPorts
      | .wordMemory => WordMemory.importedConstraintsMemoryPorts) := by rfl

@[simp] theorem family_constraints [Fact p.Prime] (family : Family)
    (rom : Table (ZMod p) (fields 9)) :
    CircuitLayout.constraints family rom = (match family with
      | .addSub => AddSub.clockConstraints
      | .wordMemory => WordMemory.clockConstraints rom) := by
  cases family <;> rfl

end Airbender.Trace
