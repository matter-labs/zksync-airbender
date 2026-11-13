module
public import Human.Circuits.ShiftBinop.Artifact
import all Init.Data.Repr -- Init.Data.Repr is not exposed (still true in 4.35)
public import Proven.CleanCore.Circuit.Operations

@[expose] public section

namespace Airbender.ShiftBinop

theorem timestamp_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraintsTimestampLookups (p := p))).length = 8 := by rfl

theorem memory_clocks : importedConstraintsMemoryPorts.map Trace.MemoryPort.clock =
    importedConstraintsTraceColumns.ports := by
  simp [importedConstraintsMemoryPorts, importedConstraintsTraceColumns]

theorem constraint_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.constraints (importedConstraints (p := p))).length = 52 := by rfl

theorem lookup_count {p : Nat} [Fact p.Prime] :
    (FlatOperation.lookups (importedConstraints (p := p))).length = 7 := by rfl

end Airbender.ShiftBinop
