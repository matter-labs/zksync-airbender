module
public import Human.Helpers.UnifiedReduced.RequestTrace
public import Human.Helpers.Memory.SailHistory
public import Human.Circuits.UnifiedReduced.Tables.Setup
public import Human.Circuits.JumpBranchSlt.Model
public import Human.Helpers.Memory.Native
public import Human.Helpers.Delegation.RequestEffects
public import Human.Helpers.Delegation.SharedMemory

@[expose] public section

namespace Airbender.UnifiedReduced.Caller
open Trace

/-- Caller rs1/rd access architectural x0. Its middle port carries the virtual
    CSR token and belongs to request matching, not initialized GPR/RAM history. -/
def architecturalPorts : Array MemoryPort :=
  #[importedConstraintsMemoryPorts[0], importedConstraintsMemoryPorts[2]]

/-- Ordinary standard/custom rows retain all three native ports. The imported
    caller selector excludes only the virtual port, with public decoding checked below. -/
def machinePorts (row : Trace.Row p UnifiedFamily) : Array MemoryPort :=
  if Selected row.assignment then architecturalPorts else row.ports

end Airbender.UnifiedReduced.Caller
