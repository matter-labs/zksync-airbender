module
public import Human.Helpers.UnifiedReduced.RequestTrace
public import Human.Helpers.UnifiedReduced.Registry

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
