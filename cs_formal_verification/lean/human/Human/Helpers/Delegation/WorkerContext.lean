module
public import Human.Helpers.Delegation.Memory
public import Human.Helpers.Memory.RowEvents

@[expose] public section

namespace Airbender.Delegation
open Trace

/-- Canonical values observed at an imported port. The row supplies its family,
    placement-resolved columns and assignment; these observations impose no
    bounds or expected behavior. Shared history proves their actual RV values. -/
def Row.readWord (row : Row p) (index : Fin row.ports.size) : Arithmetic.Word :=
  (readToken row.assignment row.ports[index.val]).word

def Row.writtenWord (row : Row p) (index : Fin row.ports.size) : Arithmetic.Word :=
  (row.writeToken row.ports[index.val]).word

end Airbender.Delegation
