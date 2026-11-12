module
public import Proven.Blake2G.NativeExecution
public import Proven.Blake2G.ControlPool
public import Proven.Delegation.CallGroups

@[expose] public section

namespace Airbender.Blake2G.Proofs
open Trace Trace.Proofs Delegation.Proofs
set_option warningAsError true

theorem call_event_time (row : Delegation.Row p) {port : MemoryPort} (present : port ∈ row.ports) :
    (transferEvent (readToken row.assignment port, row.writeToken port)).1 =
      (timeOfPair (row.writeToken importedConstraintsMemoryPorts[8]).time).value + 1 := by
  have same : (row.writeToken port).time = (row.writeToken importedConstraintsMemoryPorts[8]).time := by
    change (_, _) = (_, _)
    rw [port_offset row present]
    rfl
  simp only [transferEvent, same]

end Airbender.Blake2G.Proofs
