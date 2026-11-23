module
public import Proven.Keccak.ControlHistory
public import Proven.Keccak.NativeExecution
public import Proven.Keccak.PointerHistory
public import Proven.Delegation.CallGroups
public import Proven.Defs.Trace.Workers.Keccak.Call

@[expose] public section

namespace Airbender.Keccak.Proofs
open Trace Trace.Proofs Delegation.Proofs Arithmetic
set_option warningAsError true

theorem call_event_time (row : Delegation.Row p) {port : MemoryPort} (present : port ∈ row.ports) :
    (transferEvent (readToken row.assignment port, row.writeToken port)).1 = callWriteTime row + 1 := by
  have same : (row.writeToken port).time = (row.writeToken importedConstraintsMemoryPorts[0]).time := by
    change (_, _) = (_, _)
    rw [port_offset row present]
    rfl
  simp only [transferEvent, same, callWriteTime]

end Airbender.Keccak.Proofs
