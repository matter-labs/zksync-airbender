import Slop.Delegation.RequestTrace
import Slop.Trace.TransferHistory
import Human.Helpers.Delegation.MixedMemory

namespace Airbender.Delegation.Caller.Proofs
open Trace Arithmetic Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384


theorem machine_port_native (row : Trace.Row p PooledFamily)
    {port : MemoryPort} (member : port ∈ machinePorts row) : port ∈ row.ports := by
  unfold machinePorts at member
  split at member
  next selected =>
    have family : row.family = .addSub := by
      cases equal : row.family <;> simp_all
    simp [architecturalPorts] at member
    rcases member with rfl | rfl
    all_goals simp [Trace.Row.ports, family, CircuitLayout.ports, AddSub.importedConstraintsMemoryPorts]
  next => exact member

end Airbender.Delegation.Caller.Proofs
