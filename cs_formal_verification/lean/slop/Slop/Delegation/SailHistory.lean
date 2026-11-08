import Slop.Delegation.History

namespace Airbender.Delegation.Proofs
open Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384


private def nonzeroPort (address : MemoryAddress) : Bool :=
  match address with
  | .constantRegister index => index != 0
  | .indirect _ => true
  | _ => false

theorem port_not_zero (row : Row p) {port : MemoryPort} (member : port ∈ row.ports) :
    port.address.code row.assignment ≠ (Cell.register 0).addressCode := by
  have checked : row.ports.toList.all (fun port => nonzeroPort port.address) = true := by
    cases row with
    | mk family w => cases family <;> dsimp only [Row.ports] <;> decide
  have valid := List.all_eq_true.mp checked port (by simpa using member)
  cases address : port.address
  all_goals simp [address, nonzeroPort] at valid
  all_goals first
    | simp [MemoryAddress.code, Cell.addressCode, Nat.pair_eq_pair] at valid ⊢
      exact valid
    | simp [MemoryAddress.code, Cell.addressCode, Nat.pair_eq_pair]

abbrev nativeEventClock (data : MemoryData p) :=
  Trace.Proofs.Transfer.nativeEventClock (transferData data)

theorem native_clock_roundtrip {data : MemoryData p} {event : MemoryAccess}
    (positive : event.1 ≠ 0) :
    relabelMemoryEvent (nativeEventClock data)
      (relabelMemoryEvent (eventClock data) event) = event :=
  Trace.Proofs.Transfer.native_clock_roundtrip (data := transferData data) positive

theorem labeled_events_split (data : MemoryData p) : labeledEvents data =
    List.append (α := MemoryAccess)
      (data.initial.map fun token => ((token.address, token.address, 0, token.value) : MemoryAccess))
      ((data.steps.map transferEvent).map (relabelMemoryEvent (eventClock data))) :=
  Trace.Proofs.Transfer.labeled_events_split (transferData data)

end Airbender.Delegation.Proofs
