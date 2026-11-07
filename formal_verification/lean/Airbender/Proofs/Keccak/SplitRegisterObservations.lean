import Airbender.Review.Trace.Workers.Keccak.SplitNative
import Airbender.Proofs.Trace.UniqueObservation
import Airbender.Proofs.Trace.TransferHistory

namespace Airbender.Keccak.Split.Native.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option Elab.async false

/-- The actual first two native ports read registers ten and eleven. -/
def nativeRegisterPort (cached : Bool) (row : Row p) (index : Fin 2) : MemoryPort :=
  (row.ports cached)[index.val]'(by
    cases row with
    | mk kind assignment =>
      cases cached <;> cases kind
      all_goals have := index.isLt
      all_goals first
        | change index.val < 14; omega
        | change index.val < 16; omega
        | change index.val < 12; omega)

theorem native_register_port_mem (cached : Bool) (row : Row p) (index : Fin 2) :
    nativeRegisterPort cached row index ∈ row.ports cached :=
  Array.getElem_mem _

theorem native_register_port_address (cached : Bool) (row : Row p) (index : Fin 2) :
    (nativeRegisterPort cached row index).address = .constantRegister (10 + index.val) := by
  cases row with
  | mk kind assignment => cases cached <;> cases kind <;> fin_cases index <;> rfl

private def registerAddress (index : Nat) (address : MemoryAddress) : Bool :=
  match address with
  | .constantRegister actual => actual == index
  | _ => false

private def supportedAddress (address : MemoryAddress) : Bool :=
  match address with
  | .constantRegister _ | .indirect _ => true
  | _ => false

private theorem register_ports_filter (cached : Bool) (row : Row p) (index : Fin 2) :
    ((row.ports cached).toList.filter fun port => registerAddress (10 + index.val) port.address) =
      [nativeRegisterPort cached row index] := by
  cases row with
  | mk kind assignment => cases cached <;> cases kind <;> fin_cases index <;>
    dsimp only [nativeRegisterPort, Row.ports] <;> rfl

private theorem register_address_test (cached : Bool) (row : Row p) (index : Fin 2)
    (port : MemoryPort) (member : port ∈ row.ports cached) :
    decide (port.address.code row.assignment = Nat.pair 0 (Nat.pair (10 + index.val) 0)) =
      registerAddress (10 + index.val) port.address := by
  have checked : (row.ports cached).toList.all (fun port => supportedAddress port.address) = true := by
    cases row with
    | mk kind assignment => cases cached <;> cases kind <;> dsimp only [Row.ports] <;> decide +kernel
  have valid := List.all_eq_true.mp checked port (by simpa using member)
  cases address : port.address
  all_goals simp [address, supportedAddress] at valid
  all_goals apply Bool.eq_iff_iff.mpr
  all_goals simp [registerAddress, MemoryAddress.code, Nat.pair_eq_pair]

/-- Each control or pointer register occurs exactly once in the complete
native event list. Lane addresses may remain unknown at this point. -/
theorem native_register_events_filter (cached : Bool) (row : Row p) (index : Fin 2) :
    (((row.memorySteps cached).map transferEvent).filter fun event => decide
      (event.2.1 = (nativeRegisterPort cached row index).address.code row.assignment)) =
      [transferEvent (readToken row.assignment (nativeRegisterPort cached row index),
        row.writeToken cached (nativeRegisterPort cached row index))] := by
  rw [native_register_port_address]
  simp only [Row.memorySteps, List.map_map, Function.comp_def, List.filter_map]
  have filtered : ((row.ports cached).toList.filter fun port => decide
      ((transferEvent (readToken row.assignment port, row.writeToken cached port)).2.1 =
        (MemoryAddress.constantRegister (10 + index.val)).code row.assignment)) =
      [nativeRegisterPort cached row index] := by
    calc
      _ = (row.ports cached).toList.filter (fun port => registerAddress (10 + index.val) port.address) := by
        apply List.filter_congr
        intro port member
        exact register_address_test cached row index port (by simpa using member)
      _ = _ := register_ports_filter cached row index
  rw [filtered]
  rfl

/-- Initialized native history determines the actual control and pointer
reads before the call. No lane-distinctness premise is required. -/
theorem native_register_observation (cached : Bool) (row : Row p) (index : Fin 2)
    {cells : List Cell} {events : List MemoryAccess} {before after : State}
    (history : SailHistory cells events before after)
    (permutation : events.Perm ((row.memorySteps cached).map transferEvent))
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (initial : ∀ cell ∈ cells, ∃ value, cell.read before = .ok value before) :
    ∃ cell ∈ cells, cell.addressCode = (nativeRegisterPort cached row index).address.code row.assignment ∧
      cell.read before = .ok (readToken row.assignment (nativeRegisterPort cached row index)).word.toBitVec before := by
  have selected := permutation.filter fun event => decide
    (event.2.1 = (nativeRegisterPort cached row index).address.code row.assignment)
  rw [native_register_events_filter] at selected
  have single : (events.filter fun event => decide
      (event.2.1 = (nativeRegisterPort cached row index).address.code row.assignment)) =
      [transferEvent (readToken row.assignment (nativeRegisterPort cached row index),
        row.writeToken cached (nativeRegisterPort cached row index))] := by
    simpa using selected
  exact history_unique_address_read history aligned initial
    (transferEvent (readToken row.assignment (nativeRegisterPort cached row index),
      row.writeToken cached (nativeRegisterPort cached row index))) single

end Airbender.Keccak.Split.Native.Proofs
