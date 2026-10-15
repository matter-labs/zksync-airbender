import Airbender.Review.Trace.UnifiedReduced.FullCalls
import Airbender.Proofs.Blake2G.ReferenceCalls
import Airbender.Proofs.Blake2Round.ReferenceCalls
import Airbender.Proofs.Keccak.ReferenceCalls
import Airbender.Proofs.UnifiedReduced.ComputedRoundRegions

namespace Airbender.UnifiedReduced.Caller.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000

theorem hash_span_call [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {workers : Delegation.MemoryData p} {initial before after : State} {domain historyCells : List Cell}
    {span : Delegation.Caller.HashSpan} {events : List MemoryAccess}
    (accepted : Delegation.MemoryAccepted workers)
    (inputs : Delegation.BoundaryMemoryInputs workers initial domain)
    (protocol : Delegation.Caller.HashSpan.Protocol workers initial span)
    (active : ∀ row ∈ workers.rows, row.assignment row.columns.execute = 1)
    (ram : ∀ address, Cell.ram address ∈ domain → ROM.limit ≤ address.toNat)
    {row : Delegation.Row p} (member : row ∈ workers.rows)
    (history : SailHistory historyCells events before after)
    (permutation : events.Perm (row.memorySteps.map transferEvent))
    (observed : ∀ port ∈ row.ports, ∃ cell : Cell,
      cell.addressCode = port.address.code row.assignment ∧
        cell.read before = .ok (readToken row.assignment port).word.toBitVec before) :
    FullCall row.family before after := by
  have rotationInverse : 64 * (-31457280 : ZMod p) = 1 := by linear_combination clockInverse
  have byteInverse : 256 * (-7864320 : ZMod p) = 1 := by linear_combination clockInverse
  have family := protocol.family row member
  cases span with
  | blakeG reduced =>
    have publicABI : Blake2G.NativeCallInputs workers initial domain reduced := by
      refine ⟨inputs, protocol.tables, protocol.family, ?_, protocol.controlStart, protocol.calls⟩
      intro row member
      have family := protocol.family row member
      simpa [Delegation.Row.columns, Delegation.Caller.HashSpan.family, family,
        Blake2G.importedConstraintsDelegationColumns, Blake2G.Variables.execute] using active row member
    rw [family]
    exact Blake2G.Call.Proofs.step_in_span (by omega) rotationInverse accepted
      publicABI.toBoundaryInputs ram member history permutation observed
  | blakeRound flags =>
    have publicABI : Blake2Round.NativeCallInputs workers initial domain flags :=
      ⟨inputs, protocol.tables, protocol.family, protocol.controlStart, protocol.calls⟩
    rw [family]
    exact Blake2Round.Call.Proofs.step_in_span (by omega) rotationInverse accepted
      publicABI.toBoundaryInputs ram member history permutation observed
  | keccak =>
    have publicABI : Keccak.NativeCallInputs workers initial domain := by
      refine ⟨inputs, protocol.controlStart, protocol.family, ?_, protocol.calls⟩
      intro row member
      have family := protocol.family row member
      simpa [Delegation.Row.columns, Delegation.Caller.HashSpan.family, family,
        Keccak.importedConstraintsDelegationColumns, Keccak.Variables.execute] using active row member
    rw [family]
    exact Keccak.Call.Proofs.step_in_span hp byteInverse accepted
      (publicABI.toBoundaryInputs (by norm_num [timestampBase]; omega) accepted)
      protocol.tables ram member history permutation observed

theorem computed_window_call [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {data : RequestTrace p} {initial before after : State} {ca oa : List (BitVec 32)}
    {cells historyCells : List Cell} {program : List UnifiedReduced.ProgramEntry}
    {window : HashWindow} {events : List MemoryAccess}
    (accepted : MixedMemoryAccepted data program)
    (inputs : MixedMemoryInputs data program initial ca oa cells)
    (scope : ComputedProtocolWindowInputs data program window)
    (first : window.lower % 4 = 0) (last : window.upper % 4 = 0)
    (ram : ∀ address, Cell.ram address ∈ cells → ROM.limit ≤ address.toNat)
    {row : Delegation.Row p} (member : row ∈ data.workers.windowRows window.lower window.upper)
    (history : SailHistory historyCells events before after)
    (permutation : events.Perm (row.memorySteps.map transferEvent))
    (observed : ∀ port ∈ row.ports, ∃ cell : Cell,
      cell.addressCode = port.address.code row.assignment ∧
        cell.read before = .ok (readToken row.assignment port).word.toBitVec before) :
    FullCall row.family before after := by
  have rotationInverse : 64 * (-31457280 : ZMod p) = 1 := by linear_combination clockInverse
  have floor := hash_control_preparation_after_initial scope.preparation
  have duration := scope.duration
  have projection := mixed_projected_window (by omega) clockInverse rotationInverse accepted inputs first last
    (by omega) (by omega) (by omega) scope.beforeTerminal (by simpa only [scope.calls] using duration)
  obtain ⟨start, finish, earlierEvents, spanEvents, atStart, atFinish, _, _, _, _,
    prefixMatching, _, startBoundary, _, selected, initialized, _, _⟩ := projection.execution
  have control := hash_control_preparation_at_boundary (by omega) clockInverse accepted inputs scope.preparation
    first prefixMatching startBoundary
  have entry : (Cell.register window.span.controlRegister).read atStart = .ok window.span.controlStart atStart := by
    simpa only [hash_preparation_value] using control.1
  have protocol : Delegation.Caller.HashSpan.Protocol (data.windowProjection window.lower window.upper start finish)
      atStart window.span := ⟨inputs.tables, scope.family, entry, scope.calls⟩
  exact hash_span_call hp clockInverse selected initialized protocol
    (fun row member => accepted.workerActive row (List.mem_of_mem_filter member))
    (fun address member => ram address (List.mem_of_mem_filter member)) member history permutation observed

end Airbender.UnifiedReduced.Caller.Proofs
