import Human.Trace.UnifiedReduced.RVHashSpans
import Slop.Blake2G.RVWindows
import Slop.Blake2Round.RVWindows
import Slop.Keccak.RVWindows
import Slop.Delegation.RVCallHistory

/-! RV sibling of `Delegation/SpanBinding.lean`: a complete G, extended-BLAKE or Keccak span from public RV
    initialization reaches its RV span result (delegate link included), by the worker families' RV bindings. -/

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Delegation.Caller
set_option warningAsError true
set_option maxRecDepth 16384

theorem rv_span_keccak_control_cell [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {workers : Delegation.MemoryData p} {before : RV.State} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted workers) (inputs : Delegation.RVMemoryInputs workers before cells)
    (protocol : RVHashSpanProtocol workers before .keccak) : Cell.register 10 ∈ cells := by
  have nonempty : workers.rows ≠ [] := by
    intro empty
    have count := protocol.calls
    rw [empty] at count
    simp [HashSpan.callCount] at count
  obtain ⟨row, member⟩ := List.exists_mem_of_ne_nil workers.rows nonempty
  have family : row.family = .keccak := protocol.family row member
  have port : Keccak.importedConstraintsMemoryPorts[0] ∈ row.ports.toList := by
    simp [Delegation.Row.ports, family, Keccak.importedConstraintsMemoryPorts]
  have edge : (readToken row.assignment Keccak.importedConstraintsMemoryPorts[0],
      row.writeToken Keccak.importedConstraintsMemoryPorts[0]) ∈ workers.steps :=
    List.mem_flatMap.mpr ⟨row, member, List.mem_map.mpr ⟨_, port, rfl⟩⟩
  obtain ⟨cell, present, same⟩ := Delegation.Proofs.seed_initialized_cell hp accepted
    inputs.toRVBoundaryInputs.toSeed edge
  have code : cell.addressCode = (Cell.register 10).addressCode := by
    simpa [readToken, Keccak.importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode] using same
  have equal := cell_address_injective code
  exact equal ▸ present

theorem rv_hash_span_binding [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {workers : Delegation.MemoryData p} {before : RV.State} {cells : List Cell} {span : HashSpan}
    (accepted : Delegation.MemoryAccepted workers) (inputs : Delegation.RVMemoryInputs workers before cells)
    (protocol : RVHashSpanProtocol workers before span)
    (active : ∀ row ∈ workers.rows, row.assignment row.columns.execute = 1)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ after, rvSpanResult span workers before after cells := by
  have rotationInverse : 64 * (-31457280 : ZMod p) = 1 := by linear_combination clockInverse
  have byteInverse : 256 * (-7864320 : ZMod p) = 1 := by linear_combination clockInverse
  cases span with
  | blakeG reduced =>
    have abi : Blake2G.RVCallInputs workers before cells reduced := by
      refine ⟨inputs, protocol.tables, protocol.family, ?_, protocol.controlStart, protocol.calls⟩
      intro row member
      have family := protocol.family row member
      have execution := active row member
      simpa [Delegation.Row.columns, HashSpan.family, family, Blake2G.importedConstraintsDelegationColumns,
        Blake2G.Variables.execute] using execution
    obtain ⟨after, result⟩ := Blake2G.Proofs.rv_workvector_binding_at_boundary (by omega) rotationInverse accepted
      (Blake2G.Proofs.RVCallInputs.toRVBoundary abi) aligned
    exact ⟨after, result⟩
  | blakeRound flags =>
    have abi : Blake2Round.RVCallInputs workers before cells flags :=
      ⟨inputs, protocol.tables, protocol.family, protocol.controlStart, protocol.calls⟩
    obtain ⟨after, result⟩ := Blake2Round.Proofs.rv_compression_binding_at_boundary (by omega) rotationInverse
      accepted (Blake2Round.Proofs.RVCallInputs.toRVBoundary abi) aligned
    exact ⟨after, result⟩
  | keccak =>
    have abi : Keccak.RVCallInputs workers before cells := by
      refine ⟨inputs, rv_span_keccak_control_cell (by norm_num [timestampBase]; omega) accepted inputs protocol,
        protocol.controlStart, protocol.family, ?_, protocol.calls⟩
      intro row member
      have family := protocol.family row member
      have execution := active row member
      simpa [Delegation.Row.columns, HashSpan.family, family, Keccak.importedConstraintsDelegationColumns,
        Keccak.Variables.execute] using execution
    obtain ⟨after, result⟩ := Keccak.Proofs.rv_permutation_binding_at_boundary hp byteInverse accepted
      abi.toRVBoundary protocol.tables aligned
    exact ⟨after, result⟩

theorem rv_hash_span_result_mapping [Fact p.Prime]
    {workers : Delegation.MemoryData p} {before after : RV.State} {cells : List Cell} {span : HashSpan}
    (result : rvSpanResult span workers before after cells) :
    Delegation.RVTraceMapping workers before after cells := by
  cases span with
  | blakeG _ | blakeRound _ =>
    obtain ⟨_, _, _, _, _, _, trace, _⟩ := result
    exact trace
  | keccak =>
    obtain ⟨_, _, _, ⟨_, trace, _⟩⟩ := result
    exact trace

end Airbender.UnifiedReduced.Caller.Proofs
