import Human.Trace.Delegation.SharedSpans
import Slop.Blake2G.WorkVectorBinding
import Slop.Blake2Round.CompressionBinding
import Slop.Keccak.PermutationBinding

namespace Airbender.Delegation.Caller.Proofs
open Trace Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem span_keccak_control_cell [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {workers : MemoryData p} {before : State} {cells : List Cell}
    (accepted : MemoryAccepted workers) (inputs : MemoryInputs workers before cells)
    (protocol : HashSpan.Protocol workers before .keccak) : Cell.register 10 ∈ cells := by
  have nonempty : workers.rows ≠ [] := by
    intro empty
    have count := protocol.calls
    rw [empty] at count
    simp [HashSpan.callCount] at count
  obtain ⟨row, member⟩ := List.exists_mem_of_ne_nil workers.rows nonempty
  have family : row.family = .keccak := protocol.family row member
  have port : Keccak.importedConstraintsMemoryPorts[0] ∈ row.ports.toList := by
    simp [Row.ports, family, Keccak.importedConstraintsMemoryPorts]
  have edge : (readToken row.assignment Keccak.importedConstraintsMemoryPorts[0],
      row.writeToken Keccak.importedConstraintsMemoryPorts[0]) ∈ workers.steps :=
    List.mem_flatMap.mpr ⟨row, member, List.mem_map.mpr ⟨_, port, rfl⟩⟩
  obtain ⟨cell, present, same⟩ := Delegation.Proofs.initialized_cell hp accepted inputs.toBoundaryInputs edge
  have code : cell.addressCode = (Cell.register 10).addressCode := by
    simpa [readToken, Keccak.importedConstraintsMemoryPorts, MemoryAddress.code, Cell.addressCode] using same
  have equal := cell_address_injective code
  exact equal ▸ present

theorem hash_span_binding [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {workers : MemoryData p} {before : State} {cells : List Cell} {span : HashSpan}
    (accepted : MemoryAccepted workers) (inputs : MemoryInputs workers before cells)
    (protocol : HashSpan.Protocol workers before span)
    (active : ∀ row ∈ workers.rows, row.assignment row.columns.execute = 1)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    ∃ after, span.Result workers before after cells := by
  have rotationInverse : 64 * (-31457280 : ZMod p) = 1 := by linear_combination clockInverse
  have byteInverse : 256 * (-7864320 : ZMod p) = 1 := by linear_combination clockInverse
  cases span with
  | blakeG reduced =>
    have abi : Blake2G.CallInputs workers before cells reduced := by
      refine ⟨inputs, protocol.tables, protocol.family, ?_, protocol.controlStart, protocol.calls⟩
      intro row member
      have family := protocol.family row member
      have execution := active row member
      simpa [Row.columns, HashSpan.family, family, Blake2G.importedConstraintsDelegationColumns,
        Blake2G.Variables.execute] using execution
    obtain ⟨after, state, message, input, words, output, mapping, trace, result⟩ :=
      Blake2G.Proofs.workvector_binding (by omega) rotationInverse accepted abi aligned
    exact ⟨after, state, message, input, words, output, mapping, trace, result⟩
  | blakeRound flags =>
    have abi : Blake2Round.CallInputs workers before cells flags :=
      ⟨inputs, protocol.tables, protocol.family, protocol.controlStart, protocol.calls⟩
    obtain ⟨after, state, pointer, input, message, output, mapping, trace, result⟩ :=
      Blake2Round.Proofs.compression_binding (by omega) rotationInverse accepted abi aligned
    exact ⟨after, state, pointer, input, message, output, mapping, trace, result⟩
  | keccak =>
    have abi : Keccak.CallInputs workers before cells := by
      refine ⟨inputs, span_keccak_control_cell (by norm_num [timestampBase]; omega) accepted inputs protocol,
        protocol.controlStart, protocol.family, ?_, protocol.calls⟩
      intro row member
      have family := protocol.family row member
      have execution := active row member
      simpa [Row.columns, HashSpan.family, family, Keccak.importedConstraintsDelegationColumns,
        Keccak.Variables.execute] using execution
    obtain ⟨after, pointer, input, output, mapping, trace, result⟩ :=
      Keccak.Proofs.permutation_binding hp byteInverse accepted abi protocol.tables aligned
    exact ⟨after, pointer, input, output, mapping, trace, result⟩

theorem hash_span_result_mapping [Fact p.Prime]
    {workers : MemoryData p} {before after : State} {cells : List Cell} {span : HashSpan}
    (result : span.Result workers before after cells) : Delegation.TraceMapping workers before after cells := by
  cases span with
  | blakeG _ | blakeRound _ =>
    obtain ⟨_, _, _, _, _, _, trace, _⟩ := result
    exact trace
  | keccak =>
    obtain ⟨_, _, _, _, trace, _⟩ := result
    exact trace

end Airbender.Delegation.Caller.Proofs
