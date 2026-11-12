module
public import Slop.Delegation.RVSharedSpans
public import Slop.Delegation.RVNativeSegments
public import Slop.Blake2Round.RVWords

@[expose] public section

/-! RV sibling of `Delegation/SpanTarget.lean` (`hash_span_at_target`): a complete span at a native boundary reaches its
    RV span result (delegate link included) at any final state that the same window's history reaches; two such final
    states are `RV.Same`, so the reference transfers whole. -/

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Delegation.Caller
set_option warningAsError true
set_option maxRecDepth 16384

/-- An RV span result transfers to an `RV.Same` final state that the same accesses reach. -/
theorem rv_span_result_transfer [Fact p.Prime] {span : HashSpan} {workers : Delegation.MemoryData p}
    {before first last : RV.State} {cells : List Cell}
    (result : Delegation.Caller.HashSpan.RVResult span workers before first cells) (same : RV.Same first last)
    (target : Delegation.RVTraceMapping workers before last cells) :
    Delegation.Caller.HashSpan.RVResult span workers before last cells := by
  cases span with
  | blakeG reduced =>
    obtain ⟨statePointer, messagePointer, input, message, output, mapping, _, value, s', run, linked⟩ := result
    exact ⟨statePointer, messagePointer, input, message, output,
      ⟨mapping.pointers, mapping.inputWords, mapping.messageWords,
        Blake2Round.Proofs.rv_words_at_same same mapping.outputWords,
        Blake2Round.Proofs.rv_words_at_same same mapping.messageUnchanged⟩,
      target, value, s', run, linked.trans (same.setPC _)⟩
  | blakeRound flags =>
    obtain ⟨statePointer, messagePointer, input, message, output, mapping, _, value, s', run, linked⟩ := result
    exact ⟨statePointer, messagePointer, input, message, output,
      ⟨mapping.pointers, mapping.inputState, mapping.inputExtended, mapping.messageWords,
        Blake2Round.Proofs.rv_words_at_same same mapping.outputState,
        Blake2Round.Proofs.rv_words_at_same same mapping.outputExtended⟩,
      target, value, s', run, linked.trans (same.setPC _)⟩
  | keccak =>
    obtain ⟨pointer, input, output, mapping, _, value, s', run, linked⟩ := result
    refine ⟨pointer, input, output, ⟨mapping.pointerRead, mapping.inputLanes, ?_⟩,
      target, value, s', run, linked.trans (same.setPC _)⟩
    intro lane
    obtain ⟨low, high, lowRead, highRead, word, bound⟩ := mapping.outputLanes lane
    exact ⟨low, high, (readRV_congr_same same).symm.trans lowRead, (readRV_congr_same same).symm.trans highRead,
      word, bound⟩

theorem rv_hash_span_at_target [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {workers : Delegation.MemoryData p} {before after : RV.State} {cells : List Cell} {span : HashSpan}
    (accepted : Delegation.MemoryAccepted workers) (inputs : Delegation.RVBoundaryMemoryInputs workers before cells)
    (protocol : Delegation.Caller.HashSpan.RVProtocol workers before span)
    (active : ∀ row ∈ workers.rows, row.assignment row.columns.execute = 1)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (target : Delegation.RVTraceMapping workers before after cells)
    (addresses : (workers.terminal.map MemoryToken.address).Perm (cells.map Cell.addressCode)) :
    Delegation.Caller.HashSpan.RVResult span workers before after cells := by
  have rotationInverse : 64 * (-31457280 : ZMod p) = 1 := by linear_combination clockInverse
  have byteInverse : 256 * (-7864320 : ZMod p) = 1 := by linear_combination clockInverse
  have reference : ∃ reached, Delegation.Caller.HashSpan.RVResult span workers before reached cells := by
    cases span with
    | blakeG reduced =>
      have abi : Blake2G.RVNativeCallInputs workers before cells reduced := by
        refine ⟨inputs, protocol.tables, protocol.family, ?_, protocol.controlStart, protocol.calls⟩
        intro row member
        have family := protocol.family row member
        simpa [Delegation.Row.columns, HashSpan.family, family, Blake2G.importedConstraintsDelegationColumns,
          Blake2G.Variables.execute] using active row member
      obtain ⟨reached, result⟩ := Blake2G.Proofs.rv_workvector_binding_at_boundary (by omega) rotationInverse
        accepted (Blake2G.Proofs.RVNativeCallInputs.toRVBoundary abi) aligned
      exact ⟨reached, result⟩
    | blakeRound flags =>
      have abi : Blake2Round.RVNativeCallInputs workers before cells flags :=
        ⟨inputs, protocol.tables, protocol.family, protocol.controlStart, protocol.calls⟩
      obtain ⟨reached, result⟩ := Blake2Round.Proofs.rv_compression_binding_at_boundary (by omega) rotationInverse
        accepted (Blake2Round.Proofs.RVNativeCallInputs.toRVBoundary abi) aligned
      exact ⟨reached, result⟩
    | keccak =>
      have abi : Keccak.RVNativeCallInputs workers before cells := by
        refine ⟨inputs, protocol.controlStart, protocol.family, ?_, protocol.calls⟩
        intro row member
        have family := protocol.family row member
        simpa [Delegation.Row.columns, HashSpan.family, family, Keccak.importedConstraintsDelegationColumns,
          Keccak.Variables.execute] using active row member
      obtain ⟨reached, result⟩ := Keccak.Proofs.rv_permutation_binding_at_boundary hp byteInverse accepted
        (abi.toRVBoundary (by norm_num [timestampBase]; omega) accepted) protocol.tables aligned
      exact ⟨reached, result⟩
  obtain ⟨reached, result⟩ := reference
  have same := Delegation.Proofs.rv_trace_mapping_same (Delegation.Caller.Proofs.rv_hash_span_result_mapping result) target addresses aligned
  exact rv_span_result_transfer result same target

end Airbender.UnifiedReduced.Caller.Proofs
