import Airbender.Proofs.Delegation.SpanBinding
import Airbender.Proofs.Delegation.HashWindowTransport
import Airbender.Proofs.Blake2G.StateCells
import Airbender.Proofs.Blake2Round.StateTrace
import Airbender.Proofs.Keccak.StateCells

namespace Airbender.Delegation.Caller.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384

theorem hash_span_at_target [Fact p.Prime] (hp : 16777216 ≤ p)
    (clockInverse : (-3840 : ZMod p) * 524288 = 1)
    {workers : MemoryData p} {before after : State} {cells : List Cell} {span : HashSpan}
    (accepted : MemoryAccepted workers) (inputs : BoundaryMemoryInputs workers before cells)
    (protocol : HashSpan.Protocol workers before span)
    (active : ∀ row ∈ workers.rows, row.assignment row.columns.execute = 1)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (target : Delegation.TraceMapping workers before after cells)
    (addresses : (workers.terminal.map MemoryToken.address).Perm (cells.map Cell.addressCode)) :
    span.Result workers before after cells := by
  have rotationInverse : 64 * (-31457280 : ZMod p) = 1 := by linear_combination clockInverse
  have byteInverse : 256 * (-7864320 : ZMod p) = 1 := by linear_combination clockInverse
  cases span with
  | blakeG reduced =>
    have publicABI : Blake2G.NativeCallInputs workers before cells reduced := by
      refine ⟨inputs, protocol.tables, protocol.family, ?_, protocol.controlStart, protocol.calls⟩
      intro row member
      have family := protocol.family row member
      simpa [Row.columns, HashSpan.family, family, Blake2G.importedConstraintsDelegationColumns,
        Blake2G.Variables.execute] using active row member
    have abi := publicABI.toBoundaryInputs
    obtain ⟨referenceAfter, statePointer, messagePointer, input, message, output, mapping, source, result⟩ :=
      Blake2G.Proofs.workvector_binding_at_boundary (by omega) rotationInverse accepted abi aligned
    obtain ⟨state, msg, stateRead, messageRead, _, _, _, domain⟩ :=
      Blake2G.Proofs.call_block_domain (by omega) rotationInverse accepted abi
    have sameState := (EStateM.Result.ok.inj (mapping.pointers.1.symm.trans stateRead)).1
    have sameMessage := (EStateM.Result.ok.inj (mapping.pointers.2.symm.trans messageRead)).1
    subst state
    subst msg
    have transfer {n : Nat} {pointer : BitVec 32} {words : Vector Word n}
        (tracked : ∀ i : Fin n, Cell.ram (pointer + BitVec.ofNat 32 (4 * (0 + i.val))) ∈ cells)
        (reads : Blake2Round.Compression.WordsAt referenceAfter pointer 0 words) :
        Blake2Round.Compression.WordsAt after pointer 0 words := by
      intro i
      exact ⟨(reads i).1, Delegation.Proofs.terminal_mapping_read source target addresses (tracked i) (reads i).2⟩
    have stateTracked : ∀ i : Fin 16, Cell.ram (statePointer + BitVec.ofNat 32 (4 * (0 + i.val))) ∈ cells := by
      intro i
      simpa only [if_true, Nat.zero_add] using domain true i
    have messageTracked : ∀ i : Fin 16, Cell.ram (messagePointer + BitVec.ofNat 32 (4 * (0 + i.val))) ∈ cells := by
      intro i
      simpa only [Bool.false_eq_true, if_false, Nat.zero_add] using domain false i
    exact ⟨statePointer, messagePointer, input, message, output,
      ⟨mapping.pointers, mapping.inputWords, mapping.messageWords,
        transfer stateTracked mapping.outputWords, transfer messageTracked mapping.messageUnchanged⟩, target, result⟩
  | blakeRound flags =>
    have publicABI : Blake2Round.NativeCallInputs workers before cells flags :=
      ⟨inputs, protocol.tables, protocol.family, protocol.controlStart, protocol.calls⟩
    have abi := publicABI.toBoundaryInputs
    obtain ⟨referenceAfter, statePointer, messagePointer, input, message, output, mapping, source, result⟩ :=
      Blake2Round.Proofs.compression_binding_at_boundary (by omega) rotationInverse accepted abi aligned
    obtain ⟨state, msg, stateRead, messageRead, domain⟩ :=
      Blake2Round.Proofs.call_block_cells (by omega) rotationInverse accepted abi aligned
    have sameState := (EStateM.Result.ok.inj (mapping.pointers.1.symm.trans stateRead)).1
    have sameMessage := (EStateM.Result.ok.inj (mapping.pointers.2.symm.trans messageRead)).1
    subst state
    subst msg
    have transfer {n offset : Nat} {words : Vector Word n}
        (tracked : ∀ i : Fin n, Cell.ram (statePointer + BitVec.ofNat 32 (4 * (offset + i.val))) ∈ cells)
        (reads : Blake2Round.Compression.WordsAt referenceAfter statePointer offset words) :
        Blake2Round.Compression.WordsAt after statePointer offset words := by
      intro i
      exact ⟨(reads i).1, Delegation.Proofs.terminal_mapping_read source target addresses (tracked i) (reads i).2⟩
    have stateTracked : ∀ i : Fin 8, Cell.ram (statePointer + BitVec.ofNat 32 (4 * (0 + i.val))) ∈ cells := by
      intro i
      have actual := domain ⟨i.val, by omega⟩
      simpa only [Fin.val_mk, if_pos (show i.val < 24 by omega), Nat.zero_add] using actual
    have extendedTracked : ∀ i : Fin 16, Cell.ram (statePointer + BitVec.ofNat 32 (4 * (8 + i.val))) ∈ cells := by
      intro i
      have actual := domain ⟨8 + i.val, by omega⟩
      simpa only [Fin.val_mk, if_pos (show 8 + i.val < 24 by omega)] using actual
    exact ⟨statePointer, messagePointer, input, message, output,
      ⟨mapping.pointers, mapping.inputState, mapping.inputExtended, mapping.messageWords,
        transfer stateTracked mapping.outputState, transfer extendedTracked mapping.outputExtended⟩, target, result⟩
  | keccak =>
    have publicABI : Keccak.NativeCallInputs workers before cells := by
      refine ⟨inputs, protocol.controlStart, protocol.family, ?_, protocol.calls⟩
      intro row member
      have family := protocol.family row member
      simpa [Row.columns, HashSpan.family, family, Keccak.importedConstraintsDelegationColumns,
        Keccak.Variables.execute] using active row member
    have abi := publicABI.toBoundaryInputs (by norm_num [timestampBase]; omega) accepted
    obtain ⟨referenceAfter, pointer, input, output, mapping, source, result⟩ :=
      Keccak.Proofs.permutation_binding_at_boundary hp byteInverse accepted abi protocol.tables aligned
    obtain ⟨otherPointer, otherRead, domain⟩ :=
      Keccak.Proofs.call_state_cells hp byteInverse accepted abi protocol.tables aligned
    have samePointer := (EStateM.Result.ok.inj (mapping.pointerRead.symm.trans otherRead)).1
    subst otherPointer
    have lanes : Keccak.Permutation.LanesAt after pointer output := by
      intro lane
      let physical : Fin 31 := ⟨Keccak.Controller.physicalLane 0 lane,
        Nat.lt_trans (Keccak.Controller.Proofs.physical_bound 0 lane) (by decide)⟩
      have lowTracked : Cell.ram (pointer + BitVec.ofNat 32 (Keccak.Permutation.laneOffset lane)) ∈ cells := by
        simpa only [physical, Keccak.Controller.physicalLane, Keccak.Permutation.laneOffset,
          Fin.val_zero, Nat.mul_zero, Nat.add_zero] using domain physical 0
      have highTracked : Cell.ram (pointer + BitVec.ofNat 32 (Keccak.Permutation.laneOffset lane) + 4) ∈ cells := by
        have four : BitVec.ofNat 32 4 = (4 : BitVec 32) := by decide +kernel
        simpa only [physical, Keccak.Controller.physicalLane, Keccak.Permutation.laneOffset,
          Fin.val_one, Nat.mul_one, BitVec.ofNat_add, ← BitVec.add_assoc, four] using domain physical 1
      obtain ⟨low, high, lowRead, highRead, value, bound⟩ := mapping.outputLanes lane
      exact ⟨low, high,
        Delegation.Proofs.terminal_mapping_read source target addresses lowTracked lowRead,
        Delegation.Proofs.terminal_mapping_read source target addresses highTracked highRead, value, bound⟩
    exact ⟨pointer, input, output, ⟨mapping.pointerRead, mapping.inputLanes, lanes⟩, target, result⟩

end Airbender.Delegation.Caller.Proofs
