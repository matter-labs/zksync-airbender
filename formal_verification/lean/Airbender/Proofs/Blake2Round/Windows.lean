import Airbender.Review.Blake2Round.Windows
import Airbender.Proofs.Blake2Round.ControlPool
import Airbender.Proofs.Blake2Round.CompressionBinding
import Airbender.Proofs.Blake2Round.Memory
import Airbender.Proofs.Delegation.HashWindowTransport

namespace Airbender.Blake2Round.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail Delegation.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

theorem window_binding [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {before : State} {cells : List Cell}
    {flags : Fin 8} {lower upper : Nat} (accepted : Delegation.MemoryAccepted data)
    (inputs : WindowInputs data before cells flags lower upper)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    (Delegation.Caller.HashSpan.blakeRound flags).WindowResult data before cells lower upper := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have nonempty : data.windowRows lower upper ≠ [] := by
    intro empty
    have count := inputs.calls
    simp only [empty, List.length_nil] at count
    split_ifs at count
  obtain ⟨row, rowMember⟩ := List.exists_mem_of_ne_nil _ nonempty
  have original := List.mem_of_mem_filter rowMember
  have portMember : importedConstraintsMemoryPorts[42] ∈ row.ports := by
    simp [Delegation.Row.ports, inputs.family row original, importedConstraintsMemoryPorts]
  have tracked := port_initialized_cell size accepted inputs.memory.toBoundaryInputs original portMember
    (cell := .register 12) (by rfl)
  have pool : ControlPoolInputs data before cells flags :=
    ⟨inputs.memory.toBoundaryInputs, inputs.tables, inputs.family, tracked,
      inputs.controlStart, inputs.roundsBound⟩
  have masks := pool_masks size accepted pool
  have table : data.setup.blakeRound = setupTable := by rw [inputs.tables]; rfl
  have rules := memory_rules hp inverse accepted inputs.family table masks
  obtain ⟨start, finish, earlierEvents, spanEvents, atStart, atFinish, _,
      selectedAccepted, earlierPerm, spanPerm, earlierHistory, spanHistory, startInputs, finishInputs⟩ :=
    native_span_window_at_boundary size accepted inputs.memory.toBoundaryInputs rules aligned lower upper
  have same := empty_prefix_state inputs.prefixEmpty earlierPerm earlierHistory
  subst atStart
  let selected : Delegation.MemoryData p := ⟨data.setup, data.windowRows lower upper, start, finish⟩
  have memory : Delegation.BoundaryMemoryInputs selected before cells :=
    native_window_boundary_inputs_at_boundary inputs.memory.toBoundaryInputs startInputs
  have abi : BoundaryCallInputs selected before cells flags :=
    ⟨memory.toBoundaryInputs, inputs.tables,
      fun row member => inputs.family row (List.mem_of_mem_filter member), inputs.controlStart, inputs.calls⟩
  obtain ⟨referenceAfter, statePointer, messagePointer, input, message, output, mapping, source, result⟩ :=
    compression_binding_at_boundary hp inverse selectedAccepted abi aligned
  have target : Delegation.TraceMapping selected before atFinish cells := by
    refine ⟨⟨spanEvents, spanPerm, spanHistory⟩, ?_⟩
    intro token member
    exact finishInputs.reads token member
  obtain ⟨state, msg, stateRead, messageRead, domain⟩ := call_block_cells hp inverse selectedAccepted abi aligned
  have sameState := (EStateM.Result.ok.inj (mapping.pointers.1.symm.trans stateRead)).1
  have sameMessage := (EStateM.Result.ok.inj (mapping.pointers.2.symm.trans messageRead)).1
  subst state
  subst msg
  have transfer {n offset : Nat} {words : Vector Word n}
      (tracked : ∀ i : Fin n, Cell.ram (statePointer + BitVec.ofNat 32 (4 * (offset + i.val))) ∈ cells)
      (reads : Compression.WordsAt referenceAfter statePointer offset words) :
      Compression.WordsAt atFinish statePointer offset words := by
    intro i
    exact ⟨(reads i).1, terminal_mapping_read source target finishInputs.addresses (tracked i) (reads i).2⟩
  have stateTracked : ∀ i : Fin 8, Cell.ram (statePointer + BitVec.ofNat 32 (4 * (0 + i.val))) ∈ cells := by
    intro i
    have actual := domain ⟨i.val, by omega⟩
    simpa only [Fin.val_mk, if_pos (show i.val < 24 by omega), Nat.zero_add] using actual
  have extendedTracked : ∀ i : Fin 16, Cell.ram (statePointer + BitVec.ofNat 32 (4 * (8 + i.val))) ∈ cells := by
    intro i
    have actual := domain ⟨8 + i.val, by omega⟩
    simpa only [Fin.val_mk, if_pos (show 8 + i.val < 24 by omega)] using actual
  have atWindow : Compression.WordMapping before atFinish statePointer messagePointer input output message :=
    ⟨mapping.pointers, mapping.inputState, mapping.inputExtended, mapping.messageWords,
      transfer stateTracked mapping.outputState, transfer extendedTracked mapping.outputExtended⟩
  refine ⟨start, finish, earlierEvents, spanEvents, before, atFinish,
    ?_, spanPerm, earlierHistory, spanHistory, selectedAccepted, memory,
    statePointer, messagePointer, input, message, output, atWindow, target, result⟩
  simpa only [native_prefix_steps] using earlierPerm

end Airbender.Blake2Round.Proofs
