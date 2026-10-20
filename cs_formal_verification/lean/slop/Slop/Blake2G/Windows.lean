import Human.Trace.Workers.Blake2G.Windows
import Slop.Blake2G.ControlPool
import Slop.Blake2G.WorkVectorBinding
import Slop.Blake2G.Memory
import Slop.Delegation.NativeSegments
import Slop.Delegation.HashWindowTransport

namespace Airbender.Blake2G.Proofs
open Trace Trace.Proofs Arithmetic Reference.RiscV.Sail Delegation.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

theorem window_binding [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {before : State} {cells : List Cell}
    {reduced : Bool} {lower upper : Nat} (accepted : Delegation.MemoryAccepted data)
    (inputs : WindowInputs data before cells reduced lower upper)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    (Delegation.Caller.HashSpan.blakeG reduced).WindowResult data before cells lower upper := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have table : data.setup.blakeG = setupTable Control.controllerRows := by
    rw [inputs.tables]
    rfl
  have rules := memory_rules (by omega) inverse accepted inputs.family table
  obtain ⟨start, finish, earlierEvents, spanEvents, atStart, atFinish, prefixFacts,
      selectedAccepted, earlierPerm, spanPerm, earlierHistory, spanHistory, startInputs, finishInputs⟩ :=
    native_span_window size accepted inputs.memory rules aligned lower upper
  let selected : Delegation.MemoryData p := ⟨data.setup, data.windowRows lower upper, start, finish⟩
  let priorData : Delegation.MemoryData p := ⟨data.setup, data.prefixRows lower, data.initial, start⟩
  have prefixAccepted : Delegation.MemoryAccepted priorData := by
    refine ⟨?_, ?_⟩
    · intro row member
      exact accepted.constraints row (List.mem_of_mem_filter member)
    · simpa only [priorData, Delegation.MemoryData.steps, native_prefix_steps] using prefixFacts.matching
  have prefixMemory : Delegation.MemoryInputs priorData before cells :=
    ⟨inputs.memory.initialization, inputs.memory.distinct,
      fun row member => inputs.memory.clockRoom row (List.mem_of_mem_filter member)⟩
  have nonempty : data.windowRows lower upper ≠ [] := by
    intro empty
    have count := inputs.calls
    rw [empty] at count
    cases reduced <;> simp [callCount] at count
  obtain ⟨row, rowMember⟩ := List.exists_mem_of_ne_nil _ nonempty
  have original := List.mem_of_mem_filter rowMember
  have controlPort : importedConstraintsMemoryPorts[8] ∈ row.ports := by
    simp [Delegation.Row.ports, inputs.family row original, importedConstraintsMemoryPorts]
  have tracked := port_initialized_cell size accepted inputs.memory.toBoundaryInputs original controlPort
    (cell := .register 12) (by rfl)
  have pool : ControlPoolInputs priorData before cells reduced :=
    ⟨prefixMemory.toBoundaryInputs, inputs.tables,
      fun row member => inputs.family row (List.mem_of_mem_filter member),
      fun row member => inputs.active row (List.mem_of_mem_filter member), tracked, inputs.controlStart⟩
  obtain ⟨_, _, _, _, sink, sinkMember, sinkCode, sinkWord⟩ := pool_ordered_controls size prefixAccepted pool
  obtain ⟨control, _, code, read⟩ := startInputs.reads sink sinkMember
  have controlSame : control = Cell.register 12 := cell_address_injective (code.trans sinkCode)
  subst control
  have reset : sink.word.toBitVec = if reduced then 128 else 0 := by
    rw [sinkWord]
    simp only [controlAt, priorData, inputs.prefixComplete, Nat.add_zero]
    cases reduced <;> rfl
  have controlStart : (Cell.register 12).read atStart = .ok (if reduced then 128 else 0) atStart := by
    change (Cell.register 12).read atStart = .ok sink.word.toBitVec atStart at read
    simpa only [reset] using read
  have memory : Delegation.BoundaryMemoryInputs selected atStart cells :=
    native_window_boundary_inputs inputs.memory startInputs
  have abi : BoundaryCallInputs selected atStart cells reduced :=
    ⟨memory.toBoundaryInputs, inputs.tables,
      fun row member => inputs.family row (List.mem_of_mem_filter member),
      fun row member => inputs.active row (List.mem_of_mem_filter member), controlStart, inputs.calls⟩
  obtain ⟨referenceAfter, statePointer, messagePointer, input, message, output, mapping, source, result⟩ :=
    workvector_binding_at_boundary hp inverse selectedAccepted abi aligned
  have target : Delegation.TraceMapping selected atStart atFinish cells := by
    refine ⟨⟨spanEvents, spanPerm, spanHistory⟩, ?_⟩
    intro token member
    exact finishInputs.reads token member
  obtain ⟨state, msg, stateRead, messageRead, _, _, _, domain⟩ := call_block_domain hp inverse selectedAccepted abi
  have sameState := (EStateM.Result.ok.inj (mapping.pointers.1.symm.trans stateRead)).1
  have sameMessage := (EStateM.Result.ok.inj (mapping.pointers.2.symm.trans messageRead)).1
  subst state
  subst msg
  have transfer {n : Nat} {pointer : BitVec 32} {words : Vector Word n}
      (tracked : ∀ i : Fin n, Cell.ram (pointer + BitVec.ofNat 32 (4 * (0 + i.val))) ∈ cells)
      (reads : Blake2Round.Compression.WordsAt referenceAfter pointer 0 words) :
      Blake2Round.Compression.WordsAt atFinish pointer 0 words := by
    intro i
    exact ⟨(reads i).1, terminal_mapping_read source target finishInputs.addresses (tracked i) (reads i).2⟩
  have stateTracked : ∀ i : Fin 16, Cell.ram (statePointer + BitVec.ofNat 32 (4 * (0 + i.val))) ∈ cells := by
    intro i
    simpa only [if_true, Nat.zero_add] using domain true i
  have messageTracked : ∀ i : Fin 16, Cell.ram (messagePointer + BitVec.ofNat 32 (4 * (0 + i.val))) ∈ cells := by
    intro i
    simpa only [Bool.false_eq_true, if_false, Nat.zero_add] using domain false i
  have atWindow : WorkVector.WordMapping atStart atFinish statePointer messagePointer input message output :=
    ⟨mapping.pointers, mapping.inputWords, mapping.messageWords,
      transfer stateTracked mapping.outputWords, transfer messageTracked mapping.messageUnchanged⟩
  refine ⟨start, finish, earlierEvents, spanEvents, atStart, atFinish,
    ?_, spanPerm, earlierHistory, spanHistory, selectedAccepted, memory,
    statePointer, messagePointer, input, message, output, atWindow, target, result⟩
  simpa only [native_prefix_steps] using earlierPerm

end Airbender.Blake2G.Proofs
