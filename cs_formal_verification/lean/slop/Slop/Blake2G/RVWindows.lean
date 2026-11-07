import Slop.Blake2G.RVWorkVector
import Slop.Blake2G.Memory
import Slop.Delegation.RVNativeSegments
import Human.Trace.Delegation.RVHashWindows

/-! RV twin of `Windows.window_binding`: a complete G-worker span selected after whole preceding spans reaches the
    work-vector reference, delegate link included, on its actual native-clock cut `RV.State`s. RAM cells include the
    shadow RAM below `ROM_END`. -/

namespace Airbender.Blake2G.Proofs
open Trace Trace.Proofs Arithmetic Delegation.Proofs
open Blake2Round.Proofs (rv_words_at_same)
set_option warningAsError true
set_option maxRecDepth 16384

/-- The RV boundary of a G span (`RVBoundaryCallInputs`) from the human `RVCallInputs`. -/
theorem RVCallInputs.toRVBoundary [Fact p.Prime] {data : Delegation.MemoryData p} {initial : RV.State}
    {cells : List Cell} {reduced : Bool} (inputs : RVCallInputs data initial cells reduced) :
    RVBoundaryCallInputs data initial cells reduced :=
  ⟨inputs.memory.toRVBoundaryInputs, inputs.tables, inputs.family, inputs.active, inputs.controlStart, inputs.calls⟩

/-- The RV boundary of a G span (`RVBoundaryCallInputs`) from the human `RVNativeCallInputs`. -/
theorem RVNativeCallInputs.toRVBoundary [Fact p.Prime] {data : Delegation.MemoryData p} {initial : RV.State}
    {cells : List Cell} {reduced : Bool} (inputs : RVNativeCallInputs data initial cells reduced) :
    RVBoundaryCallInputs data initial cells reduced :=
  ⟨RVBoundaryMemoryInputs.toRVBoundaryInputs inputs.memory, inputs.tables, inputs.family, inputs.active,
    inputs.controlStart, inputs.calls⟩

theorem rv_window_binding [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {before : RV.State} {cells : List Cell}
    {reduced : Bool} {lower upper : Nat} (accepted : Delegation.MemoryAccepted data)
    (inputs : RVWindowInputs data before cells reduced lower upper)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.Caller.RVWindowResult (RVSpanResult reduced) data before cells lower upper := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  -- the serialized inverse fixes p = BabyBear, above Blake2G's 2^25 bound
  have field : 33554432 ≤ p := by
    rw [serialized_field inverse]; unfold babyBearModulus; norm_num
  have table : data.setup.blakeG = setupTable Control.controllerRows := by
    rw [inputs.tables]
    rfl
  have rules := memory_rules (by omega) inverse accepted inputs.family table
  have boundary := inputs.memory.toRVBoundaryInputs
  obtain ⟨start, finish, earlierEvents, spanEvents, atStart, atFinish, prefixFacts,
      selectedAccepted, earlierPerm, spanPerm, earlierHistory, spanHistory, startInputs, finishInputs⟩ :=
    rv_native_span_window_at_boundary size accepted boundary rules aligned lower upper
  let selected : Delegation.MemoryData p := ⟨data.setup, data.windowRows lower upper, start, finish⟩
  let priorData : Delegation.MemoryData p := ⟨data.setup, data.prefixRows lower, data.initial, start⟩
  have prefixAccepted : Delegation.MemoryAccepted priorData := by
    refine ⟨?_, ?_⟩
    · intro row member
      exact accepted.constraints row (List.mem_of_mem_filter member)
    · simpa only [priorData, Delegation.MemoryData.steps, native_prefix_steps] using prefixFacts.matching
  have prefixMemory : Delegation.RVMemoryInputs priorData before cells :=
    ⟨inputs.memory.initialization, inputs.memory.distinct,
      fun row member => inputs.memory.clockRoom row (List.mem_of_mem_filter member),
      fun row member => inputs.memory.invocationHigh row (List.mem_of_mem_filter member)⟩
  have nonempty : data.windowRows lower upper ≠ [] := by
    intro empty
    have count := inputs.calls
    rw [empty] at count
    cases reduced <;> simp [callCount] at count
  obtain ⟨row, rowMember⟩ := List.exists_mem_of_ne_nil _ nonempty
  have original := List.mem_of_mem_filter rowMember
  have controlPort : importedConstraintsMemoryPorts[8] ∈ row.ports := by
    simp [Delegation.Row.ports, inputs.family row original, importedConstraintsMemoryPorts]
  have tracked := seed_port_initialized_cell size accepted boundary.toSeed original controlPort
    (cell := .register 12) (by rfl)
  have prefixBoundary := prefixMemory.toRVBoundaryInputs
  have pool : SeedControlPoolInputs priorData cells reduced := by
    refine ⟨prefixBoundary.toSeed, inputs.tables,
      fun row member => inputs.family row (List.mem_of_mem_filter member),
      fun row member => inputs.active row (List.mem_of_mem_filter member), tracked, ?_⟩
    intro token present code
    rw [rv_seed_word prefixBoundary present code inputs.controlStart]
    cases reduced <;> rfl
  obtain ⟨_, _, _, _, sink, sinkMember, sinkCode, sinkWord⟩ := seed_pool_ordered_controls size prefixAccepted pool
  obtain ⟨control, _, code, read⟩ := startInputs.reads sink sinkMember
  have controlSame : control = Cell.register 12 := cell_address_injective (code.trans sinkCode)
  subst control
  have reset : sink.word.toBitVec = if reduced then 128 else 0 := by
    rw [sinkWord]
    simp only [controlAt, priorData, inputs.prefixComplete, Nat.add_zero]
    cases reduced <;> rfl
  have controlStart : (Cell.register 12).readRV atStart = some (if reduced then 128 else 0) := by
    change (Cell.register 12).readRV atStart = some sink.word.toBitVec at read
    rw [read, reset]
  have memory : Delegation.RVBoundaryMemoryInputs selected atStart cells :=
    rv_native_window_boundary_inputs_at_boundary boundary startInputs
  have abi : RVBoundaryCallInputs selected atStart cells reduced :=
    ⟨RVBoundaryMemoryInputs.toRVBoundaryInputs memory, inputs.tables,
      fun row member => inputs.family row (List.mem_of_mem_filter member),
      fun row member => inputs.active row (List.mem_of_mem_filter member), controlStart, inputs.calls⟩
  obtain ⟨referenceAfter, statePointer, messagePointer, input, message, output, mapping, source, result,
    s', run, linked⟩ := rv_workvector_binding_at_boundary hp inverse selectedAccepted abi aligned
  have target : Delegation.RVTraceMapping selected atStart atFinish cells := by
    refine ⟨⟨spanEvents, spanPerm, spanHistory⟩, ?_⟩
    intro token member
    exact finishInputs.reads token member
  have same := rv_trace_mapping_same source target finishInputs.addresses aligned
  have atWindow : WorkVector.RVWordMapping atStart atFinish statePointer messagePointer input message output :=
    ⟨mapping.pointers, mapping.inputWords, mapping.messageWords,
      rv_words_at_same same mapping.outputWords, rv_words_at_same same mapping.messageUnchanged⟩
  refine ⟨start, finish, earlierEvents, spanEvents, atStart, atFinish,
    ?_, spanPerm, earlierHistory, spanHistory, selectedAccepted, memory,
    statePointer, messagePointer, input, message, output, atWindow, target, result, s', run,
    linked.trans (same.setPC _)⟩
  simpa only [native_prefix_steps] using earlierPerm

end Airbender.Blake2G.Proofs
