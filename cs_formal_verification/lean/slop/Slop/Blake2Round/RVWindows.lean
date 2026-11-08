module
public import Slop.Blake2Round.RVCompression
public import Slop.Blake2Round.Memory
public import Slop.Delegation.RVNativeSegments
public import Human.Trace.Delegation.RVHashWindows

@[expose] public section

/-! RV twin of `Windows.window_binding`: the first complete compression of a retained native boundary reaches its
    reference, delegate link included, on actual cut `RV.State`s. RAM cells include the shadow RAM below `ROM_END`. -/

namespace Airbender.Blake2Round.Proofs
open Trace Trace.Proofs Arithmetic Delegation.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

/-- The RV boundary of a round span from the human `RVCallInputs`. -/
theorem RVCallInputs.toRVBoundary [Fact p.Prime] {data : Delegation.MemoryData p} {initial : RV.State}
    {cells : List Cell} {flags : Fin 8} (inputs : RVCallInputs data initial cells flags) :
    RVBoundaryCallInputs data initial cells flags :=
  ⟨inputs.memory.toRVBoundaryInputs, inputs.tables, inputs.family, inputs.controlStart, inputs.calls⟩

/-- The RV boundary of a round span from the human `RVNativeCallInputs`. -/
theorem RVNativeCallInputs.toRVBoundary [Fact p.Prime] {data : Delegation.MemoryData p} {initial : RV.State}
    {cells : List Cell} {flags : Fin 8} (inputs : RVNativeCallInputs data initial cells flags) :
    RVBoundaryCallInputs data initial cells flags :=
  ⟨RVBoundaryMemoryInputs.toRVBoundaryInputs inputs.memory, inputs.tables, inputs.family, inputs.controlStart,
    inputs.calls⟩

theorem rv_window_binding [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {before : RV.State} {cells : List Cell}
    {flags : Fin 8} {lower upper : Nat} (accepted : Delegation.MemoryAccepted data)
    (inputs : RVWindowInputs data before cells flags lower upper)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.Caller.RVWindowResult (RVSpanResult flags) data before cells lower upper := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have boundary := RVBoundaryMemoryInputs.toRVBoundaryInputs inputs.memory
  have nonempty : data.windowRows lower upper ≠ [] := by
    intro empty
    have count := inputs.calls
    simp only [empty, List.length_nil] at count
    split_ifs at count
  obtain ⟨row, rowMember⟩ := List.exists_mem_of_ne_nil _ nonempty
  have seed : SeedCallInputs data cells flags := by
    refine ⟨boundary.toSeed, inputs.tables, inputs.family, ?_, inputs.roundsBound,
      List.ne_nil_of_mem (List.mem_of_mem_filter rowMember)⟩
    intro token present code
    rw [rv_seed_word boundary present code inputs.controlStart]
    have flagBound := flags.isLt
    simp [Word.ofBitVec, controlAt, limbBase, BitVec.toNat_ofNat]
    omega
  have masks := matching_masks size accepted (seed.toMatching size accepted)
  have table : data.setup.blakeRound = setupTable := by rw [inputs.tables]; rfl
  have rules := memory_rules hp inverse accepted inputs.family table masks
  obtain ⟨start, finish, earlierEvents, spanEvents, atStart, atFinish, _,
      selectedAccepted, earlierPerm, spanPerm, earlierHistory, spanHistory, startInputs, finishInputs⟩ :=
    rv_native_span_window_at_boundary size accepted boundary rules aligned lower upper
  have same := rv_empty_prefix_state inputs.prefixEmpty earlierPerm earlierHistory
  subst atStart
  let selected : Delegation.MemoryData p := ⟨data.setup, data.windowRows lower upper, start, finish⟩
  have memory : Delegation.RVBoundaryMemoryInputs selected before cells :=
    rv_native_window_boundary_inputs_at_boundary boundary startInputs
  have abi : RVBoundaryCallInputs selected before cells flags :=
    ⟨RVBoundaryMemoryInputs.toRVBoundaryInputs memory, inputs.tables,
      fun row member => inputs.family row (List.mem_of_mem_filter member), inputs.controlStart, inputs.calls⟩
  obtain ⟨referenceAfter, statePointer, messagePointer, input, message, output, mapping, source, result,
    s', run, linked⟩ := rv_compression_binding_at_boundary hp inverse selectedAccepted abi aligned
  have target : Delegation.RVTraceMapping selected before atFinish cells := by
    refine ⟨⟨spanEvents, spanPerm, spanHistory⟩, ?_⟩
    intro token member
    exact finishInputs.reads token member
  have sameFinal := rv_trace_mapping_same source target finishInputs.addresses aligned
  have atWindow : Compression.RVWordMapping before atFinish statePointer messagePointer input output message :=
    ⟨mapping.pointers, mapping.inputState, mapping.inputExtended, mapping.messageWords,
      rv_words_at_same sameFinal mapping.outputState, rv_words_at_same sameFinal mapping.outputExtended⟩
  refine ⟨start, finish, earlierEvents, spanEvents, before, atFinish,
    ?_, spanPerm, earlierHistory, spanHistory, selectedAccepted, memory,
    statePointer, messagePointer, input, message, output, atWindow, target, result, s', run,
    linked.trans (sameFinal.setPC _)⟩
  simpa only [native_prefix_steps] using earlierPerm

end Airbender.Blake2Round.Proofs
