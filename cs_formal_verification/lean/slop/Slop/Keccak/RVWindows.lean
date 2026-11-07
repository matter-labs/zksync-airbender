import Slop.Keccak.RVPermutation
import Slop.Keccak.MemorySoundness
import Slop.Delegation.RVNativeSegments
import Human.Trace.Delegation.RVHashWindows

/-! RV twins of `Windows.window_binding` and the boundary conversions: the first complete special5 span in a native
    worker pool reaches Clean's Keccak permutation, delegate link included, on its actual native-clock cut
    `RV.State`s. RAM cells include the shadow RAM below `ROM_END`. -/

namespace Airbender.Keccak.Proofs
open Trace Trace.Proofs Arithmetic Delegation.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

/-- The RV boundary of a special5 span (`RVBoundaryCallInputs`) from the human `RVCallInputs`. -/
theorem _root_.Airbender.Keccak.RVCallInputs.toRVBoundary [Fact p.Prime] {data : Delegation.MemoryData p} {initial : RV.State}
    {cells : List Cell} (inputs : RVCallInputs data initial cells) : RVBoundaryCallInputs data initial cells :=
  ⟨inputs.memory.toRVBoundaryInputs, inputs.controlCell, inputs.controlStart, inputs.family, inputs.active,
    inputs.calls⟩

/-- The RV boundary of a special5 span from the human `RVNativeCallInputs`: x10 is tracked because every row's
    control port is initialized. -/
theorem _root_.Airbender.Keccak.RVNativeCallInputs.toRVBoundary [Fact p.Prime] (hp : 2 * timestampBase + 4 < p)
    {data : Delegation.MemoryData p} {initial : RV.State} {cells : List Cell}
    (accepted : Delegation.MemoryAccepted data) (inputs : RVNativeCallInputs data initial cells) :
    RVBoundaryCallInputs data initial cells := by
  have memory := RVBoundaryMemoryInputs.toRVBoundaryInputs inputs.memory
  have nonempty : data.rows ≠ [] := by
    intro empty
    have count := inputs.calls
    simp [empty] at count
  obtain ⟨row, member⟩ := List.exists_mem_of_ne_nil _ nonempty
  have family := inputs.family row member
  have port : importedConstraintsMemoryPorts[0] ∈ row.ports := by
    simp [Delegation.Row.ports, family, importedConstraintsMemoryPorts]
  have tracked := seed_port_initialized_cell hp accepted memory.toSeed member port (cell := .register 10) (by rfl)
  exact ⟨memory, tracked, inputs.controlStart, inputs.family, inputs.active, inputs.calls⟩

/-- State-free twin of `Memory.Proofs.memory_rules_at_boundary`: Keccak writes are canonical given canonical reads. -/
theorem seed_memory_rules [Fact p.Prime] (hp : 1048576 ≤ p) {data : Delegation.MemoryData p}
    (accepted : Delegation.MemoryAccepted data) (families : ∀ row ∈ data.rows, row.family = .keccak)
    (table : data.setup.keccak = setupTable Controller.rows)
    (active : ∀ row ∈ data.rows, row.assignment Variables.execute = 1) :
    Delegation.Proofs.WriteBoundsFromReads data := by
  intro row member reads
  cases row with
  | mk family w =>
    have selected := families ⟨family, w⟩ member
    change family = .keccak at selected
    subst family
    have h := accepted.constraints ⟨.keccak, w⟩ member
    change FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (clockConstraints data.setup.keccak) at h
    rw [table] at h
    exact Keccak.Proofs.memory_write_rule hp h (active _ member) reads

theorem rv_window_binding [Fact p.Prime] (hp : 16777216 ≤ p)
    (inverse : 256 * (-7864320 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {before : RV.State} {cells : List Cell} {lower upper : Nat}
    (accepted : Delegation.MemoryAccepted data) (inputs : RVWindowInputs data before cells lower upper)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.Caller.RVWindowResult RVSpanResult data before cells lower upper := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have rules := seed_memory_rules (by omega) accepted inputs.family (by rw [inputs.tables]; rfl) inputs.active
  have boundary := RVBoundaryMemoryInputs.toRVBoundaryInputs inputs.memory
  obtain ⟨start, finish, earlierEvents, spanEvents, atStart, atFinish, _,
      selectedAccepted, earlierPerm, spanPerm, earlierHistory, spanHistory, startInputs, finishInputs⟩ :=
    rv_native_span_window_at_boundary size accepted boundary rules aligned lower upper
  have same := rv_empty_prefix_state inputs.prefixEmpty earlierPerm earlierHistory
  subst atStart
  let selected : Delegation.MemoryData p := ⟨data.setup, data.windowRows lower upper, start, finish⟩
  have memory : Delegation.RVBoundaryMemoryInputs selected before cells :=
    rv_native_window_boundary_inputs_at_boundary boundary startInputs
  have publicABI : RVNativeCallInputs selected before cells :=
    ⟨memory, inputs.controlStart,
      fun row member => inputs.family row (List.mem_of_mem_filter member),
      fun row member => inputs.active row (List.mem_of_mem_filter member), inputs.calls⟩
  have abi := publicABI.toRVBoundary size selectedAccepted
  obtain ⟨referenceAfter, pointer, input, output, mapping, source, result, s', run, linked⟩ :=
    rv_permutation_binding_at_boundary hp inverse selectedAccepted abi inputs.tables aligned
  have target : Delegation.RVTraceMapping selected before atFinish cells := by
    refine ⟨⟨spanEvents, spanPerm, spanHistory⟩, ?_⟩
    intro token member
    exact finishInputs.reads token member
  have sameAfter := rv_trace_mapping_same source target finishInputs.addresses aligned
  have lanes : Permutation.RVLanesAt atFinish pointer output := by
    intro lane
    obtain ⟨low, high, lowRead, highRead, value, bound⟩ := mapping.outputLanes lane
    exact ⟨low, high, (readRV_congr_same sameAfter).symm.trans lowRead,
      (readRV_congr_same sameAfter).symm.trans highRead, value, bound⟩
  refine ⟨start, finish, earlierEvents, spanEvents, before, atFinish,
    ?_, spanPerm, earlierHistory, spanHistory, selectedAccepted, memory,
    pointer, input, output, ⟨mapping.pointerRead, mapping.inputLanes, lanes⟩, target, result, s', run,
    linked.trans (sameAfter.setPC _)⟩
  simpa only [native_prefix_steps] using earlierPerm

end Airbender.Keccak.Proofs
