import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.UnifiedReduced.MixedNativeROM
import Airbender.Proofs.UnifiedReduced.ROMData
import Airbender.Proofs.UnifiedReduced.MixedMemory
import Airbender.Proofs.ExternalBoundary.WorkerRAM

namespace Airbender.UnifiedReduced.Caller.NativeROM.Proofs
open Trace Arithmetic Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem selected (initial : State) (native : Trace.Row p UnifiedFamily) :
    Selected (UnifiedReduced.ROMView.row initial native).assignment ↔ Selected native.assignment := by
  unfold UnifiedReduced.ROMView.row
  split <;> rfl

theorem request (initial : State) (native : Trace.Row p UnifiedFamily) :
    Caller.request (UnifiedReduced.ROMView.row initial native).assignment = Caller.request native.assignment := by
  unfold UnifiedReduced.ROMView.row
  split <;> rfl

theorem caller_query (initial : State) (native : Trace.Row p UnifiedFamily) :
    UnifiedReduced.decoderQuery (UnifiedReduced.ROMView.row initial native).assignment = UnifiedReduced.decoderQuery native.assignment := by
  unfold UnifiedReduced.ROMView.row
  split <;> rfl

theorem callers [Fact p.Prime] (initial : State) (native : RequestTrace p) :
    (view initial native).callers = native.callers.map (UnifiedReduced.ROMView.row initial) := by
  simp only [RequestTrace.callers, view, UnifiedReduced.ROMView.data, List.filter_map]
  congr 1
  apply List.filter_congr
  intro row _
  simp only [Function.comp_apply, selected]

theorem calls [Fact p.Prime] (initial : State) (native : RequestTrace p) :
    (view initial native).calls = native.calls := by
  simp only [RequestTrace.calls, callers, List.map_map, Function.comp_def, request]

theorem caller_row [Fact p.Prime] (hp : FieldCapacity.NoWrap p 18) (initial : State)
    (native : Trace.Row p UnifiedFamily) (setup : Table (ZMod p) (fields 10))
    (active : native.assignment 4 = 1)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment native.assignment) (native.constraints setup))
    (caller : Selected native.assignment) : UnifiedReduced.ROMView.row initial native = native := by
  rcases native with ⟨family, w⟩
  cases family
  have core := Verification.holds_of_sublist holds
    (List.sublist_append_left (importedConstraints setup) importedConstraintsTimestampLookups)
  have flag : w 18 = 1 := caller
  have excluded := UnifiedReduced.Proofs.dispatch_exclusive hp core active 7 flag 16 (by decide)
  change w 28 = 0 at excluded
  simp [UnifiedReduced.ROMView.row, excluded]

theorem zip_maps (items : List α) (left : α → β) (right : α → γ) :
    (items.map left).zip (items.map right) = items.map (fun item => (left item, right item)) := by
  induction items <;> simp_all

theorem machine_steps [Fact p.Prime] (hp : FieldCapacity.NoWrap p 131072) (initial : State)
    (native : Trace.Row p UnifiedFamily) (setup : Table (ZMod p) (fields 10))
    (active : native.assignment 4 = 1)
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment native.assignment) (native.constraints setup)) :
    (machinePorts (UnifiedReduced.ROMView.row initial native)).toList.map (fun port =>
      (readToken (UnifiedReduced.ROMView.row initial native).assignment port,
        writeToken (UnifiedReduced.ROMView.row initial native).columns
          (UnifiedReduced.ROMView.row initial native).assignment port)) =
    ((machinePorts native).toList.map (fun port =>
      (readToken native.assignment port, writeToken native.columns native.assignment port))).map
        (fun edge => (Trace.ROMView.token initial edge.1, Trace.ROMView.token initial edge.2)) := by
  by_cases caller : Selected native.assignment
  · rw [caller_row (by omega) initial native setup active holds caller]
    have core := Verification.holds_of_sublist holds
      (List.sublist_append_left (importedConstraints setup) importedConstraintsTimestampLookups)
    have store := UnifiedReduced.Proofs.dispatch_exclusive (by omega) core active 7 caller 17 (by decide)
    change native.assignment 29 = 0 at store
    simp [machinePorts, caller, architecturalPorts, importedConstraintsMemoryPorts,
      readToken, writeToken, Trace.Row.columns, CircuitLayout.columns,
      importedConstraintsTraceColumns, MemoryPort.readCode, MemoryPort.writeCode,
      MemoryAddress.code, store, Trace.ROMView.token, Trace.ROMView.shadow]
  · have lifted : ¬ Selected (UnifiedReduced.ROMView.row initial native).assignment := by
      simpa only [selected] using caller
    simp only [machinePorts, if_neg caller, if_neg lifted]
    have transfers := UnifiedReduced.ROMView.row_transfers hp initial native setup active holds
    calc
      _ = (UnifiedReduced.ROMView.row initial native).reads.zip
          (UnifiedReduced.ROMView.row initial native).writes := (zip_maps _ _ _).symm
      _ = (native.reads.map (Trace.ROMView.token initial)).zip
          (native.writes.map (Trace.ROMView.token initial)) := by rw [transfers.1, transfers.2]
      _ = (native.reads.zip native.writes).map
          (Prod.map (Trace.ROMView.token initial) (Trace.ROMView.token initial)) := List.zip_map
      _ = _ := by rw [Trace.Row.reads, Trace.Row.writes, zip_maps]; rfl

theorem steps [Fact p.Prime] (hp : FieldCapacity.NoWrap p 131072) (initial : State)
    {native : RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    (accepted : MixedMemoryAccepted native program)
    (ram : ExternalBoundary.WorkerRAM.Binding native.workers.rows) :
    (view initial native).mixedSteps = native.mixedSteps.map
      (fun edge => (Trace.ROMView.token initial edge.1, Trace.ROMView.token initial edge.2)) := by
  simp only [RequestTrace.mixedSteps, view, UnifiedReduced.ROMView.data, List.flatMap_map, List.map_append]
  rw [ExternalBoundary.WorkerRAM.Proofs.pool_transfers_unchanged initial ram]
  congr 1
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro row member
  exact machine_steps hp initial row native.machine.rom (accepted.active row member) (accepted.constraints row member)

theorem accepted [Fact p.Prime] (hp : FieldCapacity.NoWrap p 131072) (initial : State)
    {native : RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    (nativeAccepted : MixedMemoryAccepted native program)
    (ram : ExternalBoundary.WorkerRAM.Binding native.workers.rows) :
    MixedMemoryAccepted (view initial native) program := by
  constructor
  · constructor
    · intro row member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact UnifiedReduced.ROMView.row_holds (by omega) initial original native.machine.rom
        (nativeAccepted.active original present) (nativeAccepted.constraints original present)
    · intro row member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      have flag := nativeAccepted.active original present
      unfold UnifiedReduced.ROMView.row
      split <;> exact flag
    · simpa [view, UnifiedReduced.ROMView.data, List.map_map, Function.comp_def] using nativeAccepted.states
    · intro row member
      rw [callers] at member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      simpa only [caller_query, view] using nativeAccepted.decoded original present
    · exact nativeAccepted.workerConstraints
    · exact nativeAccepted.workerActive
    · change Delegation.Requests.Matching (view initial native).calls native.fulfillments
      rw [calls]
      exact nativeAccepted.requests
  · intro row member outside
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    have unselected : original ∉ native.callers := by
      intro included
      exact outside ((callers initial native).symm ▸ List.mem_map.mpr ⟨original, included, rfl⟩)
    simpa only [UnifiedReduced.ROMView.row_query] using nativeAccepted.ordinaryDecoded original present unselected
  · have matching := nativeAccepted.memory.map (Trace.ROMView.token initial)
    have reads := congrArg (List.map Prod.fst) (steps hp initial nativeAccepted ram)
    have writes := congrArg (List.map Prod.snd) (steps hp initial nativeAccepted ram)
    simp only [List.map_map, Function.comp_def] at reads writes
    change ((native.machine.initialMemory.map (Trace.ROMView.token initial)) ++ _).Perm
      ((native.machine.terminalMemory.map (Trace.ROMView.token initial)) ++ _)
    rw [reads, writes]
    simpa only [List.map_append, List.map_map, Function.comp_def] using matching

theorem inputs [Fact p.Prime] (hp : FieldCapacity.NoWrap p 4)
    {native : RequestTrace p} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {cells : List Cell} (boot : Inputs native program initial cells) :
    ∃ ca oa, MixedMemoryInputs (view initial native) program initial ca oa cells := by
  obtain ⟨ca, callerImage⟩ := boot.callers
  obtain ⟨oa, ordinaryImage⟩ := boot.machine.programImage
  obtain ⟨image, physical⟩ := boot.machine.image
  have seed := Trace.ROMView.seed_image boot.machine.profile physical
  have clocks := Trace.ROMView.native_clocks hp boot.machine.seed boot.machine.initialPC
  refine ⟨ca, oa, ⟨?_, clocks.initial, clocks.aligned⟩, ordinaryImage, ?_, ?_,
    boot.machine.aligned, boot.machine.setup, boot.tables, boot.rounds⟩
  · exact callerImage
  · change initialImage initial cells = some (native.machine.initialMemory.map (Trace.ROMView.token initial))
    rw [boot.machine.seed, seed]
    exact physical
  · exact boot.machine.distinct.map Trace.Proofs.cell_address_injective

theorem memory_soundness
    {native : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {cells : List Cell}
    (nativeAccepted : MixedMemoryAccepted native program) (boot : Inputs native program initial cells)
    (ram : ExternalBoundary.WorkerRAM.Binding native.workers.rows) :
    MixedMemoryEffects (view initial native) initial cells := by
  obtain ⟨ca, oa, physical⟩ := inputs (by decide) boot
  exact Caller.Proofs.mixed_memory_effects (accepted (by decide) initial nativeAccepted ram) physical

theorem ram_binding_of_inputs
    {data : RequestTrace babyBearModulus} {program : List UnifiedReduced.ProgramEntry}
    {initial : State} {cells : List Cell} {ca oa : List (BitVec 32)}
    (nativeAccepted : MixedMemoryAccepted data program)
    (physical : MixedMemoryInputs data program initial ca oa cells)
    (domain : ∀ address, Cell.ram address ∈ cells → ROM.limit ≤ address.toNat) :
    ExternalBoundary.WorkerRAM.Binding data.workers.rows := by
  have effects := Caller.Proofs.mixed_memory_effects nativeAccepted physical
  intro worker member port present
  obtain ⟨cell, included, code, _⟩ := effects.addresses _
    (Caller.Proofs.mixed_worker_member member present)
  cases cell with
  | register index => exact ⟨.register index, code.symm⟩
  | ram addr => exact ⟨.ram addr (domain addr included), code.symm⟩

end Airbender.UnifiedReduced.Caller.NativeROM.Proofs
