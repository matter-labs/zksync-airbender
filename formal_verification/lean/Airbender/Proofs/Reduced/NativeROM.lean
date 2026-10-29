import Airbender.Proofs.Reduced.ROMAddresses
import Airbender.Proofs.Trace.PooledROMView
import Airbender.Proofs.ExternalBoundary.WorkerRAM

namespace Airbender.Delegation.Caller.NativeROM
open Trace Reference.RiscV.Sail

/-- Interpret public ROM bytes in the actual pooled machine assignments. -/
def view [Fact p.Prime] (initial : State) (native : RequestTrace p) : RequestTrace p :=
  { native with machine := PooledROMView.data initial native.machine }

namespace Proofs
open Arithmetic Trace.Proofs
open AddSub.Modular.External.Caller.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

theorem caller_row [Fact p.Prime] (initial : State) {data : RequestTrace p}
    {row : Trace.Row p PooledFamily} (member : row ∈ data.callers) :
    PooledROMView.row initial row = row := by
  have family := (Caller.Proofs.caller_member member).2
  rcases row with ⟨kind, w⟩
  cases family
  rfl

theorem callers [Fact p.Prime] (initial : State) (data : RequestTrace p) :
    (view initial data).callers = data.callers.map (PooledROMView.row initial) := by
  simp only [RequestTrace.callers, view, PooledROMView.data, List.filter_map]
  congr 1
  apply List.filter_congr
  intro row _
  simp only [Function.comp_apply, PooledROMView.row_family]
  rcases row with ⟨kind, w⟩
  cases kind <;> rfl

theorem callers_unchanged [Fact p.Prime] (initial : State) (data : RequestTrace p) :
    (view initial data).callers = data.callers := by
  rw [callers]
  simpa only [List.map_id] using
    (List.map_congr_left (f := PooledROMView.row initial) (g := id)
      (fun _ member => caller_row initial member))

theorem calls [Fact p.Prime] (initial : State) (data : RequestTrace p) :
    (view initial data).calls = data.calls := by
  simp only [RequestTrace.calls, callers_unchanged]

theorem zip_maps (items : List α) (left : α → β) (right : α → γ) :
    (items.map left).zip (items.map right) = items.map (fun item => (left item, right item)) := by
  induction items <;> simp_all

theorem machine_steps [Fact p.Prime] (hp : FieldCapacity.NoWrap p 131072) (initial : State)
    {data : RequestTrace p} {program : List PooledProgramEntry}
    (accepted : MixedMemoryAccepted data program) (requests : RequestBinding data initial)
    (facts : Transfer.Facts (mixedData data)) {cells : List Cell}
    (seed : data.machine.initialMemory = ROMView.nativeBootImage cells)
    {row : Trace.Row p PooledFamily} (member : row ∈ data.machine.rows) :
    (machinePorts (PooledROMView.row initial row)).toList.map (fun port =>
      (readToken (PooledROMView.row initial row).assignment port,
        writeToken (PooledROMView.row initial row).columns
          (PooledROMView.row initial row).assignment port)) =
    ((machinePorts row).toList.map (fun port =>
      (readToken row.assignment port, writeToken row.columns row.assignment port))).map
        (fun edge => (ROMView.token initial edge.1, ROMView.token initial edge.2)) := by
  by_cases caller : row ∈ data.callers
  · rw [caller_row initial caller]
    rw [machine_ports_caller caller, List.map_map]
    apply List.map_congr_left
    intro port present
    have modes : port = AddSub.importedConstraintsMemoryPorts[0] ∨
        port = AddSub.importedConstraintsMemoryPorts[2] := by
      simpa [architecturalPorts] using present
    have binding := (requests.callers row caller).1
    have same : (readToken row.assignment port).address = (Cell.register 0).addressCode := by
      rcases modes with rfl | rfl
      · exact binding.sourceAddress
      · exact binding.destinationAddress
    have outside : ¬ ROMView.shadow (readToken row.assignment port).address := by
      rw [same]
      simp [Cell.addressCode, ROMView.shadow]
    have address : (writeToken row.columns row.assignment port).address =
        (readToken row.assignment port).address := rfl
    simp only [Function.comp_apply, ROMView.token, address, outside, if_false]
  · have lifted : PooledROMView.row initial row ∉ (view initial data).callers := by
      rw [callers]
      intro included
      obtain ⟨original, present, equal⟩ := List.mem_map.mp included
      have same := congrArg Trace.Row.family equal
      rw [PooledROMView.row_family, PooledROMView.row_family] at same
      have selected := (Caller.Proofs.caller_member present).2
      have nativeFamily : row.family = .addSub := same.symm.trans selected
      have nativeView : PooledROMView.row initial row = row := by
        rcases row with ⟨kind, w⟩
        cases nativeFamily
        rfl
      have equalRows : original = row := (caller_row initial present).symm.trans (equal.trans nativeView)
      exact caller (equalRows ▸ present)
    have liftedMember : PooledROMView.row initial row ∈ (view initial data).machine.rows :=
      List.mem_map.mpr ⟨row, member, rfl⟩
    rw [machine_ports_ordinary liftedMember lifted,
      machine_ports_ordinary member caller]
    have transfers := PooledROMView.row_transfers hp initial row data.machine.rom
      (accepted.constraints row member) (native_ordinary_addresses facts seed member caller)
    calc
      _ = (PooledROMView.row initial row).reads.zip (PooledROMView.row initial row).writes :=
        (zip_maps _ _ _).symm
      _ = (row.reads.map (ROMView.token initial)).zip (row.writes.map (ROMView.token initial)) := by
        rw [transfers.1, transfers.2]
      _ = (row.reads.zip row.writes).map
          (Prod.map (ROMView.token initial) (ROMView.token initial)) := List.zip_map
      _ = _ := by rw [Trace.Row.reads, Trace.Row.writes, zip_maps]; rfl

theorem steps [Fact p.Prime] (hp : FieldCapacity.NoWrap p 131072) (initial : State)
    {data : RequestTrace p} {program : List PooledProgramEntry}
    (accepted : MixedMemoryAccepted data program) (requests : RequestBinding data initial)
    (facts : Transfer.Facts (mixedData data)) {cells : List Cell}
    (seed : data.machine.initialMemory = ROMView.nativeBootImage cells)
    (ram : ExternalBoundary.WorkerRAM.Binding data.workers.rows) :
    (view initial data).mixedSteps = data.mixedSteps.map
      (fun edge => (ROMView.token initial edge.1, ROMView.token initial edge.2)) := by
  simp only [RequestTrace.mixedSteps, view, PooledROMView.data, List.flatMap_map, List.map_append]
  rw [ExternalBoundary.WorkerRAM.Proofs.pool_transfers_unchanged initial ram]
  congr 1
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro row member
  exact machine_steps hp initial accepted requests facts seed member

end Proofs
end Airbender.Delegation.Caller.NativeROM
