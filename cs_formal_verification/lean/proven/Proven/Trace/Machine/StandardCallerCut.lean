module
public import Proven.Trace.Machine.StandardCall
public import Proven.Trace.Machine.CallerHistory
public import Proven.Trace.Machine.WorkerAccess
public import Proven.Trace.Machine.ZeroWrites
public import Proven.Trace.Machine.MemoryBounds

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Delegation Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- A matched standard worker in a caller cut executes its RV call from derived shared-memory reads. -/
theorem standard_caller_cut_call {data : Transfer.Data babyBearModulus} {workers : WorkerPools babyBearModulus}
    {initial before after : RV.State} {cells : List Cell} {events cpu : List MemoryAccess}
    (facts : Transfer.Facts data) (image : initialImageRV initial cells = some data.initial)
    (distinctCells : cells.Nodup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    (pool : workers.steps.Sublist data.steps) (clocks : WorkerClocks workers)
    (accepted : WorkersAccepted workers) (tables : workers.standard.setup = modeledSetup Keccak.Controller.rows)
    (writeRules : Transfer.WriteRules data) (zeroRules : Transfer.CellWriteRules data (Cell.register 0).addressCode 0)
    {worker : Delegation.Row babyBearModulus} (member : worker ∈ workers.standard.rows)
    (permutation : events.Perm (cpu ++ worker.memorySteps.map transferEvent))
    (history : RVHistory cells events before after)
    (callerZero : ∀ event ∈ cpu, event.2.1 = (Cell.register 0).addressCode)
    (native : ∀ event ∈ events, event ∈ data.steps.map transferEvent)
    (notSpecial : worker.family ≠ .keccak) (pc : RV.Word) :
    ∃ next, RV.exec (before.setPC pc) (.delegate (standardKind worker.family)) = some next ∧
      RV.Same next (after.setPC (pc + 4)) := by
  have included : Sum.inl worker ∈ anyWorkers workers := by simp [anyWorkers, member]
  have unique : (worker.memorySteps.map fun edge => edge.1.address).Nodup := by
    simpa only [AnyWorker.steps] using any_worker_addresses_distinct facts image distinctCells pool clocks included
  have noZero := any_worker_events_not_zero included
  have zero : ∀ event ∈ events, event.2.1 = (Cell.register 0).addressCode → memoryWord event.2.2.2 = 0 := by
    intro event present
    exact shared_zero_writes facts image zeroRules event (native event present)
  obtain ⟨grouped, actual⟩ := caller_worker_history permutation history callerZero noZero zero
  have addressUnique : ((worker.memorySteps.map transferEvent).map fun event => event.2.1).Nodup := by
    simpa only [List.map_map, Function.comp_def, transferEvent] using unique
  have observations := caller_worker_observations permutation history callerZero noZero zero aligned addressUnique
  have ports : ∀ port ∈ worker.ports, ∃ cell ∈ cells, cell.addressCode = port.address.code worker.assignment ∧
      cell.readRV before = some (memoryWord (port.readCode worker.assignment)) ∧
      cell.readRV after = some (memoryWord (port.writeCode worker.assignment)) := by
    intro port present
    have event : transferEvent (readToken worker.assignment port, worker.writeToken port) ∈ worker.memorySteps.map transferEvent :=
      List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨port, by simpa using present, rfl⟩, rfl⟩
    exact observations _ event
  have allBounds := (Delegation.Caller.Proofs.rv_transfer_bounds facts (RVValues.rv_image_bounds image) writeRules).1
  have reads : ∀ port ∈ worker.ports, (readToken worker.assignment port).word.Bounded := by
    intro port present
    have step : (readToken worker.assignment port, worker.writeToken port) ∈ worker.memorySteps :=
      List.mem_map.mpr ⟨port, by simpa using present, rfl⟩
    exact (allBounds _ (pool.subset ((any_worker_steps_sublist included).subset step))).1
  have holds := accepted.standardConstraints worker member
  rw [tables] at holds
  exact standard_native_call holds (accepted.standardActive worker member) reads ports unique actual grouped aligned notSpecial pc

end Airbender.Trace.Machine.Proofs
