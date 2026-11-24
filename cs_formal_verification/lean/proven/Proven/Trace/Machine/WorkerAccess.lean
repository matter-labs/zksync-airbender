module
public import Proven.Trace.Machine.AnyWorker
public import Proven.Trace.Machine.MemoryAccess
public import Proven.Trace.Machine.WorkerZero

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Delegation Trace.Proofs
set_option warningAsError true

/-- A worker occurrence retains its full transfer list inside the combined pool. -/
theorem any_worker_steps_sublist {workers : WorkerPools p} {row : AnyWorker p}
    (member : row ∈ anyWorkers workers) : row.steps.Sublist workers.steps := by
  obtain ⟨before, after, same⟩ := List.append_of_mem member
  rw [← any_worker_steps, same, List.flatMap_append, List.flatMap_cons]
  exact (List.sublist_append_left _ _).trans (List.sublist_append_right _ _)

/-- No event of either native worker kind addresses x0. -/
theorem any_worker_events_not_zero {workers : WorkerPools p} {row : AnyWorker p}
    (member : row ∈ anyWorkers workers) :
    ∀ event ∈ row.steps.map transferEvent, event.2.1 ≠ (Cell.register 0).addressCode := by
  intro event present
  obtain ⟨edge, included, rfl⟩ := List.mem_map.mp present
  exact worker_not_zero ((any_worker_steps_sublist member).subset included)

/-- Shared memory matching derives distinct addresses within each actual native worker call. -/
theorem any_worker_addresses_distinct {data : Transfer.Data babyBearModulus}
    {workers : WorkerPools babyBearModulus} {initial : RV.State} {cells : List Cell}
    (facts : Transfer.Facts data) (image : initialImageRV initial cells = some data.initial)
    (distinct : cells.Nodup) (pool : workers.steps.Sublist data.steps) (clocks : WorkerClocks workers)
    {row : AnyWorker babyBearModulus} (member : row ∈ anyWorkers workers) :
    (row.steps.map fun edge => edge.1.address).Nodup := by
  apply same_tick_addresses_distinct (shared_access_keys_unique facts image (distinct.map cell_address_injective))
    ((any_worker_steps_sublist member).trans pool)
  intro edge included
  exact any_worker_event_time clocks member (List.mem_map.mpr ⟨edge, included, rfl⟩)

end Airbender.Trace.Machine.Proofs
