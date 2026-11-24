module
public import Proven.Trace.Machine.WorkerEvents

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Delegation
set_option warningAsError true

/-- The common proof view of standard and split native rows. -/
abbrev AnyWorker (p : Nat) := Delegation.Row p ⊕ Keccak.Split.Native.Row p

/-- Retain every submitted worker occurrence. -/
def anyWorkers (workers : WorkerPools p) : List (AnyWorker p) :=
  workers.standard.rows.map Sum.inl ++ workers.split.rows.map Sum.inr

/-- The full CSR and invocation clock of either native worker kind. -/
def AnyWorker.request (row : AnyWorker p) : Requests.Request p :=
  match row with
  | .inl standard => Requests.fulfillment standard
  | .inr split => splitFulfillment split

/-- The unchanged native architectural transfers of either kind. -/
def AnyWorker.steps (row : AnyWorker p) : List (MemoryToken p × MemoryToken p) :=
  match row with
  | .inl standard => standard.memorySteps
  | .inr split => split.memorySteps

/-- The common view preserves the existing request list. -/
theorem any_worker_requests (workers : WorkerPools p) :
    (anyWorkers workers).map AnyWorker.request = workers.fulfillments := by
  simp [anyWorkers, AnyWorker.request, WorkerPools.fulfillments, List.map_map, Function.comp_def]

/-- The common view preserves the existing transfer list. -/
theorem any_worker_steps (workers : WorkerPools p) :
    (anyWorkers workers).flatMap AnyWorker.steps = workers.steps := by
  simp [anyWorkers, AnyWorker.steps, WorkerPools.steps, Delegation.MemoryData.steps,
    Keccak.Split.Native.MemoryData.steps, List.flatMap_map]

/-- Both native kinds place their memory events at the matched worker tick. -/
theorem any_worker_event_time {workers : WorkerPools babyBearModulus} (clocks : WorkerClocks workers)
    {row : AnyWorker babyBearModulus} (member : row ∈ anyWorkers workers)
    {event : MemoryAccess} (present : event ∈ row.steps.map transferEvent) :
    event.1 = (timeOfPair row.request.time).value + 3 := by
  cases row with
  | inl standard =>
    have included : standard ∈ workers.standard.rows := by simpa [anyWorkers] using member
    exact standard_event_time clocks included present
  | inr split =>
    have included : split ∈ workers.split.rows := by simpa [anyWorkers] using member
    exact split_event_time clocks included present

end Airbender.Trace.Machine.Proofs
