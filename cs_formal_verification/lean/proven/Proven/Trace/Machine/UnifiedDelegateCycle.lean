module
public import Proven.Trace.Machine.UnifiedStandardCycle

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Delegation Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Exact full-CSR matching supplies the standard worker of each unified delegation cycle. -/
theorem unified_delegate_cycle
    {trace : UnifiedTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} {initialState before after : RV.State} {cells : List Cell} {addresses : List (BitVec 32)}
    (accepted : UnifiedAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (alignedClock : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (image : initialImageRV initialState cells = some trace.initialMemory)
    (distinct : cells.Nodup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    (programImage : rvMachineProgramImage .unified initialState addresses = some program)
    (tables : workers.standard.setup = modeledSetup Keccak.Controller.rows)
    {row : Row babyBearModulus UnifiedFamily} (called : row ∈ trace.rows.filter (fun source => decide (UnifiedReduced.Caller.Selected source.assignment)))
    {entry : RVMachineProgramEntry} (present : entry ∈ program) {kind : RV.DelegationKind}
    (decoded : RV.decode entry.bits = some (.delegate kind))
    (fields : rvMachineDecoderFields .unified (.delegate kind) = some entry.data)
    (query : row.decoderQuery = (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus)))
    (notSpecial : kind ≠ .keccak)
    {events : List MemoryAccess} (permutation : events.Perm ((unifiedMemory trace workers).steps.map transferEvent))
    (history : RVHistory cells (events.filter fun event => decide (row.clock < event.1 ∧ event.1 ≤ row.clock + 4)) before after)
    (rom : before.rom = initialState.rom) :
    ∃ next, RV.step (before.setPC entry.pc) = some next ∧ RV.Same next (after.setPC row.finish.word.toBitVec) := by
  have complete := unified_requests_complete accepted initial alignedClock
  have request : UnifiedReduced.Caller.request row.assignment ∈ workers.fulfillments :=
    complete.mem_iff.mp (List.mem_map.mpr ⟨row, called, rfl⟩)
  obtain ⟨chosen, included, matched, _⟩ := submitted_worker (unified_worker_clocks accepted initial alignedClock).2 request
  cases chosen with
  | inl standard =>
    have member : standard ∈ workers.standard.rows := by simpa [anyWorkers] using included
    exact unified_standard_cycle accepted initial alignedClock image distinct aligned programImage tables
      called present decoded fields query member matched notSpecial permutation history rom
  | inr split =>
    have csr := machine_csr_value fields query
    have kindMatch : split.kind.delegation = kind := by
      apply any_worker_kind (row := Sum.inr split)
      exact (congrArg Requests.Request.csr matched).trans csr
    have admitted := (machine_delegate_fields fields).1
    rw [← kindMatch] at admitted
    cases split with
    | mk tag w => cases tag <;> contradiction

end Airbender.Trace.Machine.Proofs
