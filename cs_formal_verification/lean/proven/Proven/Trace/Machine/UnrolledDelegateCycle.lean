module
public import Proven.Trace.Machine.UnrolledStandardCycle
public import Proven.Trace.Machine.UnrolledSplitCycle

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Delegation Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Exact request matching supplies the native worker of every unrolled delegation cycle. -/
theorem unrolled_delegate_cycle {config : RVMachineConfig} (unrolled : config ≠ .unified)
    {trace : PooledTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} {initialState before after : RV.State} {cells : List Cell} {addresses : List (BitVec 32)}
    (accepted : UnrolledAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (alignedClock : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (image : initialImageRV initialState cells = some trace.initialMemory)
    (distinct : cells.Nodup) (aligned : ∀ cell ∈ cells, cell.Aligned)
    (programImage : rvMachineProgramImage config initialState addresses = some program)
    (wordSetup : trace.rom.wordMemory = ROM.table cells (romImageRV initialState cells))
    (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.wordsRV initialState))
    (tables : workers.standard.setup = modeledSetup Keccak.Controller.rows)
    {row : Row babyBearModulus PooledFamily} (called : row ∈ unrolledCallers trace)
    {entry : RVMachineProgramEntry} (present : entry ∈ program) {kind : RV.DelegationKind}
    (decoded : RV.decode entry.bits = some (.delegate kind))
    (fields : rvMachineDecoderFields config (.delegate kind) = some entry.data)
    (query : row.decoderQuery = (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus)))
    (notSpecial : kind ≠ .keccak)
    {events : List MemoryAccess} (permutation : events.Perm ((unrolledMemory trace workers).steps.map transferEvent))
    (history : RVHistory cells (events.filter fun event => decide (row.clock < event.1 ∧ event.1 ≤ row.clock + 4)) before after)
    (rom : before.rom = initialState.rom) :
    ∃ next, RV.step (before.setPC entry.pc) = some next ∧ RV.Same next (after.setPC row.finish.word.toBitVec) := by
  have complete := unrolled_requests_complete accepted initial alignedClock
  have request : Requests.caller row.assignment ∈ workers.fulfillments :=
    complete.mem_iff.mp (List.mem_map.mpr ⟨row, called, rfl⟩)
  obtain ⟨chosen, included, matched, _⟩ := submitted_worker (unrolled_worker_clocks accepted initial alignedClock).2 request
  cases chosen with
  | inl standard =>
    have member : standard ∈ workers.standard.rows := by simpa [anyWorkers] using included
    exact unrolled_standard_cycle unrolled accepted initial alignedClock image distinct aligned programImage wordSetup
      subwordSetup tables called present decoded fields query member matched notSpecial permutation history rom
  | inr split =>
    have member : split ∈ workers.split.rows := by simpa [anyWorkers] using included
    exact unrolled_split_cycle unrolled accepted initial alignedClock image distinct aligned programImage wordSetup
      subwordSetup tables called present decoded fields query member matched permutation history rom

end Airbender.Trace.Machine.Proofs
