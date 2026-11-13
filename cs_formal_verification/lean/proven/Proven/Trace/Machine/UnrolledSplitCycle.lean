module
public import Proven.Trace.Machine.SplitCallerCut
public import Proven.Trace.Machine.CallerAddresses
public import Proven.Trace.Machine.CallerRetirement
public import Proven.Trace.Machine.WorkerKind
public import Proven.Trace.Machine.CycleGroups

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Delegation Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- An accepted unrolled caller cycle executes its fetched split Keccak instruction. -/
theorem unrolled_split_cycle {config : RVMachineConfig} (unrolled : config ≠ .unified)
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
    {worker : Keccak.Split.Native.Row babyBearModulus} (workerMember : worker ∈ workers.split.rows)
    (matched : splitFulfillment worker = Requests.caller row.assignment)
    {events : List MemoryAccess} (permutation : events.Perm ((unrolledMemory trace workers).steps.map transferEvent))
    (history : RVHistory cells (events.filter fun event => decide (row.clock < event.1 ∧ event.1 ≤ row.clock + 4)) before after)
    (rom : before.rom = initialState.rom) :
    ∃ next, RV.step (before.setPC entry.pc) = some next ∧ RV.Same next (after.setPC row.finish.word.toBitVec) := by
  have member := (unrolled_caller_member called).1
  have family := (unrolled_caller_member called).2
  obtain ⟨tag, w⟩ := row
  change tag = .addSub at family
  subst tag
  have selected : w 17 = 1 := by
    simpa [Requests.Selected, AddSub.importedConstraintsDecoderColumns] using (List.mem_filter.mp called).2
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left AddSub.importedConstraints AddSub.importedConstraintsTimestampLookups)
  have csr := machine_csr_value fields query
  have kindMatch : worker.kind.delegation = kind := by
    apply any_worker_kind (row := Sum.inr worker)
    exact (congrArg Requests.Request.csr matched).trans csr
  have included : Sum.inr worker ∈ anyWorkers workers := by simp [anyWorkers, workerMember]
  have grouped := unrolled_caller_cycle_group accepted initial alignedClock permutation called included matched
  have facts := unrolled_memory_facts accepted initial alignedClock image
  have writes := unrolled_write_rules unrolled accepted initial alignedClock programImage wordSetup subwordSetup tables
  have zero := unrolled_zero_rules unrolled accepted initial alignedClock programImage
  have native : ∀ event ∈ events.filter (fun event => decide
      ((⟨.addSub, w⟩ : Row babyBearModulus PooledFamily).clock < event.1 ∧
        event.1 ≤ (⟨.addSub, w⟩ : Row babyBearModulus PooledFamily).clock + 4)),
      event ∈ (unrolledMemory trace workers).steps.map transferEvent := by
    intro event present
    exact permutation.mem_iff.mp (List.mem_of_mem_filter present)
  have call := split_caller_cut_call facts image distinct aligned (List.sublist_append_right _ _)
    (unrolled_worker_clocks accepted initial alignedClock).1 accepted.toWorkersAccepted writes zero workerMember
    grouped history (unrolled_caller_addresses fields query selected) native entry.pc
  rw [kindMatch] at call
  exact fetched_delegate_cycle programImage present decoded rom (unrolled_caller_retirement core query) call

end Airbender.Trace.Machine.Proofs
