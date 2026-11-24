module
public import Proven.Trace.Machine.StandardCallerCut
public import Proven.Trace.Machine.CallerAddresses
public import Proven.Trace.Machine.CallerRetirement
public import Proven.Trace.Machine.WorkerKind
public import Proven.Trace.Machine.CycleGroups

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Delegation Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- An accepted unified caller cycle executes its fetched bigint, G or arbitrary-mask round instruction. -/
theorem unified_standard_cycle
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
    {worker : Delegation.Row babyBearModulus} (workerMember : worker ∈ workers.standard.rows)
    (matched : Requests.fulfillment worker = UnifiedReduced.Caller.request row.assignment) (notSpecial : kind ≠ .keccak)
    {events : List MemoryAccess} (permutation : events.Perm ((unifiedMemory trace workers).steps.map transferEvent))
    (history : RVHistory cells (events.filter fun event => decide (row.clock < event.1 ∧ event.1 ≤ row.clock + 4)) before after)
    (rom : before.rom = initialState.rom) :
    ∃ next, RV.step (before.setPC entry.pc) = some next ∧ RV.Same next (after.setPC row.finish.word.toBitVec) := by
  have member := (List.mem_filter.mp called).1
  obtain ⟨tag, w⟩ := row
  cases tag
  have selected : w 18 = 1 := of_decide_eq_true (List.mem_filter.mp called).2
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (UnifiedReduced.importedConstraints trace.rom)
      UnifiedReduced.importedConstraintsTimestampLookups)
  have csr := machine_csr_value fields query
  have kindMatch : standardKind worker.family = kind := by
    apply any_worker_kind (row := Sum.inl worker)
    exact (congrArg Requests.Request.csr matched).trans csr
  have workerNotSpecial : worker.family ≠ .keccak := by
    intro same
    rw [same] at kindMatch
    exact notSpecial kindMatch.symm
  have included : Sum.inl worker ∈ anyWorkers workers := by simp [anyWorkers, workerMember]
  have grouped := unified_caller_cycle_group accepted initial alignedClock permutation called included matched
  have facts := unified_memory_facts accepted initial alignedClock image
  have writes := unified_write_rules accepted initial alignedClock tables
  have zero := unified_zero_rules accepted initial alignedClock programImage
  have native : ∀ event ∈ events.filter (fun event => decide
      ((⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).clock < event.1 ∧
        event.1 ≤ (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).clock + 4)),
      event ∈ (unifiedMemory trace workers).steps.map transferEvent := by
    intro event present
    exact permutation.mem_iff.mp (List.mem_of_mem_filter present)
  have call := standard_caller_cut_call facts image distinct aligned (List.sublist_append_right _ _)
    (unified_worker_clocks accepted initial alignedClock).1 accepted.toWorkersAccepted tables writes zero workerMember
    grouped history (unified_caller_addresses core fields query selected) native workerNotSpecial entry.pc
  rw [kindMatch] at call
  exact fetched_delegate_cycle programImage present decoded rom (unified_caller_retirement core (accepted.active _ member) fields query) call

end Airbender.Trace.Machine.Proofs
