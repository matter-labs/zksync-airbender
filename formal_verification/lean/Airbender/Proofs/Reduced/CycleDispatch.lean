import Airbender.Review.Trace.Modular.ExternalCalls
import Airbender.Proofs.Reduced.PCBounds
import Airbender.Proofs.Reduced.StreamCount
import Airbender.Review.Helpers.Context.PooledBoundary

namespace Airbender.AddSub.Modular.External.Caller.Proofs
open Arithmetic Trace Trace.Proofs Reference.RiscV.Sail Reference.Sail
open Delegation.Caller Delegation.Caller.Proofs AddSub.Modular.External.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Every ordinary reduced instruction retires in its actual shared native cycle. -/
theorem ordinary_cycle_at
    {data : RequestTrace babyBearModulus} {program : List PooledProgramEntry}
    {initial : State} {ca oa : List (BitVec 32)} {cells : List Cell}
    (accepted : MixedMemoryAccepted data program)
    (inputs : StreamMemoryInputs data program initial ca oa cells)
    (profile : PooledPublicInputs initial cells program)
    (initialPositive : 0 < (timeOfPair data.machine.initial.timestamp).value)
    (closure : VerifierBoundary.BootClosure data.machine.initial
      (data.machine.rows.map Row.start) (data.machine.rows.map Row.finish))
    (families : ∀ row ∈ data.machine.rows, AddSub.Modular.External.Caller.reducedFamily row.family = true)
    (effects : MixedMemoryEffects data initial cells)
    {events : List MemoryAccess} {finalState : State}
    (permutation : events.Perm (data.mixedSteps.map transferEvent))
    (order : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    (readonly : ∀ event ∈ events, ∀ pc : BitVec 32, pc.toNat < ROM.limit →
      event.2.1 = (Cell.ram pc).addressCode → event.2.2.1 = event.2.2.2)
    (stream : List (BitVec 32)) (ports : External.StreamPorts data.machine stream)
    {row : Trace.Row babyBearModulus PooledFamily}
    (member : row ∈ data.machine.rows) (ordinary : row ∉ data.callers) :
    Caller.OrdinaryCycle stream program data.machine cells events initial finalState row := by
  obtain ⟨entry, present, source, family, query⟩ := mixed_ordinary_source accepted inputs member ordinary
  obtain ⟨before, after, past, current, future, native, ranges⟩ :=
    ordinary_context_at accepted inputs effects initialPositive permutation order history member ordinary
  suffices localRun : ∃ clause next,
      External.clause stream (External.readIndex data.machine row) entry.instruction = some (clause, next) ∧
      next = External.readIndex data.machine row + (if External.isRead row then 1 else 0) ∧
      run (normalStep clause) (retiredState before row.start.word.toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after row.finish.word.toBitVec) by
    obtain ⟨clause, next, selected, count, executed⟩ := localRun
    exact ⟨entry, present, family, query, clause, next, selected, count,
      before, after, past, current, future, executed⟩
  have constraints := accepted.constraints row member
  have active := accepted.active row member
  have readonlyPast : ∀ event ∈ events.filter (fun event => decide (event.1 ≤ row.clock)),
      ∀ pc : BitVec 32, pc.toNat < ROM.limit →
      event.2.1 = (Cell.ram pc).addressCode → event.2.2.1 = event.2.2.2 :=
    fun event included => readonly event (List.mem_filter.mp included).1
  cases row with
  | mk kind w =>
    cases kind with
    | addSub =>
      obtain ⟨clause, selected, executed⟩ := addsub_execution_from_shared_history (by decide) (by decide)
        inputs.initialization profile.registers constraints active ranges source family query
        (profile.loads entry present) (ports _ member) 1 past native
      exact ⟨clause, _, selected, rfl, executed⟩
    | shiftBinop =>
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left ShiftBinop.importedConstraints ShiftBinop.importedConstraintsTimestampLookups)
      have zeros : ∀ port ∈ ShiftBinop.importedConstraintsMemoryPorts,
          port.address.code w = (Cell.register 0).addressCode → (readToken w port).value = 0 := by
        intro port present atZero
        exact effects.zeroReads _ (mixed_machine_member member
          (by rw [machine_ports_ordinary member ordinary]; exact present)) atZero
      obtain ⟨clause, selected, executed⟩ := shift_execution_from_shared_history (by decide) (by decide)
        core active source family query zeros 1 native
      refine ⟨clause, _, clause_original selected, ?_, executed⟩
      simp [External.isRead, NonDeterminism.Pooled.isRead]
    | jumpBranchSlt =>
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left JumpBranchSlt.importedConstraints JumpBranchSlt.importedConstraintsTimestampLookups)
      have left := ranges JumpBranchSlt.importedConstraintsMemoryPorts[0] (Array.getElem_mem (by change 0 < 3; decide))
      have right := ranges JumpBranchSlt.importedConstraintsMemoryPorts[1] (Array.getElem_mem (by change 1 < 3; decide))
      have leftBound : (Word.mk (w 22).val (w 23).val).Bounded := by
        simpa [read_word, JumpBranchSlt.importedConstraintsMemoryPorts] using left
      have rightBound : (Word.mk (w 26).val (w 27).val).Bounded := by
        simpa [read_word, JumpBranchSlt.importedConstraintsMemoryPorts] using right
      have pcWord := native_query_pc_word (by decide) query
      have aligned : (w 0).val % 4 = 0 := by
        have low := congrArg Word.lo pcWord
        change (w 0).val = (Word.ofBitVec entry.pc).lo at low
        rw [low]
        simpa only [Word.ofBitVec, limbBase, Nat.mod_mod_of_dvd _ (by decide : 4 ∣ 65536)]
          using (profile.code entry present).2
      have finalHi : (w 17).val < limbBase := (native_pc_bounds (by decide) accepted closure _ member).2.2
      obtain ⟨clause, selected, executed⟩ := control_execution_from_shared_history (by decide)
        core active source family query leftBound rightBound aligned finalHi 1 past native
        profile.configuration.isa ⟨profile.configuration.privilege, profile.landingPadDisabled⟩
      refine ⟨clause, _, clause_original selected, ?_, executed⟩
      simp [External.isRead, NonDeterminism.Pooled.isRead]
    | wordMemory =>
      have addresses : ∀ port ∈ WordMemory.importedConstraintsMemoryPorts,
          ∃ cell ∈ cells, port.address.code w = cell.addressCode := by
        intro port present
        obtain ⟨cell, included, code, _⟩ := effects.addresses _ (mixed_machine_member member
          (by rw [machine_ports_ordinary member ordinary]; exact present))
        exact ⟨cell, included, code.symm⟩
      obtain ⟨clause, selected, executed⟩ := word_execution_from_shared_history (by decide) (by decide)
        inputs.initialization inputs.wordTable inputs.aligned profile.ordinary profile.configuration
        constraints active (ranges _ (Array.getElem_mem (by change 0 < 3; decide))) addresses
        source family query 1 readonlyPast past native
      refine ⟨clause, _, clause_original selected, ?_, executed⟩
      simp [External.isRead, NonDeterminism.Pooled.isRead]
    | mulDiv | subwordMemory =>
      have allowed := families _ member
      simp [AddSub.Modular.External.Caller.reducedFamily] at allowed

end Airbender.AddSub.Modular.External.Caller.Proofs
