import Airbender.Proofs.FullUnsigned.OrdinaryCycles
import Airbender.Proofs.FullUnsigned.StandardCycles
import Airbender.Proofs.FullUnsigned.SplitCycles
import Airbender.Proofs.Trace.IndexedCycleComposition
import Airbender.Proofs.Trace.ExternalComposition

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail Reference.Sail
open AddSub.Modular.External.Caller
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Native ordinary, standard and split cycles share one indexed full transition.
Only input contracts remain: no native call or instruction result is a premise. -/
theorem unrolled_full_cycle_transition
    {initial finalState : State}
    (bundles : List UnifiedReduced.Caller.DelegationUse.Bundle) (splitBundles : List Keccak.Split.Bundle) {text : List (BitVec 32)} {capacity : Nat}
    {masks : PooledFamily → NativeDecoder.ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {splitWorkers : Keccak.Split.Native.MemoryData babyBearModulus}
    (setup : UnrolledProgramSetup .fullUnsigned initial text capacity masks columns)
    (lookup : UnrolledDecoderExactLookup trace masks columns)
    (accepted : UnrolledAcceptance trace workers splitWorkers.steps
      (splitWorkers.rows.map (Keccak.Split.Native.Row.fulfillment splitWorkers.cached)))
    (excluded : FullUnsigned.NoSpecial5Call initial text)
    (initialPC : trace.initial.word.lo < limbBase)
    (closure : VerifierBoundary.BootClosure trace.initial
      (trace.rows.map Row.start) (trace.rows.map Row.finish))
    (equations : Keccak.Split.Native.EquationsHold splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (fixedEquations : Keccak.Split.Native.EquationsHold
      splitWorkers.cached Keccak.Split.Native.Proofs.fixedSetup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows, row.assignment (row.columns splitWorkers.cached).execute = 1)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {cells : List Cell} {physicalImage : List (MemoryToken babyBearModulus)}
    (image : initialImage initial cells = some physicalImage)
    (wordSetup : trace.rom.wordMemory = ROM.table cells physicalImage)
    (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.words initial))
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (profile : PooledPublicInputs initial cells
      (NativeDecoder.ProgramRows.programOf .fullUnsigned initial text))
    {events : List MemoryAccess}
    (permutation : events.Perm ((unrolledFullMemoryData trace workers splitWorkers).steps.map transferEvent))
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events initial finalState)
    (readonly : ∀ event ∈ events, ∀ pc : BitVec 32, pc.toNat < ROM.limit →
      event.2.1 = (Cell.ram pc).addressCode → event.2.2.1 = event.2.2.2)
    (facts : Transfer.Facts (unrolledFullMemoryData trace workers splitWorkers))
    (inputs : Transfer.NativeInputs (unrolledFullMemoryData trace workers splitWorkers) initial cells)
    (workerSetup : workers.setup = Delegation.modeledSetup Keccak.Controller.rows)
    (workerFamilies : ∀ worker ∈ workers.rows, FullUnsigned.standardCall worker.family)
    (bounds : ∀ edge ∈ (unrolledFullMemoryData trace workers splitWorkers).steps,
      edge.1.word.Bounded ∧ edge.2.word.Bounded)
    (ram : ExternalBoundary.WorkerRAM.Binding workers.rows)
    (commands : ∀ worker ∈ workers.rows, worker.family = .bigint →
      ∃ command, ExternalBoundary.BigintABI.Binding worker.assignment command)
    (controls : ∀ w, (⟨.blakeRound, w⟩ : Delegation.Row babyBearModulus) ∈ workers.rows →
      ExternalBoundary.HashABI.RoundControl w)
    (splitInputs : ∀ row ∈ trace.rows, ∀ worker ∈ splitWorkers.rows,
      worker.fulfillment splitWorkers.cached = Delegation.Requests.caller row.assignment →
      ∀ before, SailHistory cells (events.filter fun event => decide (event.1 ≤ row.clock)) initial before →
        ∃ index : Fin 361, Keccak.Split.ArgumentsAt index.val before)
    (stream : List (BitVec 32)) (ports : NonDeterminism.Pooled.StreamPorts trace stream)
    {row : Trace.Row babyBearModulus PooledFamily} (member : row ∈ trace.rows) :
    let program := FullUnsigned.Program.ofText initial text bundles splitBundles
    ∃ before after,
      CutState cells events initial (timeOfPair row.start.timestamp).value before ∧
      CutState cells events initial (timeOfPair row.finish.timestamp).value after ∧
      FullUnsigned.Step stream program
        (retiredState before row.start.word.toBitVec, countAt trace row.clock)
        (retiredState after row.finish.word.toBitVec, countAt trace (timeOfPair row.finish.timestamp).value) ∧
      (run (SailRV32.Functions.get_arch_pc ()) before = .ok row.start.word.toBitVec before →
        FullUnsigned.Step stream program (before, countAt trace row.clock)
          (retiredState after row.finish.word.toBitVec, countAt trace (timeOfPair row.finish.timestamp).value)) := by
  let program := FullUnsigned.Program.ofText initial text bundles splitBundles
  have clocks := state_clock_inputs (by decide)
    (by decide +kernel : SerializedInverse.Clock babyBearModulus)
    accepted.cpuEquations accepted.states initialClock initialAligned row member
  have advance := ClockLaws.advance (by decide)
    (by decide +kernel : SerializedInverse.Clock babyBearModulus) trace.rom row
    (accepted.cpuEquations row member) clocks.1
  change (timeOfPair row.finish.timestamp).value = row.clock + 4 at advance
  have orderedClocks : (timeOfPair row.start.timestamp).value ≤ (timeOfPair row.finish.timestamp).value := by
    change row.clock ≤ (timeOfPair row.finish.timestamp).value
    omega
  have count := unrolled_full_cycle_count accepted initialClock initialAligned member
  by_cases caller : row.family = .addSub ∧ Delegation.Requests.Selected row.assignment
  · have noRead := unrolled_full_caller_read_disabled setup lookup accepted excluded initialPC
      row member caller.1 caller.2
    have sameCount : countAt trace (timeOfPair row.finish.timestamp).value = countAt trace row.clock := by
      simpa [countAt, noRead] using count
    have ledger := unrolled_full_requests_match accepted equations active initialClock initialAligned
    have issued : Delegation.Requests.caller row.assignment ∈ pooledCalls trace := by
      apply List.mem_map.mpr
      refine ⟨row, List.mem_filter.mpr ⟨member, ?_⟩, rfl⟩
      simp only [caller.1, beq_self_eq_true, caller.2, decide_true, Bool.and_self]
    rcases List.mem_append.mp (ledger.mem_iff.mp issued) with standard | split
    · obtain ⟨worker, present, matched⟩ := List.mem_map.mp standard
      obtain ⟨before, after, past, current, _, entry, included, query, pc, source, raw, retired⟩ :=
        unrolled_full_standard_caller_cycle setup lookup accepted excluded initialPC equations active
          initialClock initialAligned facts inputs workerSetup bounds ram commands controls row member
          caller.1 caller.2 worker present (workerFamilies worker present) matched permutation ordered history readonly aligned
      have allowed := (unrolled_full_caller_metadata
        (text_caller_sources FullUnsigned.standardDecoderFields initial text setup.image setup.size entry included).fields).2
      refine ⟨before, after, past, history_prefix_of_window ordered orderedClocks past current,
        Or.inl (Or.inr ⟨sameCount.symm, entry, included, allowed,
          entry_source_retired_state source _, ?_, retired⟩), ?_⟩
      · rw [← pc]
        exact retired_state_pc before _
      · intro read
        have binding := unrolled_full_standard_pc_binding setup lookup accepted excluded initialPC
          row member caller.1 caller.2 worker matched
        have start : Delegation.Caller.initialPC row.assignment = row.start.word := by
          cases row with | mk kind w => cases caller.1; rfl
        have finish : Delegation.Caller.finalPC row.assignment = row.finish.word := by
          cases row with | mk kind w => cases caller.1; rfl
        refine Or.inl (Or.inr ⟨sameCount.symm, entry, included, allowed,
          source, pc ▸ read, after, raw, ?_⟩)
        simpa only [finish, retiredState] using binding.sail after
          (by simpa only [start] using sail_history_pc_read current read)
    · obtain ⟨worker, present, matched⟩ := List.mem_map.mp split
      obtain ⟨before, after, past, current, _, entry, included, source, pc, query, sameKind, executes⟩ :=
        unrolled_full_split_caller_cycle setup lookup accepted excluded initialPC workerFamilies equations
          fixedEquations active initialClock initialAligned inputs (fun edge present => (bounds edge present).1)
          row member caller.1 caller.2 worker present matched permutation ordered history readonly aligned
      obtain ⟨index, arguments⟩ := splitInputs row member worker present matched before past
      obtain ⟨raw, retired⟩ := executes index arguments
      refine ⟨before, after, past, history_prefix_of_window ordered orderedClocks past current,
        Or.inr ⟨sameCount.symm, entry, included, entry_source_retired_state source _, ?_, sameKind ▸ retired⟩, ?_⟩
      · rw [← pc]
        exact retired_state_pc before _
      · intro read
        have binding := unrolled_full_split_pc_binding setup lookup accepted excluded initialPC workerFamilies
          equations active initialClock initialAligned row member caller.1 caller.2 worker matched
        have start : Delegation.Caller.initialPC row.assignment = row.start.word := by
          cases row with | mk kind w => cases caller.1; rfl
        have finish : Delegation.Caller.finalPC row.assignment = row.finish.word := by
          cases row with | mk kind w => cases caller.1; rfl
        refine Or.inr ⟨sameCount.symm, entry, included, source, pc ▸ read, after, sameKind ▸ raw, ?_⟩
        simpa only [finish, retiredState] using binding.sail after
          (by simpa only [start] using sail_history_pc_read current read)
  · obtain ⟨entry, included, family, query, clause, next, selected, counter,
        before, after, past, current, _, retired⟩ :=
      unrolled_full_ordinary_cycle setup lookup accepted excluded initialPC closure equations active
        initialClock initialAligned image wordSetup subwordSetup aligned profile permutation ordered history
        readonly (fun edge present => (bounds edge present).1) stream ports member caller
    have pcWord := native_query_pc_word (by decide) query
    change row.start.word = Word.ofBitVec entry.pc at pcWord
    have pc := (congrArg Word.toBitVec pcWord).trans (Word.ofBitVec_roundtrip _)
    have source := entry_source_after_history past
      (fun event present => readonly event (List.mem_filter.mp present).1)
      (run_program_sources (unrolled_full_ordinary_image setup.image setup.size) entry included)
      (profile.code entry included).1 (profile.code entry included).2
    have nextCount : next = countAt trace (timeOfPair row.finish.timestamp).value := counter.trans count.symm
    have step : NonDeterminism.StepWithClause AddSub.Modular.External.decoderFields AddSub.Modular.External.clause
        stream program.ordinary
        (retiredState before row.start.word.toBitVec, countAt trace row.clock)
        (retiredState after row.finish.word.toBitVec, countAt trace (timeOfPair row.finish.timestamp).value) := by
      refine ⟨entry, included, entry_source_retired_state source _, pc ▸ retired_state_pc before _,
        clause, ?_, retired⟩
      rw [← nextCount]
      exact selected
    exact ⟨before, after, past, history_prefix_of_window ordered orderedClocks past current,
      Or.inl (Or.inl step), fun read => Or.inl (Or.inl (ExternalStream.Proofs.step_of_rebased_with_clause read step))⟩

end Airbender.Compiler.MachineTargets.Proofs
