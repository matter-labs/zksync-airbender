import Airbender.Proofs.FullUnsigned.PCBounds
import Airbender.Proofs.FullUnsigned.StreamCount
import Airbender.Proofs.FullUnsigned.SubwordExecution
import Airbender.Proofs.MulDiv.Composition
import Airbender.Proofs.Reduced.WordExecution
import Airbender.Review.Helpers.Delegation.StreamCycles

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail Reference.Sail
open Delegation.Caller AddSub.Modular.External.Caller.Proofs AddSub.Modular.External.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

private theorem history_zero_reads {cells : List Cell} {events : List MemoryAccess}
    {before after : State} (history : SailHistory cells events before after) :
    ∀ event ∈ events, event.2.1 = (Cell.register 0).addressCode → memoryWord event.2.2.1 = 0 := by
  induction history with
  | nil => simp
  | @cons event rest before middle after past cell member address read written ih =>
    intro target present zero
    rcases List.mem_cons.mp present with same | earlier
    · subst target
      have sameCell := cell_address_injective (address.trans zero)
      subst cell
      change EStateM.Result.ok (0 : BitVec 32) middle = .ok (memoryWord event.2.2.1) middle at read
      exact (EStateM.Result.ok.inj read).1.symm
    · exact ih target earlier zero

private theorem bounded_zero_token {token : MemoryToken babyBearModulus}
    (bounded : token.word.Bounded) (zero : memoryWord token.value = 0) : token.value = 0 := by
  have bits : token.word.toBitVec = 0 := zero
  have value := congrArg BitVec.toNat bits
  rw [Word.toBitVec_toNat bounded] at value
  have low : token.word.lo = 0 := by dsimp [Word.value, limbBase] at value; omega
  have high : token.word.hi = 0 := by dsimp [Word.value, limbBase] at value; omega
  calc
    token.value = Nat.pair token.word.lo token.word.hi := (Nat.pair_unpair _).symm
    _ = 0 := by rw [low, high]; rfl

variable [Fact babyBearModulus.Prime]
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- Every ordinary full native cycle executes its public stream-aware Sail clause.
All six CPU families use the same history and exact native PC endpoints. -/
theorem unrolled_full_ordinary_cycle
    {initial finalState : State} {text : List (BitVec 32)} {capacity : Nat}
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
    (reads : ∀ edge ∈ (unrolledFullMemoryData trace workers splitWorkers).steps, edge.1.word.Bounded)
    (stream : List (BitVec 32)) (ports : NonDeterminism.Pooled.StreamPorts trace stream)
    {row : Trace.Row babyBearModulus PooledFamily} (member : row ∈ trace.rows)
    (ordinary : ¬ (row.family = .addSub ∧ Delegation.Requests.Selected row.assignment)) :
    AddSub.Modular.External.Caller.OrdinaryCycle stream
      (NativeDecoder.ProgramRows.programOf .fullUnsigned initial text)
      trace cells events initial finalState row := by
  have zeroReads : ∀ edge ∈ (unrolledFullMemoryData trace workers splitWorkers).steps,
      edge.1.address = (Cell.register 0).addressCode → edge.1.value = 0 := by
    intro edge member same
    have native := permutation.mem_iff.mpr (List.mem_map.mpr ⟨edge, member, rfl⟩)
    exact bounded_zero_token (reads edge member) (history_zero_reads history _ native same)
  obtain ⟨entry, present, source, family, query⟩ :=
    unrolled_full_ordinary_source setup lookup accepted excluded initialPC row member ordinary
  obtain ⟨before, after, past, current, native, ranges, future⟩ :=
    unrolled_full_ordinary_context accepted equations active initialClock initialAligned row member ordinary
      permutation ordered history reads
  have clocks := state_clock_inputs (by decide)
    (by decide +kernel : SerializedInverse.Clock babyBearModulus)
    accepted.cpuEquations accepted.states initialClock initialAligned row member
  have finish := ClockLaws.advance (by decide)
    (by decide +kernel : SerializedInverse.Clock babyBearModulus) trace.rom row
    (accepted.cpuEquations row member) clocks.1
  change (timeOfPair row.finish.timestamp).value = row.clock + 4 at finish
  let physicalTrace := {trace with initialMemory := physicalImage}
  suffices localRun : ∃ clause next,
      AddSub.Modular.External.clause stream (NonDeterminism.Pooled.readIndex trace row) entry.instruction = some (clause, next) ∧
      next = NonDeterminism.Pooled.readIndex trace row + (if NonDeterminism.Pooled.isRead row then 1 else 0) ∧
      run (normalStep clause) (retiredState before row.start.word.toBitVec) =
        .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after row.finish.word.toBitVec) by
    obtain ⟨clause, next, selected, count, executed⟩ := localRun
    refine ⟨entry, present, family, query, clause, next, selected, count,
      before, after, past, ?_, ?_, executed⟩
    · change SailHistory cells (events.filter fun event => decide
        (row.clock < event.1 ∧ event.1 ≤ (timeOfPair row.finish.timestamp).value)) before after
      rw [finish]
      exact current
    · rw [finish]
      exact future
  have constraints := accepted.cpuEquations row member
  have active := accepted.cpuActive row member
  have readonlyPast : ∀ event ∈ events.filter (fun event => decide (event.1 ≤ row.clock)),
      ∀ pc : BitVec 32, pc.toNat < ROM.limit →
      event.2.1 = (Cell.ram pc).addressCode → event.2.2.1 = event.2.2.2 :=
    fun event included => readonly event (List.mem_filter.mp included).1
  cases row with
  | mk kind w =>
    cases kind with
    | addSub =>
      obtain ⟨clause, selected, executed⟩ := addsub_execution_from_shared_history (trace := physicalTrace) (by decide) (by decide +kernel : SerializedInverse.Clock babyBearModulus)
        image profile.registers constraints active ranges source family query
        (profile.loads entry present) (ports _ member) 1 past native
      exact ⟨clause, _, selected, rfl, executed⟩
    | shiftBinop =>
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left ShiftBinop.importedConstraints ShiftBinop.importedConstraintsTimestampLookups)
      have zeros : ∀ port ∈ ShiftBinop.importedConstraintsMemoryPorts,
          port.address.code w = (Cell.register 0).addressCode → (readToken w port).value = 0 := by
        intro port present atZero
        apply zeroReads (readToken w port,
          writeToken (⟨.shiftBinop, w⟩ : Trace.Row babyBearModulus PooledFamily).columns w port) ?_ atZero
        apply List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl ?_)))
        apply List.mem_flatMap.mpr
        refine ⟨⟨.shiftBinop, w⟩, member, List.mem_map.mpr ⟨port, ?_, rfl⟩⟩
        simpa [machinePorts, Trace.Row.ports, CircuitLayout.ports] using present
      obtain ⟨clause, selected, executed⟩ := shift_execution_from_shared_history (by decide) (by decide +kernel : SerializedInverse.Clock babyBearModulus)
        core active source family query zeros 1 native
      refine ⟨clause, _, clause_original selected, ?_, executed⟩
      simp [NonDeterminism.Pooled.isRead]
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
      have finalHi : (w 17).val < limbBase := (unrolled_full_pc_bounds setup lookup accepted excluded initialPC closure _ member).2.2
      obtain ⟨clause, selected, executed⟩ := control_execution_from_shared_history (by decide)
        core active source family query leftBound rightBound aligned finalHi 1 past native
        profile.configuration.isa ⟨profile.configuration.privilege, profile.landingPadDisabled⟩
      refine ⟨clause, _, clause_original selected, ?_, executed⟩
      simp [NonDeterminism.Pooled.isRead]
    | wordMemory =>
      have addresses : ∀ port ∈ WordMemory.importedConstraintsMemoryPorts,
          ∃ cell ∈ cells, port.address.code w = cell.addressCode := by
        intro port present
        exact native_history_cell 1 rfl rfl rfl native present
      obtain ⟨clause, selected, executed⟩ := word_execution_from_shared_history (trace := physicalTrace) (by decide) (by decide +kernel : SerializedInverse.Clock babyBearModulus)
        image wordSetup aligned profile.ordinary profile.configuration
        constraints active (ranges _ (Array.getElem_mem (by change 0 < 3; decide))) addresses
        source family query 1 readonlyPast past native
      refine ⟨clause, _, clause_original selected, ?_, executed⟩
      simp [NonDeterminism.Pooled.isRead]
    | mulDiv =>
      have core := Verification.holds_of_sublist constraints
        (List.sublist_append_left MulDiv.importedConstraints MulDiv.importedConstraintsTimestampLookups)
      have left := ranges MulDiv.importedConstraintsMemoryPorts[0]
        (Array.getElem_mem (by change 0 < 3; decide))
      have leftBound : (Word.mk (w 20).val (w 21).val).Bounded := by
        simpa [read_word, MulDiv.importedConstraintsMemoryPorts] using left
      rcases AddSub.Modular.External.Proofs.source_cases source with
        ⟨original, _, equal⟩ | ⟨_, _, equal⟩ | ⟨original, originalSource, equal⟩ |
        ⟨_, _, equal⟩ | ⟨_, _, equal⟩
      · cases kind : original.data.family <;>
          simp [equal, ProgramEntry.mapFamily, DecoderData.mapFamily, pooledArithmeticFamily, kind] at family
      · simp [equal, ProgramEntry.mapFamily, DecoderData.mapFamily] at family
      · rw [equal, mapped_query] at query
        obtain ⟨clause, selected, executed⟩ := MulDiv.Proofs.local_instruction_execution (by decide)
          (by decide +kernel : SerializedInverse.Limb16 babyBearModulus)
          core 1 originalSource query leftBound native
        have originalClause : instructionClause entry.instruction = some clause := by
          simpa only [equal, ProgramEntry.mapFamily] using selected
        refine ⟨clause, _, AddSub.Modular.External.Proofs.clause_original originalClause, ?_, executed⟩
        simp [NonDeterminism.Pooled.isRead]
      · simp [equal, ProgramEntry.mapFamily, DecoderData.mapFamily] at family
      · simp [equal, ProgramEntry.mapFamily, DecoderData.mapFamily] at family
    | subwordMemory =>
      obtain ⟨clause, selected, executed⟩ := unrolled_subword_execution_from_shared_history image subwordSetup
        aligned profile.ordinary profile.configuration constraints active ranges source family query past readonlyPast native
      refine ⟨clause, _, AddSub.Modular.External.Proofs.clause_original selected, ?_, executed⟩
      simp [NonDeterminism.Pooled.isRead]

end Airbender.Compiler.MachineTargets.Proofs
