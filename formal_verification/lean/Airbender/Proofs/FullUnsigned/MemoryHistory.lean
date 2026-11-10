import Airbender.Proofs.FullUnsigned.MemoryFacts
import Airbender.Proofs.FullUnsigned.MemoryWriteRules
import Airbender.Proofs.FullUnsigned.MemoryZero
import Airbender.Proofs.Trace.TransferBoundary

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- The complete accepted native pool realizes one initialized Sail history.
Raw word bounds and terminal observations follow from that same exact pool. -/
theorem unrolled_full_memory_history
    {initial before : State} {text : List (BitVec 32)} {capacity : Nat}
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
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {physicalCells cells : List Cell} {physicalImage : List (MemoryToken babyBearModulus)}
    (image : initialImage initial physicalCells = some physicalImage)
    (wordSetup : trace.rom.wordMemory = ROM.table physicalCells physicalImage)
    (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.words initial))
    (workerSetup : workers.setup = Delegation.modeledSetup Keccak.Controller.rows)
    (rounds : ∀ row ∈ workers.rows, row.family = .blakeRound →
      ∃ round, Blake2Round.Memory.RoundMask row.assignment round)
    (splitEquations : Keccak.Split.Native.EquationsHold
      splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (control : Keccak.Split.Native.ControlSetupFacts splitWorkers.setup)
    (splitEquationsFixed : Keccak.Split.Native.EquationsHold
      splitWorkers.cached Keccak.Split.Native.Proofs.fixedSetup splitWorkers.rows)
    (splitActive : ∀ row ∈ splitWorkers.rows,
      row.assignment (row.columns splitWorkers.cached).execute = 1)
    (inputs : Transfer.NativeInputs (unrolledFullMemoryData trace workers splitWorkers) before cells)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    (∀ edge ∈ (unrolledFullMemoryData trace workers splitWorkers).steps,
      edge.1.word.Bounded ∧ edge.2.word.Bounded) ∧
      (∀ token ∈ trace.terminalMemory, token.word.Bounded) ∧
      ∃ (history : TimestampSortedMemoryAccessList) (events : List MemoryAccess) (after : State),
        history.val.Perm (Transfer.labeledEvents (unrolledFullMemoryData trace workers splitWorkers)) ∧
        events.Perm ((unrolledFullMemoryData trace workers splitWorkers).steps.map transferEvent) ∧
        events.Pairwise (fun a b => b.1 ≤ a.1) ∧
        SailHistory cells events before after ∧ SailStateMatches cells history after ∧
        ∀ token ∈ trace.terminalMemory, ∃ cell ∈ cells, cell.addressCode = token.address ∧
          cell.read after = .ok (memoryWord token.value) after := by
  let data := unrolledFullMemoryData trace workers splitWorkers
  have facts := unrolled_full_memory_facts accepted splitEquations splitActive control
    initialClock initialAligned inputs.clocks
  have rules := unrolled_full_memory_write_rules setup lookup accepted excluded initialPC
    initialClock initialAligned image wordSetup subwordSetup workerSetup rounds splitEquationsFixed splitActive
  have produced := Transfer.produced_bounds_of_seed facts inputs.words rules
  have zeroRules := unrolled_full_memory_zero_rules setup lookup accepted excluded initialPC
    initialClock initialAligned
  have seedZero : ∀ token ∈ data.initial, token.address = (Cell.register 0).addressCode →
      token.value = 0 := by
    intro token member same
    obtain ⟨cell, _, address, read⟩ := inputs.reads token member
    have cellZero := cell_address_injective (address.trans same)
    subst cell
    change EStateM.Result.ok (0 : BitVec 32) before = .ok (memoryWord token.value) before at read
    have bits : token.word.toBitVec = 0 := (EStateM.Result.ok.inj read).1.symm
    have value : token.word.value = 0 := by
      have equal := congrArg BitVec.toNat bits
      have zero : (0 : BitVec 32).toNat = 0 := by decide
      rw [Word.toBitVec_toNat (inputs.words token member), zero] at equal
      exact equal
    have low : token.word.lo = 0 := by dsimp [Word.value, limbBase] at value; omega
    have high : token.word.hi = 0 := by dsimp [Word.value, limbBase] at value; omega
    calc
      token.value = Nat.pair token.word.lo token.word.hi := (Nat.pair_unpair _).symm
      _ = 0 := by rw [low, high]; rfl
  have zeroReads := Transfer.read_cell_values_of_rules facts (Cell.register 0).addressCode 0
    seedZero zeroRules
  have zero : ∀ edge ∈ data.steps, edge.1.address = (Cell.register 0).addressCode →
      memoryWord edge.2.value = 0 := by
    intro edge member same
    have value := zeroRules edge member same (by
      intro previous present _ key
      exact zeroReads previous present key)
    rw [value]
    rfl
  obtain ⟨history, events, after, matched, permutation, ordered, realized, final⟩ :=
    Transfer.native_sail_history_at_boundary facts inputs.toBoundaryInputs aligned zero
  refine ⟨?_, ?_, history, events, after, matched, permutation, ordered, realized, final, ?_⟩
  · intro edge member
    exact ⟨produced edge.1 (facts.matching.mem_iff.mpr
        (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, member, rfl⟩)))),
      produced edge.2 (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨edge, member, rfl⟩)))⟩
  · intro token member
    exact produced token (facts.matching.mem_iff.mpr (List.mem_append.mpr (Or.inl member)))
  · exact Transfer.terminal_sail_reads_at_boundary facts inputs.toBoundaryInputs matched final

end Airbender.Compiler.MachineTargets.Proofs
