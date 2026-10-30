import Airbender.Proofs.FullUnsigned.CPUWriteRules
import Airbender.Proofs.Delegation.Operations
import Airbender.Proofs.Keccak.SplitNativeWriteRules

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- One time induction bounds the full machine's raw writes. Public round
controls and split setup interpretation remain named supporting obligations. -/
theorem unrolled_full_memory_write_rules
    {initial : Reference.RiscV.Sail.State} {text : List (BitVec 32)} {capacity : Nat}
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
    {cells : List Cell} {physicalImage : List (MemoryToken babyBearModulus)}
    (image : initialImage initial cells = some physicalImage)
    (wordSetup : trace.rom.wordMemory = ROM.table cells physicalImage)
    (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.words initial))
    (workerSetup : workers.setup = Delegation.modeledSetup Keccak.Controller.rows)
    (rounds : ∀ row ∈ workers.rows, row.family = .blakeRound →
      ∃ round, Blake2Round.Memory.RoundMask row.assignment round)
    (splitEquationsFixed : Keccak.Split.Native.EquationsHold
      splitWorkers.cached Keccak.Split.Native.Proofs.fixedSetup splitWorkers.rows)
    (splitActive : ∀ row ∈ splitWorkers.rows,
      row.assignment (row.columns splitWorkers.cached).execute = 1) :
    Transfer.WriteRules (unrolledFullMemoryData trace workers splitWorkers) := by
  have workerRules := Delegation.Proofs.operation_rules_of_queries (by decide)
    (by decide +kernel : SerializedInverse.Scale64 babyBearModulus)
    accepted.workerEquations workerSetup rounds (by
      intro row present family
      have active := accepted.workerActive row present
      rwa [Delegation.Row.columns, family] at active)
  intro edge present earlierReads
  change edge ∈ pooledSteps trace ++ workers.steps ++ splitWorkers.steps at present
  rw [List.append_assoc] at present
  rcases List.mem_append.mp present with machine | rest
  · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨port, included, rfl⟩ := List.mem_map.mp step
    apply unrolled_full_cpu_write_rule setup lookup accepted excluded initialPC
      initialClock initialAligned image wordSetup subwordSetup row member
      (unrolledFullMemoryData trace workers splitWorkers) ?_ port (by simpa using included) earlierReads
    intro source physical
    have inMachine : (readToken row.assignment source,
        writeToken row.columns row.assignment source) ∈ pooledSteps trace :=
      List.mem_flatMap.mpr ⟨row, member, List.mem_map.mpr ⟨source, by simpa using physical, rfl⟩⟩
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl inMachine)))
  · rcases List.mem_append.mp rest with standard | split
    · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp standard
      obtain ⟨port, included, rfl⟩ := List.mem_map.mp step
      apply workerRules row member ?_ port (by simpa using included)
      intro source physical
      have inWorkers : (readToken row.assignment source, row.writeToken source) ∈ workers.steps :=
        List.mem_flatMap.mpr ⟨row, member, List.mem_map.mpr ⟨source, by simpa using physical, rfl⟩⟩
      apply earlierReads _ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr inWorkers))))
      have same : (row.writeToken source).time = (row.writeToken port).time := by
        simp only [Delegation.Row.writeToken, Delegation.Proofs.port_offset row physical,
          Delegation.Proofs.port_offset row (by simpa using included)]
      rw [same]
    · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp split
      obtain ⟨port, included, rfl⟩ := List.mem_map.mp step
      apply Keccak.Split.Native.Proofs.native_write_rule splitWorkers.cached row
        (splitEquationsFixed.rowsHold row member) (splitActive row member)
        (unrolledFullMemoryData trace workers splitWorkers) ?_ port (by simpa using included) earlierReads
      intro source physical
      have inWorkers : (readToken row.assignment source,
          row.writeToken splitWorkers.cached source) ∈ splitWorkers.steps :=
        List.mem_flatMap.mpr ⟨row, member, List.mem_map.mpr ⟨source, by simpa using physical, rfl⟩⟩
      exact List.mem_append.mpr (Or.inr inWorkers)

end Airbender.Compiler.MachineTargets.Proofs
