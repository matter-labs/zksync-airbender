import Airbender.Proofs.FullUnsigned.CPUWriteRules
import Airbender.Proofs.Keccak.SplitNonzeroPorts
import Airbender.Proofs.Delegation.SailHistory
import Airbender.Proofs.Trace.PooledHistory
import Airbender.Proofs.Trace.TransferValues

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Delegation.Caller
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- The complete native CPU and worker pool preserves Sail's zero register.
The same chronological induction handles refreshes and ordinary writes. -/
theorem unrolled_full_memory_zero_rules
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
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0) :
    Transfer.CellWriteRules (unrolledFullMemoryData trace workers splitWorkers)
      (Cell.register 0).addressCode 0 := by
  intro edge present same reads
  have inPool := present
  change edge ∈ pooledSteps trace ++ workers.steps ++ splitWorkers.steps at present
  rw [List.append_assoc] at present
  rcases List.mem_append.mp present with machine | rest
  · obtain ⟨row, member, step⟩ := List.mem_flatMap.mp machine
    obtain ⟨port, included, rfl⟩ := List.mem_map.mp step
    have native := Delegation.Caller.Proofs.machine_port_native row (by simpa using included)
    by_cases caller : (row.family == .addSub && decide (Delegation.Requests.Selected row.assignment)) = true
    · have both : row.family = .addSub ∧ Delegation.Requests.Selected row.assignment := by
        simpa only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using caller
      have architectural : machinePorts row = architecturalPorts := by
        simp only [machinePorts, caller, ↓reduceIte]
      rw [architectural] at included
      have cases : port = AddSub.importedConstraintsMemoryPorts[0] ∨
          port = AddSub.importedConstraintsMemoryPorts[2] := by simpa [architecturalPorts] using included
      rcases cases with rfl | rfl
      · exact reads _ inPool (Nat.le_refl _) same
      · have core := accepted.cpuEquations row member
        simp only [Trace.Row.constraints, both.1, CircuitLayout.constraints] at core
        have holds := Verification.holds_of_sublist core
          (List.sublist_append_left _ AddSub.importedConstraintsTimestampLookups)
        obtain ⟨_, _, low, high⟩ := Delegation.Requests.Proofs.caller_tokens holds both.2
        simp [writeToken, MemoryPort.writeCode, WordColumns.code, WordColumns.evaluate,
          AddSub.importedConstraintsMemoryPorts, low, high, Nat.pair]
    · have ordinary : ¬ (row.family = .addSub ∧ Delegation.Requests.Selected row.assignment) := by
        intro both
        exact caller (by simp only [both.1, beq_self_eq_true, both.2, decide_true, Bool.and_self])
      obtain ⟨entry, _, source, family, query⟩ :=
        unrolled_full_ordinary_source setup lookup accepted excluded initialPC row member ordinary
      have preserving := pooled_row_zero_preserving AddSub.Modular.External.Proofs.decoderRules
        (by decide) trace.rom row (accepted.cpuEquations row member)
        (AddSub.Modular.External.Proofs.source_cases source) family query
      have clock := state_clock_inputs (by decide)
        (by decide +kernel : SerializedInverse.Clock babyBearModulus)
        accepted.cpuEquations accepted.states initialClock initialAligned row member
      have time (source : MemoryPort) (sourceMember : source ∈ row.ports) :
          (timeOfPair (writeToken row.columns row.assignment source).time).value =
            (source.event row.columns row.assignment).1 :=
        (write_time (by decide) (base := rawPair row.assignment row.columns.initialTime)
          clock.1 clock.2 (Trace.Proofs.port_offset row source sourceMember)).2
      apply preserving port native same
      intro previous prior earlier key
      have physical : previous ∈ machinePorts row := by
        simpa only [machinePorts, if_neg caller] using prior
      have inMachine : (readToken row.assignment previous,
          writeToken row.columns row.assignment previous) ∈ pooledSteps trace :=
        List.mem_flatMap.mpr ⟨row, member, List.mem_map.mpr ⟨previous, by simpa using physical, rfl⟩⟩
      apply reads _ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl inMachine))))
      · rw [time previous prior, time port native]
        exact earlier
      · exact key
  · rcases List.mem_append.mp rest with standard | split
    · obtain ⟨row, _, step⟩ := List.mem_flatMap.mp standard
      obtain ⟨port, included, rfl⟩ := List.mem_map.mp step
      exact False.elim (Delegation.Proofs.port_not_zero row (by simpa using included) same)
    · obtain ⟨row, _, step⟩ := List.mem_flatMap.mp split
      obtain ⟨port, included, rfl⟩ := List.mem_map.mp step
      exact False.elim (Keccak.Split.Native.Proofs.port_not_zero splitWorkers.cached row
        (by simpa using included) same)

end Airbender.Compiler.MachineTargets.Proofs
