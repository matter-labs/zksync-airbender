import Airbender.Proofs.FullUnsigned.MemoryClocks
import Airbender.Proofs.AddSub.ModularExternalDecoder
import Airbender.Proofs.Trace.PooledValues
import Airbender.Proofs.Trace.TransferBounds

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Delegation.Caller
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
variable [Fact babyBearModulus.Prime]

/-- A non-caller row has its exact original public instruction source. -/
theorem unrolled_full_ordinary_source
    {initial : Reference.RiscV.Sail.State} {text : List (BitVec 32)} {capacity : Nat}
    {masks : PooledFamily → NativeDecoder.ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {extraSteps : List (MemoryToken babyBearModulus × MemoryToken babyBearModulus)}
    {extraRequests : List (Delegation.Requests.Request babyBearModulus)}
    (setup : UnrolledProgramSetup .fullUnsigned initial text capacity masks columns)
    (lookup : UnrolledDecoderExactLookup trace masks columns)
    (accepted : UnrolledAcceptance trace workers extraSteps extraRequests)
    (excluded : FullUnsigned.NoSpecial5Call initial text)
    (initialPC : trace.initial.word.lo < limbBase)
    (row : Trace.Row babyBearModulus PooledFamily) (present : row ∈ trace.rows)
    (ordinary : ¬ (row.family = .addSub ∧ Delegation.Requests.Selected row.assignment)) :
    ∃ entry ∈ NativeDecoder.ProgramRows.programOf .fullUnsigned initial text,
      entry.SourceWith initial AddSub.Modular.External.decoderFields ∧
        entry.data.family = row.family ∧ row.decoderQuery = entry.query := by
  rcases unrolled_full_native_row_classification setup lookup accepted excluded initialPC row present with
    ⟨entry, member, source, family, query, _⟩ | ⟨_, _, _, family, _, selected⟩ |
      ⟨_, _, _, family, _, selected⟩
  · exact ⟨entry, member, source, family, query⟩
  · exact False.elim (ordinary ⟨family, selected⟩)
  · exact False.elim (ordinary ⟨family, selected⟩)

/-- Every full native CPU row satisfies the shared raw write-bound rule.
The public ROM image and chronological read bounds remain explicit. -/
theorem unrolled_full_cpu_write_rule
    {initial : Reference.RiscV.Sail.State} {text : List (BitVec 32)} {capacity : Nat}
    {masks : PooledFamily → NativeDecoder.ProgramRows.Mask}
    {columns : PooledFamily → List (List (ZMod babyBearModulus))}
    {trace : PooledTrace babyBearModulus} {workers : Delegation.MemoryData babyBearModulus}
    {extraSteps : List (MemoryToken babyBearModulus × MemoryToken babyBearModulus)}
    {extraRequests : List (Delegation.Requests.Request babyBearModulus)}
    (setup : UnrolledProgramSetup .fullUnsigned initial text capacity masks columns)
    (lookup : UnrolledDecoderExactLookup trace masks columns)
    (accepted : UnrolledAcceptance trace workers extraSteps extraRequests)
    (excluded : FullUnsigned.NoSpecial5Call initial text)
    (initialPC : trace.initial.word.lo < limbBase)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    {cells : List Cell} {physicalImage : List (MemoryToken babyBearModulus)}
    (image : initialImage initial cells = some physicalImage)
    (wordSetup : trace.rom.wordMemory = ROM.table cells physicalImage)
    (subwordSetup : trace.rom.subwordMemory = Verification.subwordTable (ROM.words initial))
    (row : Trace.Row babyBearModulus PooledFamily) (present : row ∈ trace.rows)
    (ambient : Transfer.Data babyBearModulus)
    (member : ∀ source ∈ machinePorts row,
      (readToken row.assignment source, writeToken row.columns row.assignment source) ∈ ambient.steps)
    (port : MemoryPort) (included : port ∈ machinePorts row)
    (earlierReads : ∀ previous ∈ ambient.steps,
      (timeOfPair previous.2.time).value ≤
        (timeOfPair (writeToken row.columns row.assignment port).time).value → previous.1.word.Bounded) :
    (writeToken row.columns row.assignment port).word.Bounded := by
  have native := Delegation.Caller.Proofs.machine_port_native row included
  by_cases caller : (row.family == .addSub && decide (Delegation.Requests.Selected row.assignment)) = true
  · have both : row.family = .addSub ∧ Delegation.Requests.Selected row.assignment := by
      simpa only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using caller
    have core := accepted.cpuEquations row present
    simp only [Trace.Row.constraints, both.1, CircuitLayout.constraints] at core
    have holds := Verification.holds_of_sublist core
      (List.sublist_append_left _ AddSub.importedConstraintsTimestampLookups)
    obtain ⟨_, _, low, high⟩ := Delegation.Requests.Proofs.caller_tokens holds both.2
    have architectural : machinePorts row = architecturalPorts := by
      simp only [machinePorts, caller, ↓reduceIte]
    rw [architectural] at included
    have cases : port = AddSub.importedConstraintsMemoryPorts[0] ∨
        port = AddSub.importedConstraintsMemoryPorts[2] := by
      simpa [architecturalPorts] using included
    rcases cases with rfl | rfl
    · have step := member AddSub.importedConstraintsMemoryPorts[0]
        (by rw [architectural]; simp [architecturalPorts])
      exact earlierReads _ step (Nat.le_refl _)
    · simp only [Trace.Row.columns, both.1, CircuitLayout.columns]
      simp [writeToken, MemoryToken.word, MemoryPort.writeCode, WordColumns.code,
        WordColumns.evaluate, AddSub.importedConstraintsMemoryPorts, low, high,
        Word.Bounded, limbBase]
  · have ordinary : ¬ (row.family = .addSub ∧ Delegation.Requests.Selected row.assignment) := by
      intro both
      exact caller (by simp only [both.1, beq_self_eq_true, both.2, decide_true, Bool.and_self])
    obtain ⟨entry, _, source, family, query⟩ :=
      unrolled_full_ordinary_source setup lookup accepted excluded initialPC row present ordinary
    let physicalTrace := { trace with initialMemory := physicalImage }
    have rules := pooled_row_write_rule (trace := physicalTrace) (by decide)
      (accepted.cpuEquations row present) (accepted.cpuActive row present)
      image wordSetup subwordSetup (AddSub.Modular.External.Proofs.source_cases source) family query
    have clock := state_clock_inputs (by decide)
      (by decide +kernel : SerializedInverse.Clock babyBearModulus)
      accepted.cpuEquations accepted.states initialClock initialAligned row present
    have time (source : MemoryPort) (sourceMember : source ∈ row.ports) :
        (timeOfPair (writeToken row.columns row.assignment source).time).value =
          (source.event row.columns row.assignment).1 :=
      (write_time (by decide) (base := rawPair row.assignment row.columns.initialTime)
        clock.1 clock.2 (Trace.Proofs.port_offset row source sourceMember)).2
    apply rules port native
    intro source sourceMember order
    have physical : source ∈ machinePorts row := by
      simpa only [machinePorts, if_neg caller] using sourceMember
    apply earlierReads _ (member source physical)
    rw [time source sourceMember, time port native]
    exact order

end Airbender.Compiler.MachineTargets.Proofs
