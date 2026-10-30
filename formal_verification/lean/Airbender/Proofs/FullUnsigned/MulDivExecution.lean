import Airbender.Proofs.FullUnsigned.OrdinaryHistory
import Airbender.Proofs.FullUnsigned.CPUWriteRules
import Airbender.Proofs.MulDiv.Composition

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace Arithmetic Trace.Proofs Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

private theorem muldiv_source {initial : State} {entry : PooledProgramEntry}
    (source : entry.SourceWith initial AddSub.Modular.External.decoderFields)
    (family : entry.data.family = .mulDiv) :
    ∃ original : ProgramEntry Unit, original.SourceWith initial MulDiv.decoderFields ∧
      entry = original.mapFamily (fun _ => .mulDiv) := by
  rcases AddSub.Modular.External.Proofs.source_cases source with
    ⟨original, _, equal⟩ | ⟨_, _, equal⟩ | original | ⟨_, _, equal⟩ | ⟨_, _, equal⟩
  · cases kind : original.data.family <;>
      simp [equal, ProgramEntry.mapFamily, DecoderData.mapFamily, pooledArithmeticFamily, kind] at family
  · simp [equal, ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · exact original
  · simp [equal, ProgramEntry.mapFamily, DecoderData.mapFamily] at family
  · simp [equal, ProgramEntry.mapFamily, DecoderData.mapFamily] at family

variable [Fact babyBearModulus.Prime]
variable [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]

/-- The full pool's multiply/divide row executes the original Sail clause
at its exact shared-history boundaries. Native matching supplies its operand. -/
theorem unrolled_full_muldiv_execution
    {initial origin finalState : State} {text : List (BitVec 32)} {capacity : Nat}
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
    (equations : Keccak.Split.Native.EquationsHold splitWorkers.cached splitWorkers.setup splitWorkers.rows)
    (active : ∀ row ∈ splitWorkers.rows, row.assignment (row.columns splitWorkers.cached).execute = 1)
    (initialClock : (timeOfPair trace.initial.timestamp).Bounded)
    (initialAligned : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (w : Nat → ZMod babyBearModulus)
    (member : (⟨.mulDiv, w⟩ : Trace.Row babyBearModulus PooledFamily) ∈ trace.rows)
    {cells : List Cell} {events : List MemoryAccess}
    (permutation : events.Perm ((unrolledFullMemoryData trace workers splitWorkers).steps.map transferEvent))
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : SailHistory cells events origin finalState)
    (reads : ∀ edge ∈ (unrolledFullMemoryData trace workers splitWorkers).steps, edge.1.word.Bounded) :
    let row : Trace.Row babyBearModulus PooledFamily := ⟨.mulDiv, w⟩
    let low := (decodeTimestamp row.assignment row.columns.initialTime).value
    ∃ entry ∈ NativeDecoder.ProgramRows.programOf .fullUnsigned initial text,
      entry.SourceWith initial AddSub.Modular.External.decoderFields ∧
      entry.data.family = .mulDiv ∧ row.decoderQuery = entry.query ∧
      ∃ clause before after, instructionClause entry.instruction = some clause ∧
        SailHistory cells (events.filter fun event => decide (event.1 ≤ low)) origin before ∧
        run (normalStep clause) (retiredState before row.start.word.toBitVec) =
          .ok SailRV32.Functions.RETIRE_SUCCESS (retiredState after row.finish.word.toBitVec) ∧
        SailHistory cells (events.filter fun event => decide (low + 4 < event.1)) after finalState := by
  let row : Trace.Row babyBearModulus PooledFamily := ⟨.mulDiv, w⟩
  have ordinary : ¬ (row.family = .addSub ∧ Delegation.Requests.Selected row.assignment) := by simp [row]
  obtain ⟨entry, included, source, family, query⟩ :=
    unrolled_full_ordinary_source setup lookup accepted excluded initialPC row member ordinary
  obtain ⟨before, after, past, native, ranges, future⟩ :=
    unrolled_full_ordinary_history accepted equations active initialClock initialAligned row member ordinary
      permutation ordered history reads
  obtain ⟨original, originalSource, equal⟩ := muldiv_source source family
  have originalQuery : MulDiv.decoderQuery w = original.query := by
    rw [equal, mapped_query] at query
    exact query
  have holds := Verification.holds_of_sublist (accepted.cpuEquations row member)
    (List.sublist_append_left MulDiv.importedConstraints MulDiv.importedConstraintsTimestampLookups)
  have left := ranges MulDiv.importedConstraintsMemoryPorts[0] (Array.getElem_mem (by change 0 < 3; decide))
  have leftBound : (Word.mk (w 20).val (w 21).val).Bounded := by
    simpa [read_word, MulDiv.importedConstraintsMemoryPorts] using left
  obtain ⟨clause, selected, executed⟩ := MulDiv.Proofs.local_instruction_execution
    (by decide) (by decide +kernel : SerializedInverse.Limb16 babyBearModulus)
    holds 1 originalSource originalQuery leftBound native
  refine ⟨entry, included, source, family, ?_, clause, before, after, ?_, past, executed, future⟩
  · exact (by rw [equal, mapped_query]; exact originalQuery)
  · simpa only [equal, ProgramEntry.mapFamily] using selected

end Airbender.Compiler.MachineTargets.Proofs
