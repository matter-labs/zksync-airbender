import Airbender.Review.MulDiv.Model
import Airbender.Proofs.Trace.RowContext
import Airbender.Proofs.Trace.PooledExecution

namespace Airbender.MulDiv.Proofs
open Arithmetic Reference.RiscV.Sail Reference.Sail Trace Trace.Proofs

set_option backward.isDefEq.respectTransparency false in
/-- Reuse the mixed-family execution proof and shared register projection.
    Initialized history derives the local decoder, operand and read interfaces. -/
theorem pooled_row_soundness {p : Nat} [Fact p.Prime]
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (hp : 536870912 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    (trace : PooledTrace p) (initial : State) (cells : List Cell) (program : List PooledProgramEntry) :
    (circuitModel trace initial cells program).SoundnessUnder
      (InterfaceAssumptions trace initial cells program) spec := by
  rintro input output w ⟨assumptions, ⟨_, accepted, decoded, member⟩, mapping⟩
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  obtain ⟨addresses, programImage⟩ := assumptions.initialization.programImage
  obtain ⟨events, rawBefore, rawAfter, _, _, history, atState⟩ := pooled_row_context
    clockSize inverse accepted assumptions.initialization.clocks assumptions.initialization.image
    assumptions.initialization.distinct assumptions.initialization.aligned programImage decoded mapping.state
  change input.before = retiredState rawBefore (Word.mk (w 0).val (w 1).val).toBitVec at atState
  obtain ⟨entry, present, family, query, encoding⟩ := mapping.instruction
  change decoderQuery w = entry.query at query
  obtain ⟨clause, clauseBound, normal⟩ := pooled_muldiv_execution hp inverse accepted
    assumptions.initialization.clocks assumptions.initialization.image assumptions.wordTable
    assumptions.subwordTable programImage decoded member present family query history
  have clauseMatches : instructionClause entry.instruction = some (execution input) := by
    rw [encoding]
    cases operation : input.operation <;> simp only [operation, execution, instructionClause]
  have same := Option.some.inj (clauseBound.symm.trans clauseMatches)
  rw [same, ← atState] at normal
  have pcWord : output.pc = Word.mk (w 14).val (w 15).val :=
    congrArg₂ Word.mk mapping.words.finalPCLo mapping.words.finalPCHi
  rw [← pcWord] at normal
  have normalized := retired_state_history history (Word.mk (w 0).val (w 1).val).toBitVec
  rw [← atState] at normalized
  cases rdIndex : input.rd with | Regidx rd =>
    have projected := register_history_projection (by omega) trace.memoryEpoch
      (first := importedConstraintsMemoryPorts[0]) (second := importedConstraintsMemoryPorts[1])
      (destination := importedConstraintsMemoryPorts[2]) rfl rfl rfl
      (by simpa only [rdIndex] using mapping.words.rdIndex) output (by
        simp [importedConstraintsMemoryPorts, MemoryPort.writeCode, pairCode, memoryWord,
          Nat.unpair_pair, Word.toBitVec, Word.value, mapping.words.outputLo, mapping.words.outputHi]) normalized
    rw [retired_state_overwrite] at projected
    exact ⟨_, normal, by simpa only [rdIndex] using projected⟩

end Airbender.MulDiv.Proofs
