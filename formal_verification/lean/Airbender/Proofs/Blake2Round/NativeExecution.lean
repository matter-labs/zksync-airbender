import Airbender.Review.Blake2Round.Execution
import Airbender.Proofs.Blake2Round.Row
import Airbender.Review.Delegation.Theorems

namespace Airbender.Blake2Round.Native.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 600000

theorem native_mapping [Fact p.Prime] (round : Fin 10) {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable)) :
    Row.Mapping (input round w) (output w) w := by
  constructor
  · constructor
    all_goals simp [input, output, Delegation.Row.readWord, Delegation.Row.writtenWord,
      Delegation.Row.ports, readToken, MemoryToken.word, Delegation.Row.writeToken,
      importedConstraintsMemoryPorts, MemoryPort.readCode, MemoryPort.writeCode,
      WordColumns.code, Variables.controlReadLo, Variables.controlReadHi,
      Variables.controlWriteLo, Variables.controlWriteHi]
  · simp [input, Delegation.Row.readWord, Delegation.Row.ports, readToken, MemoryToken.word,
      importedConstraintsMemoryPorts, MemoryPort.readCode, WordColumns.code]
  · simp [input, Delegation.Row.readWord, Delegation.Row.ports, readToken, MemoryToken.word,
      importedConstraintsMemoryPorts, MemoryPort.readCode, WordColumns.code]
  · have flag := Control.Proofs.control_bits holds 0
    change w 139 = 0 ∨ w 139 = 1 at flag
    rcases flag with flag | flag <;> simp [input, Variables.controlBits, flag]
  · have flag := Control.Proofs.control_bits holds 2
    change w 141 = 0 ∨ w 141 = 1 at flag
    rcases flag with flag | flag <;> simp [input, Variables.controlBits, flag]
  · have flag := Control.Proofs.control_bits holds 1
    change w 140 = 0 ∨ w 140 = 1 at flag
    rcases flag with flag | flag <;> simp [input, Variables.controlBits, flag]
  · apply Vector.ext
    intro i bound
    change i < 8 at bound
    interval_cases i
    all_goals simp [input, Delegation.Row.readWord, Delegation.Row.ports, readToken,
      MemoryToken.word, importedConstraintsMemoryPorts, MemoryPort.readCode, WordColumns.code,
      Preparation.words, Variables.stateReads]
  · apply Vector.ext
    intro i bound
    change i < 16 at bound
    interval_cases i
    all_goals simp [input, Delegation.Row.readWord, Delegation.Row.ports, readToken,
      MemoryToken.word, importedConstraintsMemoryPorts, MemoryPort.readCode, WordColumns.code,
      Preparation.words, Variables.extendedReads]
  · apply Vector.ext
    intro i bound
    change i < 16 at bound
    interval_cases i
    all_goals simp [input, Delegation.Row.readWord, Delegation.Row.ports, readToken,
      MemoryToken.word, importedConstraintsMemoryPorts, MemoryPort.readCode, WordColumns.code,
      Preparation.words, Variables.messageReads]
  · apply Vector.ext
    intro i bound
    change i < 8 at bound
    interval_cases i
    all_goals simp [output, Delegation.Row.writtenWord, Delegation.Row.writeToken, Delegation.Row.ports,
      MemoryToken.word, importedConstraintsMemoryPorts, MemoryPort.writeCode, WordColumns.code,
      Preparation.words, Finalization.stateWrites]
  · apply Vector.ext
    intro i bound
    change i < 16 at bound
    interval_cases i
    all_goals simp [output, Delegation.Row.writtenWord, Delegation.Row.writeToken, Delegation.Row.ports,
      MemoryToken.word, importedConstraintsMemoryPorts, MemoryPort.writeCode, WordColumns.code,
      Preparation.words, Mixing.extendedWrites]
  · rfl

theorem operation_execution [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1)
    {data : Delegation.MemoryData p} {before : Reference.RiscV.Sail.State} {cells : List Cell}
    {control : Fin 4096 → Vector Nat 6}
    (accepted : Delegation.MemoryAccepted data) (inputs : Delegation.OperationInputs data before cells control)
    (aligned : ∀ cell ∈ cells, cell.Aligned) :
    Delegation.MemoryExecution data before cells ∧
      ∀ row ∈ data.rows, row.family = .blakeRound →
        ∃ round, Memory.RoundMask row.assignment round ∧ Row.spec (input round row.assignment) (output row.assignment) := by
  have size : 2 * timestampBase + 4 < p := by norm_num [timestampBase]; omega
  have bounds := Delegation.Proofs.operation_word_bounds hp inverse accepted inputs
  refine ⟨Delegation.native_memory_execution size accepted inputs.publicState aligned, ?_⟩
  intro row member family
  obtain ⟨round, mask⟩ := inputs.rounds row member family
  have holds := accepted.constraints row member
  have reads := bounds.reads row member
  rcases row with ⟨kind, w⟩
  change kind = .blakeRound at family
  subst kind
  simp only [Delegation.Row.constraints, inputs.tables, Delegation.modeledSetup] at holds
  have core := Verification.holds_of_sublist holds (List.sublist_append_left
    (importedConstraints setupTable) importedConstraintsTimestampLookups)
  refine ⟨round, mask, ?_⟩
  apply Row.Proofs.soundness hp inverse (input round w) (output w) w
  refine ⟨?_, core, native_mapping round core⟩
  constructor
  · exact mask
  · exact ⟨reads importedConstraintsMemoryPorts[0] (by simp [Delegation.Row.ports, importedConstraintsMemoryPorts]),
      reads importedConstraintsMemoryPorts[25] (by simp [Delegation.Row.ports, importedConstraintsMemoryPorts])⟩
  · intro i
    simp only [input, Fin.getElem_fin, Vector.getElem_ofFn]
    exact reads (importedConstraintsMemoryPorts[1 + i.val]'(by change 1 + i.val < 43; omega))
      (Array.getElem_mem (by change 1 + i.val < 43; omega))
  · intro i
    simp only [input, Fin.getElem_fin, Vector.getElem_ofFn]
    exact reads (importedConstraintsMemoryPorts[9 + i.val]'(by change 9 + i.val < 43; omega))
      (Array.getElem_mem (by change 9 + i.val < 43; omega))
  · intro i
    simp only [input, Fin.getElem_fin, Vector.getElem_ofFn]
    exact reads (importedConstraintsMemoryPorts[26 + i.val]'(by change 26 + i.val < 43; omega))
      (Array.getElem_mem (by change 26 + i.val < 43; omega))

end Airbender.Blake2Round.Native.Proofs
