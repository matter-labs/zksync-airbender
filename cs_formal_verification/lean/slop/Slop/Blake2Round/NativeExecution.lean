module
public import Human.Circuits.Blake2Round.Execution
public import Slop.Blake2Round.Row
public import Slop.Delegation.Operations
public import Slop.Delegation.Requests
public import Slop.Delegation.PortEvents
public import Slop.Defs.Circuits.Blake2Round.Row
public import Slop.Defs.Helpers.Memory.Ports
public import Slop.Defs.Circuits.Blake2Round.Artifact
public import Slop.Defs.Circuits.Blake2Round.Preparation
public import Slop.Defs.Circuits.Blake2Round.Control
public import Slop.Defs.Circuits.Blake2Round.Mixing
public import Slop.Defs.Circuits.Blake2Round.Finalization

@[expose] public section

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

theorem native_effects [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1) (round : Fin 10) {w : Nat → ZMod p}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (importedConstraints setupTable))
    (mask : Memory.RoundMask w round)
    (reads : ∀ port ∈ importedConstraintsMemoryPorts, (readToken w port).word.Bounded) :
    Row.spec (input round w) (output w) := by
  apply Row.Proofs.soundness hp inverse (input round w) (output w) w
  refine ⟨?_, core, native_mapping round core⟩
  constructor
  · exact mask
  · exact ⟨reads importedConstraintsMemoryPorts[0] (by simp [importedConstraintsMemoryPorts]),
      reads importedConstraintsMemoryPorts[25] (by simp [importedConstraintsMemoryPorts])⟩
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
