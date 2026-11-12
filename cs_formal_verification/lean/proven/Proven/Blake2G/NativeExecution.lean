module
public import Human.Circuits.Blake2G.Execution
public import Proven.Blake2G.Soundness
public import Proven.Delegation.Operations
public import Proven.Delegation.Requests
public import Proven.Delegation.PortEvents
public import Proven.Defs.Helpers.Memory.Ports
public import Proven.Defs.Circuits.Blake2G.Execution

@[expose] public section

namespace Airbender.Blake2G.Native.Proofs
open Trace
set_option warningAsError true

theorem native_mapping {p : Nat} (w : Nat → ZMod p) : WordMapping (input w) (output w) w := by
  constructor
  all_goals simp [input, output, Delegation.Row.readWord, Delegation.Row.writtenWord, Delegation.Row.ports, readToken, MemoryToken.word,
    Delegation.Row.writeToken, importedConstraintsMemoryPorts, MemoryPort.readCode,
    MemoryPort.writeCode, WordColumns.code]

theorem native_effects [Fact p.Prime] (hp : 8388608 ≤ p)
    (inverse : 64 * (-31457280 : ZMod p) = 1) {w : Nat → ZMod p}
    (core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable Control.controllerRows)))
    (reads : ∀ port ∈ importedConstraintsMemoryPorts, (readToken w port).word.Bounded) :
    Blake2G.spec (input w) (output w) := by
  apply Blake2G.Proofs.soundness (by omega) inverse Control.controllerRows (input w) (output w) w
  refine ⟨?_, core, native_mapping w⟩
  constructor
  · exact reads importedConstraintsMemoryPorts[1] (by simp [importedConstraintsMemoryPorts])
  · exact reads importedConstraintsMemoryPorts[3] (by simp [importedConstraintsMemoryPorts])
  · exact reads importedConstraintsMemoryPorts[6] (by simp [importedConstraintsMemoryPorts])
  · exact reads importedConstraintsMemoryPorts[7] (by simp [importedConstraintsMemoryPorts])

end Airbender.Blake2G.Native.Proofs
