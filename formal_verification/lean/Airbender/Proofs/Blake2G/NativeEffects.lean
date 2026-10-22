import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Review.Circuits.Blake2G.Execution
import Airbender.Proofs.Blake2G.Soundness

namespace Airbender.Blake2G.Native.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 250000

theorem native_mapping {p : Nat} (w : Nat → ZMod p) : WordMapping (input w) (output w) w := by
  constructor
  all_goals simp [input, output, Delegation.Row.readWord, Delegation.Row.writtenWord, Delegation.Row.ports, readToken, MemoryToken.word,
    Delegation.Row.writeToken, importedConstraintsMemoryPorts, MemoryPort.readCode,
    MemoryPort.writeCode, WordColumns.code]

theorem native_effects [Fact p.Prime] (hp : FieldCapacity.NativeHashCapacity p)
    (inverse : SerializedInverse.Scale64 p) {w : Nat → ZMod p}
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
