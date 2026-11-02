import Airbender.Proofs.GKRProtocol.MemoryValueCongruence
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.KeccakUncached
import Airbender.Proofs.GKRProtocol.MemoryNative.KeccakUncached
import Airbender.Proofs.GKRProtocol.MemoryTokens
import Airbender.Proofs.GKRProtocol.FunctionalLinksNative.KeccakUncached
import Airbender.Proofs.GKRProtocol.NativeWitness
import Airbender.Review.Helpers.Delegation.Requests

namespace Airbender.Compiler.WorkerPortsNative.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536

noncomputable def originalIndices : List Nat := [0] ++
  (Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows ++ Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows).flatMap Source.MemoryRow.originalIndices

noncomputable def logicalValues (assignment : Nat → Source.BaseField) (other : Source.MemoryValues) : Source.MemoryValues :=
  { other with
    original := assignment
    readTimestamp := fun query limb =>
      if bounded : query < Airbender.Keccak.importedConstraintsMemoryPorts.size then
        assignment ((Airbender.Keccak.importedConstraintsMemoryPorts[query]).clock.previous[limb.val])
      else 0 }

end Airbender.Compiler.WorkerPortsNative.KeccakUncached
