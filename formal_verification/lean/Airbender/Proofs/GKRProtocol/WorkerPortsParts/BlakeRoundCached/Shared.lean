import Airbender.Proofs.GKRProtocol.MemoryValueCongruence
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.BlakeRoundCached
import Airbender.Proofs.GKRProtocol.MemoryNative.BlakeRoundCached
import Airbender.Proofs.GKRProtocol.MemoryTokens
import Airbender.Proofs.GKRProtocol.FunctionalLinksNative.BlakeRoundCached
import Airbender.Proofs.GKRProtocol.NativeWitness
import Airbender.Review.Helpers.Delegation.Requests

namespace Airbender.Compiler.WorkerPortsNative.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def originalIndices : List Nat := [0] ++
  (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows ++ Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows).flatMap Source.MemoryRow.originalIndices

theorem original_columns : originalIndices.all (fun index =>
    decide (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement index) =
      Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement.original index))) = true := by decide +kernel

noncomputable def historyPredicate : Fin Airbender.Blake2Round.importedConstraintsMemoryPorts.size → Bool := fun index =>
    (List.finRange 2).all (fun limb => decide
      (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement
        ((Airbender.Blake2Round.importedConstraintsMemoryPorts[index.val]).clock.previous[limb.val])) =
       Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement.readTimestamp index.val limb)))

end Airbender.Compiler.WorkerPortsNative.BlakeRoundCached
