import Airbender.Proofs.GKRProtocol.MemoryValueCongruence
import Airbender.Proofs.GKRProtocol.CleanArithmeticNative.BlakeRoundUncached
import Airbender.Proofs.GKRProtocol.MemoryNative.BlakeRoundUncached
import Airbender.Proofs.GKRProtocol.MemoryTokens
import Airbender.Proofs.GKRProtocol.FunctionalLinksNative.BlakeRoundUncached
import Airbender.Proofs.GKRProtocol.NativeWitness
import Airbender.Review.Helpers.Delegation.Requests

namespace Airbender.Compiler.WorkerPortsNative.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

noncomputable def originalIndices : List Nat := [0] ++
  (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.memoryReadRows ++ Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.memoryWriteRows).flatMap Source.MemoryRow.originalIndices

theorem original_columns : originalIndices.all (fun index =>
    decide (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.placement index) =
      Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.sourcePlacement.original index))) = true := by decide +kernel

noncomputable def historyPredicate : Fin Airbender.Blake2Round.importedConstraintsMemoryPorts.size → Bool := fun index =>
    (List.finRange 2).all (fun limb => decide
      (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.placement
        ((Airbender.Blake2Round.importedConstraintsMemoryPorts[index.val]).clock.previous[limb.val])) =
       Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.sourcePlacement.readTimestamp index.val limb)))

end Airbender.Compiler.WorkerPortsNative.BlakeRoundUncached
