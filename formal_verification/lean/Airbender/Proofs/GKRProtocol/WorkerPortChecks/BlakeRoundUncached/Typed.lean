import Airbender.Proofs.GKRProtocol.WorkerPortChecks.BlakeRoundUncached.Inputs
import Airbender.Proofs.GKRProtocol.NumericWorkerPortChecks

namespace Airbender.Compiler.WorkerPortChecks.BlakeRoundUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def originalPairs := Airbender.Compiler.WorkerPortsNative.BlakeRoundUncached.originalIndices.map (fun index =>
  (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.placement index), Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.sourcePlacement.original index)))
noncomputable def historyPairs := (List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).flatMap (fun index =>
  (List.finRange 2).map (fun limb => (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.placement ((Airbender.Blake2Round.importedConstraintsMemoryPorts[index.val]).clock.previous[limb.val])), Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.sourcePlacement.readTimestamp index.val limb))))
noncomputable def indexBounds := (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.memoryReadRows ++ Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.memoryWriteRows).flatMap (fun row => row.fields.flatMap (fun field => field.historyIndices.map (fun index => (index.1, Airbender.Blake2Round.importedConstraintsMemoryPorts.size))))
noncomputable def original : NumericWorkerPortChecks.Typed := ⟨originalPairs ++ historyPairs, indexBounds⟩

theorem history_predicate : Airbender.Compiler.WorkerPortsNative.BlakeRoundUncached.historyPredicate = (fun index => (List.finRange 2).all (fun limb => decide (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.placement ((Airbender.Blake2Round.importedConstraintsMemoryPorts[index.val]).clock.previous[limb.val])) = Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.sourcePlacement.readTimestamp index.val limb)))) := by rfl

theorem original_check (checked : original.check = true) :
    ((Airbender.Compiler.WorkerPortsNative.BlakeRoundUncached.originalIndices.all (fun index =>
    decide (Airbender.Compiler.FullArithmeticNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundUncached.native.placement index) =
      Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.bank.address (Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.sourcePlacement.original index))) = true) ∧ ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).all Airbender.Compiler.WorkerPortsNative.BlakeRoundUncached.historyPredicate = true)) ∧ ((Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.memoryReadRows ++ Airbender.Compiler.MemoryNative.BlakeRoundUncached.native.memoryWriteRows).all
      (fun row => row.fields.all (fun field => field.historyIndices.all
        (fun index => decide (index.1 < Airbender.Blake2Round.importedConstraintsMemoryPorts.size)))) = true) := by
  rw [history_predicate]
  simpa only [original, NumericWorkerPortChecks.Typed.check, originalPairs, historyPairs,
    indexBounds, List.all_append, List.all_map, List.all_flatMap, Function.comp_def, Bool.and_eq_true] using checked

end Airbender.Compiler.WorkerPortChecks.BlakeRoundUncached
