import Airbender.Proofs.GKRProtocol.WorkerPortChecks.BlakeRoundCached.Inputs
import Airbender.Proofs.GKRProtocol.NumericWorkerPortChecks

namespace Airbender.Compiler.WorkerPortChecks.BlakeRoundCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def originalPairs := Airbender.Compiler.WorkerPortsNative.BlakeRoundCached.originalIndices.map (fun index =>
  (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement index), Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement.original index)))
noncomputable def historyPairs := (List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).flatMap (fun index =>
  (List.finRange 2).map (fun limb => (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement ((Airbender.Blake2Round.importedConstraintsMemoryPorts[index.val]).clock.previous[limb.val])), Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement.readTimestamp index.val limb))))
noncomputable def indexBounds := (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows ++ Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows).flatMap (fun row => row.fields.flatMap (fun field => field.historyIndices.map (fun index => (index.1, Airbender.Blake2Round.importedConstraintsMemoryPorts.size))))
noncomputable def original : NumericWorkerPortChecks.Typed := ⟨originalPairs ++ historyPairs, indexBounds⟩

theorem history_predicate : Airbender.Compiler.WorkerPortsNative.BlakeRoundCached.historyPredicate = (fun index => (List.finRange 2).all (fun limb => decide (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement ((Airbender.Blake2Round.importedConstraintsMemoryPorts[index.val]).clock.previous[limb.val])) = Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement.readTimestamp index.val limb)))) := by rfl

theorem original_check (checked : original.check = true) :
    ((Airbender.Compiler.WorkerPortsNative.BlakeRoundCached.originalIndices.all (fun index =>
    decide (Airbender.Compiler.FullArithmeticNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BlakeRoundCached.native.placement index) =
      Airbender.Compiler.MemoryNative.BlakeRoundCached.native.bank.address (Airbender.Compiler.MemoryNative.BlakeRoundCached.native.sourcePlacement.original index))) = true) ∧ ((List.finRange Airbender.Blake2Round.importedConstraintsMemoryPorts.size).all Airbender.Compiler.WorkerPortsNative.BlakeRoundCached.historyPredicate = true)) ∧ ((Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryReadRows ++ Airbender.Compiler.MemoryNative.BlakeRoundCached.native.memoryWriteRows).all
      (fun row => row.fields.all (fun field => field.historyIndices.all
        (fun index => decide (index.1 < Airbender.Blake2Round.importedConstraintsMemoryPorts.size)))) = true) := by
  rw [history_predicate]
  simpa only [original, NumericWorkerPortChecks.Typed.check, originalPairs, historyPairs,
    indexBounds, List.all_append, List.all_map, List.all_flatMap, Function.comp_def, Bool.and_eq_true] using checked

end Airbender.Compiler.WorkerPortChecks.BlakeRoundCached
