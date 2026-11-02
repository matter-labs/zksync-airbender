import Airbender.Proofs.GKRProtocol.WorkerPortChecks.BigintCached.Inputs
import Airbender.Proofs.GKRProtocol.NumericWorkerPortChecks

namespace Airbender.Compiler.WorkerPortChecks.BigintCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def originalPairs := Airbender.Compiler.WorkerPortsNative.BigintCached.originalIndices.map (fun index =>
  (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement index), Airbender.Compiler.MemoryNative.BigintCached.native.bank.address (Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement.original index)))
noncomputable def historyPairs := (List.finRange Airbender.Bigint.importedConstraintsMemoryPorts.size).flatMap (fun index =>
  (List.finRange 2).map (fun limb => (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement ((Airbender.Bigint.importedConstraintsMemoryPorts[index.val]).clock.previous[limb.val])), Airbender.Compiler.MemoryNative.BigintCached.native.bank.address (Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement.readTimestamp index.val limb))))
noncomputable def indexBounds := (Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows ++ Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows).flatMap (fun row => row.fields.flatMap (fun field => field.historyIndices.map (fun index => (index.1, Airbender.Bigint.importedConstraintsMemoryPorts.size))))
noncomputable def original : NumericWorkerPortChecks.Typed := ⟨originalPairs ++ historyPairs, indexBounds⟩

theorem original_check (checked : original.check = true) :
    ((Airbender.Compiler.WorkerPortsNative.BigintCached.originalIndices.all (fun index =>
    decide (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement index) =
      Airbender.Compiler.MemoryNative.BigintCached.native.bank.address (Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement.original index))) = true) ∧ (((List.finRange Airbender.Bigint.importedConstraintsMemoryPorts.size).all (fun index =>
    (List.finRange 2).all (fun limb => decide
      (Airbender.Compiler.FullArithmeticNative.BigintCached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.BigintCached.native.placement
        ((Airbender.Bigint.importedConstraintsMemoryPorts[index.val]).clock.previous[limb.val])) =
       Airbender.Compiler.MemoryNative.BigintCached.native.bank.address (Airbender.Compiler.MemoryNative.BigintCached.native.sourcePlacement.readTimestamp index.val limb))))) = true)) ∧ ((Airbender.Compiler.MemoryNative.BigintCached.native.memoryReadRows ++ Airbender.Compiler.MemoryNative.BigintCached.native.memoryWriteRows).all
      (fun row => row.fields.all (fun field => field.historyIndices.all
        (fun index => decide (index.1 < Airbender.Bigint.importedConstraintsMemoryPorts.size)))) = true) := by
  simpa only [original, NumericWorkerPortChecks.Typed.check, originalPairs, historyPairs,
    indexBounds, List.all_append, List.all_map, List.all_flatMap, Function.comp_def, Bool.and_eq_true] using checked

end Airbender.Compiler.WorkerPortChecks.BigintCached
