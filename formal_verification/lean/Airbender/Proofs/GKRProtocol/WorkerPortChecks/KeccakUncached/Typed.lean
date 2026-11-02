import Airbender.Proofs.GKRProtocol.WorkerPortChecks.KeccakUncached.Inputs
import Airbender.Proofs.GKRProtocol.NumericWorkerPortChecks

namespace Airbender.Compiler.WorkerPortChecks.KeccakUncached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

noncomputable def originalPairs := Airbender.Compiler.WorkerPortsNative.KeccakUncached.originalIndices.map (fun index =>
  (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement index), Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.address (Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement.original index)))
noncomputable def historyPairs := (List.finRange Airbender.Keccak.importedConstraintsMemoryPorts.size).flatMap (fun index =>
  (List.finRange 2).map (fun limb => (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement ((Airbender.Keccak.importedConstraintsMemoryPorts[index.val]).clock.previous[limb.val])), Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.address (Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement.readTimestamp index.val limb))))
noncomputable def indexBounds := (Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows ++ Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows).flatMap (fun row => row.fields.flatMap (fun field => field.historyIndices.map (fun index => (index.1, Airbender.Keccak.importedConstraintsMemoryPorts.size))))
noncomputable def original : NumericWorkerPortChecks.Typed := ⟨originalPairs ++ historyPairs, indexBounds⟩

theorem original_check (checked : original.check = true) :
    ((Airbender.Compiler.WorkerPortsNative.KeccakUncached.originalIndices.all (fun index =>
    decide (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement index) =
      Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.address (Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement.original index))) = true) ∧ (((List.finRange Airbender.Keccak.importedConstraintsMemoryPorts.size).all (fun index =>
    (List.finRange 2).all (fun limb => decide
      (Airbender.Compiler.FullArithmeticNative.KeccakUncached.native.bank.address (Airbender.Compiler.CleanArithmeticNative.KeccakUncached.native.placement
        ((Airbender.Keccak.importedConstraintsMemoryPorts[index.val]).clock.previous[limb.val])) =
       Airbender.Compiler.MemoryNative.KeccakUncached.native.bank.address (Airbender.Compiler.MemoryNative.KeccakUncached.native.sourcePlacement.readTimestamp index.val limb))))) = true)) ∧ ((Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryReadRows ++ Airbender.Compiler.MemoryNative.KeccakUncached.native.memoryWriteRows).all
      (fun row => row.fields.all (fun field => field.historyIndices.all
        (fun index => decide (index.1 < Airbender.Keccak.importedConstraintsMemoryPorts.size)))) = true) := by
  simpa only [original, NumericWorkerPortChecks.Typed.check, originalPairs, historyPairs,
    indexBounds, List.all_append, List.all_map, List.all_flatMap, Function.comp_def, Bool.and_eq_true] using checked

end Airbender.Compiler.WorkerPortChecks.KeccakUncached
