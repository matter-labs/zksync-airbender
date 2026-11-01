import Airbender.Proofs.GKRProtocol.FunctionalStepChecks.BigintUncached.Bindings

namespace Airbender.Compiler.FunctionalStepChecks.BigintUncached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericFunctionalStepChecks.treeCheck ∅ ports = true := by decide +kernel

theorem programChecked : FunctionalProgram.check Airbender.Compiler.FunctionalNative.BigintUncached.native.isBase [] Airbender.Compiler.FunctionalNative.BigintUncached.native.program = true :=
  NumericFunctionalStepChecks.tree_check_sound Airbender.Compiler.FunctionalNative.BigintUncached.native.isBase Airbender.Compiler.FunctionalNative.BigintUncached.native.program ports ports_binding checked

noncomputable def entries := NumericFunctionalStepChecks.sourceEntries [] Airbender.Compiler.FunctionalNative.BigintUncached.native.program

theorem entriesChecked : entries.all (fun entry => entry.2.check Airbender.Compiler.FunctionalNative.BigintUncached.native.isBase entry.1) = true :=
  (NumericFunctionalStepChecks.sourceEntries_check Airbender.Compiler.FunctionalNative.BigintUncached.native.isBase [] Airbender.Compiler.FunctionalNative.BigintUncached.native.program).trans programChecked

theorem entriesLength : entries.length = 192 := by
  rw [entries, NumericFunctionalStepChecks.sourceEntries_length, programLength]

end Airbender.Compiler.FunctionalStepChecks.BigintUncached
