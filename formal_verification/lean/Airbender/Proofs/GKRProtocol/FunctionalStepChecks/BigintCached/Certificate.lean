import Airbender.Proofs.GKRProtocol.FunctionalStepChecks.BigintCached.Bindings

namespace Airbender.Compiler.FunctionalStepChecks.BigintCached
open Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 8192

theorem checked : NumericFunctionalStepChecks.treeCheck ∅ ports = true := by decide +kernel

theorem programChecked : FunctionalProgram.check Airbender.Compiler.FunctionalNative.BigintCached.native.isBase [] Airbender.Compiler.FunctionalNative.BigintCached.native.program = true :=
  NumericFunctionalStepChecks.tree_check_sound Airbender.Compiler.FunctionalNative.BigintCached.native.isBase Airbender.Compiler.FunctionalNative.BigintCached.native.program ports ports_binding checked

noncomputable def entries := NumericFunctionalStepChecks.sourceEntries [] Airbender.Compiler.FunctionalNative.BigintCached.native.program

theorem entriesChecked : entries.all (fun entry => entry.2.check Airbender.Compiler.FunctionalNative.BigintCached.native.isBase entry.1) = true :=
  (NumericFunctionalStepChecks.sourceEntries_check Airbender.Compiler.FunctionalNative.BigintCached.native.isBase [] Airbender.Compiler.FunctionalNative.BigintCached.native.program).trans programChecked

theorem entriesLength : entries.length = 294 := by
  rw [entries, NumericFunctionalStepChecks.sourceEntries_length, programLength]

end Airbender.Compiler.FunctionalStepChecks.BigintCached
