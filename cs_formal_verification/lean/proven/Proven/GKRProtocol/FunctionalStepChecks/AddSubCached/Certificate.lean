module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FunctionalStepChecks.AddSubCached.Bindings

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FunctionalStepChecks.AddSubCached
open Airbender.Compiler
set_option maxRecDepth 8192

theorem checked : NumericFunctionalStepChecks.treeCheck ∅ ports = true := by decide +kernel

theorem programChecked : FunctionalProgram.check Airbender.Compiler.FunctionalNative.AddSubCached.native.isBase [] Airbender.Compiler.FunctionalNative.AddSubCached.native.program = true :=
  NumericFunctionalStepChecks.tree_check_sound Airbender.Compiler.FunctionalNative.AddSubCached.native.isBase Airbender.Compiler.FunctionalNative.AddSubCached.native.program ports ports_binding checked

noncomputable def entries := NumericFunctionalStepChecks.sourceEntries [] Airbender.Compiler.FunctionalNative.AddSubCached.native.program

theorem entriesChecked : entries.all (fun entry => entry.2.check Airbender.Compiler.FunctionalNative.AddSubCached.native.isBase entry.1) = true :=
  (NumericFunctionalStepChecks.sourceEntries_check Airbender.Compiler.FunctionalNative.AddSubCached.native.isBase [] Airbender.Compiler.FunctionalNative.AddSubCached.native.program).trans programChecked

theorem entriesLength : entries.length = 47 := by
  rw [entries, NumericFunctionalStepChecks.sourceEntries_length, programLength]

end Airbender.Compiler.FunctionalStepChecks.AddSubCached
