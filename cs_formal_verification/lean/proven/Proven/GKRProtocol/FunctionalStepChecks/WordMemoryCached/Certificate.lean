module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FunctionalStepChecks.WordMemoryCached.Bindings

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FunctionalStepChecks.WordMemoryCached
open Airbender.Compiler
set_option maxRecDepth 8192

theorem checked : NumericFunctionalStepChecks.treeCheck ∅ ports = true := by decide +kernel

theorem programChecked : FunctionalProgram.check Airbender.Compiler.FunctionalNative.WordMemoryCached.native.isBase [] Airbender.Compiler.FunctionalNative.WordMemoryCached.native.program = true :=
  NumericFunctionalStepChecks.tree_check_sound Airbender.Compiler.FunctionalNative.WordMemoryCached.native.isBase Airbender.Compiler.FunctionalNative.WordMemoryCached.native.program ports ports_binding checked

noncomputable def entries := NumericFunctionalStepChecks.sourceEntries [] Airbender.Compiler.FunctionalNative.WordMemoryCached.native.program

theorem entriesChecked : entries.all (fun entry => entry.2.check Airbender.Compiler.FunctionalNative.WordMemoryCached.native.isBase entry.1) = true :=
  (NumericFunctionalStepChecks.sourceEntries_check Airbender.Compiler.FunctionalNative.WordMemoryCached.native.isBase [] Airbender.Compiler.FunctionalNative.WordMemoryCached.native.program).trans programChecked

theorem entriesLength : entries.length = 44 := by
  rw [entries, NumericFunctionalStepChecks.sourceEntries_length, programLength]

end Airbender.Compiler.FunctionalStepChecks.WordMemoryCached
