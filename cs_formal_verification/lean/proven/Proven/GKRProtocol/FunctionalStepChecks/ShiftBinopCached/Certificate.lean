module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.FunctionalStepChecks.ShiftBinopCached.Bindings

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.FunctionalStepChecks.ShiftBinopCached
open Airbender.Compiler
set_option maxRecDepth 8192

theorem checked : NumericFunctionalStepChecks.treeCheck ∅ ports = true := by decide +kernel

theorem programChecked : FunctionalProgram.check Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.isBase [] Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.program = true :=
  NumericFunctionalStepChecks.tree_check_sound Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.isBase Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.program ports ports_binding checked

noncomputable def entries := NumericFunctionalStepChecks.sourceEntries [] Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.program

theorem entriesChecked : entries.all (fun entry => entry.2.check Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.isBase entry.1) = true :=
  (NumericFunctionalStepChecks.sourceEntries_check Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.isBase [] Airbender.Compiler.FunctionalNative.ShiftBinopCached.native.program).trans programChecked

theorem entriesLength : entries.length = 51 := by
  rw [entries, NumericFunctionalStepChecks.sourceEntries_length, programLength]

end Airbender.Compiler.FunctionalStepChecks.ShiftBinopCached
