import GKRCompiler.Import

namespace Airbender.Compiler.Native.ShiftBinopCached
open Airbender Airbender.Compiler
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

import_compiler_arithmetic native from "artifacts/compiler/shift-binop-cached.json"
  certificate "artifacts/compiler/shift-binop-cached-certificate.json"

theorem source_preserved {values} (holds : native.artifact.LoweredHolds values) :
    native.artifact.SourceHolds (values ∘ native.artifact.placement) :=
  native.artifact.backward native.selected native.extension native.certificate
    native.gatesChecked native.checked holds

theorem source_extends {values} (holds : native.artifact.SourceHolds values) :
    ∃ extended,
      (∀ wire, extended (native.artifact.placement wire) = values wire) ∧
      (∀ index ∈ native.selected, (native.artifact.gates.get index).expressionResidual extended = 0) :=
  native.artifact.forward native.selected native.extension native.certificate
    native.gatesChecked native.checked holds

end Airbender.Compiler.Native.ShiftBinopCached
