import Airbender.Import.Compiler.Arithmetic.UnifiedUncached

namespace Airbender.Compiler.Native.UnifiedUncached
open Airbender Airbender.Compiler

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

end Airbender.Compiler.Native.UnifiedUncached
