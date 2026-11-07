import Airbender.Import.ReducedAuxiliary
import Airbender.Review.Circuits.ReducedMachine.InitializationRangeColumns

namespace Airbender.Import.ReducedInitializationRange
open Lean Elab Command

/-- Reuse complete unchanged body and all18 stage2-field validation on this
    SAME source read. Expose only the validated extra address-pair columns. -/
def parse (source : String) : Except String Airbender.ReducedMachine.Native.InitializationRangeLayout := do
  let full ← ReducedAuxiliary.parse source
  let json ← Json.parse source
  let stage ← json.getObjVal? "stage_2_layout"
  let pair ← stage.getObjVal? "lazy_init_address_range_check_16"
  let base ← pair.getObjVal? "base_field_oracles"
  let quartic ← pair.getObjVal? "ext_4_field_oracles"
  let baseStart : Nat ← fromJson? (← base.getObjVal? "start")
  let quarticStart : Nat ← fromJson? (← quartic.getObjVal? "start")
  return ⟨full.traceLength,full.extensionOffset,full.width,⟨baseStart⟩,⟨quarticStart⟩⟩

elab "import_native_reduced_initialization_range " name:ident " from " path:str : command => do
  let source ← IO.FS.readFile path.getString
  let layout ← match parse source with
    | .ok layout => pure layout | .error e => throwError "Reduced initialization range import failed: {e}"
  let bytes := mkIdent (name.getId.appendAfter "SourceBytes")
  elabCommand (← `(def $name : Airbender.ReducedMachine.Native.InitializationRangeLayout :=
    ⟨$(quote layout.traceLength),$(quote layout.extensionOffset),$(quote layout.width),
      ⟨$(quote layout.product.index)⟩,⟨$(quote layout.accumulator.start)⟩⟩))
  elabCommand (← `(def $bytes : String := $(quote source)))
end Airbender.Import.ReducedInitializationRange
