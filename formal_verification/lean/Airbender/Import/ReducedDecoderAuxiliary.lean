import Airbender.Import.ReducedAuxiliary
import Airbender.Review.Circuits.ReducedMachine.DecoderAuxiliaryColumns

namespace Airbender.Import.ReducedDecoderAuxiliary
open Lean Elab Command

/-- Reuse complete unchanged body/stage2 validation on this same source read;
    expose the already validated decoder-access group as a typed quartic slot. -/
def parse (source : String) : Except String Airbender.ReducedMachine.Native.DecoderAuxiliaryLayout := do
  let full ← ReducedAuxiliary.parse source
  let json ← Json.parse source
  let stage ← json.getObjVal? "stage_2_layout"
  let access ← stage.getObjVal? "intermediate_poly_for_decoder_accesses"
  let start : Nat ← fromJson? (← access.getObjVal? "start")
  return ⟨full.traceLength,full.extensionOffset,full.width,⟨start⟩⟩

elab "import_native_reduced_decoder_auxiliary " name:ident " from " path:str : command => do
  let source ← IO.FS.readFile path.getString
  let layout ← match parse source with
    | .ok layout => pure layout | .error e => throwError "Reduced decoder auxiliary import failed: {e}"
  let bytes := mkIdent (name.getId.appendAfter "SourceBytes")
  elabCommand (← `(def $name : Airbender.ReducedMachine.Native.DecoderAuxiliaryLayout :=
    ⟨$(quote layout.traceLength),$(quote layout.extensionOffset),$(quote layout.width),⟨$(quote layout.access.start)⟩⟩))
  elabCommand (← `(def $bytes : String := $(quote source)))
end Airbender.Import.ReducedDecoderAuxiliary
