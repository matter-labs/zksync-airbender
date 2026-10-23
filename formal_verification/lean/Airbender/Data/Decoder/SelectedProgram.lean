import Airbender.Review.Helpers.Decoder.ImportedProgram
import Airbender.Review.Helpers.Decoder.PooledProgram
import Airbender.Review.Circuits.UnifiedReduced.Decoder
import Mathlib.Tactic.FinCases

namespace Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

/-- The four leading entries of the retained text, indexed in its complete image.
    These indices do not depend on a trace witness. -/
def selectedIndex (index : Fin 4) : Fin ROM.nativeProgramData.text_words :=
  ⟨index.val, by have := index.isLt; change index.val < 1048576; omega⟩

private theorem pooled_entry_present (index : Fin 4) :
    (selectedEntry pooledDecoderFields (selectedIndex index)).isSome := by
  fin_cases index <;> decide +kernel

/-- Decode the actual retained word and require its pooled projection to exist. -/
def pooledEntry (index : Fin 4) : PooledProgramEntry :=
  (selectedEntry pooledDecoderFields (selectedIndex index)).get (pooled_entry_present index)

def pooledProgram : List PooledProgramEntry := (List.finRange 4).map pooledEntry

private theorem unified_entry_present (index : Fin 4) :
    (selectedEntry UnifiedReduced.decoderFields (selectedIndex index)).isSome := by
  fin_cases index <;> decide +kernel

/-- Decode the same retained word using the unified metadata projection. -/
def unifiedEntry (index : Fin 4) : UnifiedReduced.ProgramEntry :=
  (selectedEntry UnifiedReduced.decoderFields (selectedIndex index)).get (unified_entry_present index)

def unifiedProgram : List UnifiedReduced.ProgramEntry := (List.finRange 4).map unifiedEntry

end Airbender.Trace.NativeDecoder
