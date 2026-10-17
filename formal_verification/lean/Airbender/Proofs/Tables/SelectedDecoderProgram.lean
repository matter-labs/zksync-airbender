import Airbender.Proofs.Tables.ImportedDecoder
import Airbender.Review.Helpers.Decoder.PooledProgram
import Airbender.Review.Circuits.UnifiedReduced.Decoder

namespace Airbender.Trace.NativeDecoder.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem selected_text_extent : ROM.nativeProgramData.text_words = 1048576 := rfl

def selectedIndex (index : Fin 4) : Fin ROM.nativeProgramData.text_words :=
  ⟨index.val, by have := index.isLt; change index.val < 1048576; omega⟩

private theorem pooled_entry_present (index : Fin 4) :
    (selectedEntry pooledDecoderFields (selectedIndex index)).isSome := by
  fin_cases index <;> decide +kernel

def pooledEntry (index : Fin 4) : PooledProgramEntry :=
  (selectedEntry pooledDecoderFields (selectedIndex index)).get (pooled_entry_present index)

def pooledProgram : List PooledProgramEntry := (List.finRange 4).map pooledEntry

theorem pooled_program_member (index : Fin 4) : pooledEntry index ∈ pooledProgram := by
  simp [pooledProgram]

theorem pooled_entry_member (index : Fin 4) :
    pooledEntry index ∈ selectedProgram pooledDecoderFields := by
  apply List.mem_filterMap.mpr
  refine ⟨selectedIndex index, by simp, ?_⟩
  exact (Option.some_get (pooled_entry_present index)).symm

private theorem unified_entry_present (index : Fin 4) :
    (selectedEntry UnifiedReduced.decoderFields (selectedIndex index)).isSome := by
  fin_cases index <;> decide +kernel

def unifiedEntry (index : Fin 4) : UnifiedReduced.ProgramEntry :=
  (selectedEntry UnifiedReduced.decoderFields (selectedIndex index)).get (unified_entry_present index)

def unifiedProgram : List UnifiedReduced.ProgramEntry := (List.finRange 4).map unifiedEntry

theorem unified_program_member (index : Fin 4) : unifiedEntry index ∈ unifiedProgram := by
  simp [unifiedProgram]

theorem unified_entry_member (index : Fin 4) :
    unifiedEntry index ∈ selectedProgram UnifiedReduced.decoderFields := by
  apply List.mem_filterMap.mpr
  refine ⟨selectedIndex index, by simp, ?_⟩
  exact (Option.some_get (unified_entry_present index)).symm

end Airbender.Trace.NativeDecoder.Proofs
