import Airbender.Proofs.Tables.ImportedDecoder
import Airbender.Data.Decoder.SelectedProgram

namespace Airbender.Trace.NativeDecoder.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

theorem selected_text_extent : ROM.nativeProgramData.text_words = 1048576 := rfl

def selectedIndex (index : Fin 4) : Fin ROM.nativeProgramData.text_words :=
  _root_.Airbender.Trace.NativeDecoder.selectedIndex index

private theorem pooled_entry_present (index : Fin 4) :
    (selectedEntry pooledDecoderFields (selectedIndex index)).isSome := by
  fin_cases index <;> decide +kernel

def pooledEntry (index : Fin 4) : PooledProgramEntry :=
  _root_.Airbender.Trace.NativeDecoder.pooledEntry index

def pooledProgram : List PooledProgramEntry := _root_.Airbender.Trace.NativeDecoder.pooledProgram

theorem pooled_program_member (index : Fin 4) : pooledEntry index ∈ pooledProgram := by
  simp [pooledProgram, _root_.Airbender.Trace.NativeDecoder.pooledProgram, pooledEntry]

theorem pooled_entry_member (index : Fin 4) :
    pooledEntry index ∈ selectedProgram pooledDecoderFields := by
  apply List.mem_filterMap.mpr
  refine ⟨selectedIndex index, by simp, ?_⟩
  exact (Option.some_get (pooled_entry_present index)).symm

private theorem unified_entry_present (index : Fin 4) :
    (selectedEntry UnifiedReduced.decoderFields (selectedIndex index)).isSome := by
  fin_cases index <;> decide +kernel

def unifiedEntry (index : Fin 4) : UnifiedReduced.ProgramEntry :=
  _root_.Airbender.Trace.NativeDecoder.unifiedEntry index

def unifiedProgram : List UnifiedReduced.ProgramEntry := _root_.Airbender.Trace.NativeDecoder.unifiedProgram

theorem unified_program_member (index : Fin 4) : unifiedEntry index ∈ unifiedProgram := by
  simp [unifiedProgram, _root_.Airbender.Trace.NativeDecoder.unifiedProgram, unifiedEntry]

theorem unified_entry_member (index : Fin 4) :
    unifiedEntry index ∈ selectedProgram UnifiedReduced.decoderFields := by
  apply List.mem_filterMap.mpr
  refine ⟨selectedIndex index, by simp, ?_⟩
  exact (Option.some_get (unified_entry_present index)).symm

end Airbender.Trace.NativeDecoder.Proofs
