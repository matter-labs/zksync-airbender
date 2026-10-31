import Airbender.Proofs.GKRProtocol.PublicProgramImage
import Airbender.Proofs.Tables.SelectedDecoderProgram
import Airbender.Review.Helpers.Memory.ImportedImage
import Airbender.Proofs.GKRProtocol.ProgramProfile
import Airbender.Review.Helpers.Decoder.PooledExternalInput

namespace Airbender.Compiler.PublicProgram
open Airbender Airbender.Trace Airbender.Trace.NativeDecoder
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

/-- The selected text and the public ROM image are independently imported
fields of the same retained setup. Their complete block encodings agree. -/
theorem text_image : ROM.nativeProgramData.text = ROM.nativeProgramData.image := by
  decide +kernel

theorem selected_bytes {before : Reference.RiscV.Sail.State}
    (image : ROM.ImportedImage before) : SelectedBytes before := by
  intro index
  have bound : 4 * index.val < 2 ^ 32 := by
    have small : index.val < 1048576 := index.isLt
    omega
  change (_root_.Sail.ArchSem.readBytes (ue := SailRV32.exception) 4
    (BitVec.ofNat 32 (4 * index.val)).toNat).run before = _
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound, text_image]
  exact image ⟨index.val, index.isLt⟩

theorem pooled_sources {before : Reference.RiscV.Sail.State}
    (image : ROM.ImportedImage before) :
    ∀ entry ∈ pooledProgram, entry.SourceWith before pooledDecoderFields := by
  intro entry member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact NativeDecoder.Proofs.selected_sources (selected_bytes image) _
    (NativeDecoder.Proofs.pooled_entry_member index)

theorem unified_sources {before : Reference.RiscV.Sail.State}
    (image : ROM.ImportedImage before) :
    ∀ entry ∈ unifiedProgram, entry.SourceWith before UnifiedReduced.decoderFields := by
  intro entry member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact NativeDecoder.Proofs.selected_sources (selected_bytes image) _
    (NativeDecoder.Proofs.unified_entry_member index)

theorem pooled_image {before : Reference.RiscV.Sail.State}
    (image : ROM.ImportedImage before) :
    programImageRunWith pooledDecoderFields before (pooledProgram.map ProgramEntry.pc) =
      some pooledProgram := image_run pooledProgram (pooled_sources image)

theorem unified_image {before : Reference.RiscV.Sail.State}
    (image : ROM.ImportedImage before) :
    programImageRunWith UnifiedReduced.decoderFields before (unifiedProgram.map ProgramEntry.pc) =
      some unifiedProgram := image_run unifiedProgram (unified_sources image)

theorem pooled_code : ∀ entry ∈ pooledProgram,
    entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0 := by
  intro entry member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  fin_cases index <;> decide +kernel

private theorem pooled_load_guard (index : Fin 4) :
    ProgramProfile.discardedLoad (pooledEntry index).instruction = false := by
  fin_cases index <;> decide +kernel

theorem pooled_loads : NoDiscardedLoads pooledProgram := by
  apply ProgramProfile.no_discarded_loads
  intro entry member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact pooled_load_guard index

theorem unified_code : ∀ entry ∈ unifiedProgram,
    entry.pc.toNat < ROM.limit ∧ entry.pc.toNat % 4 = 0 := by
  intro entry member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  fin_cases index <;> decide +kernel

private theorem unified_load_guard (index : Fin 4) :
    ProgramProfile.discardedLoad (unifiedEntry index).instruction = false := by
  fin_cases index <;> decide +kernel

theorem unified_loads : NoDiscardedLoads unifiedProgram := by
  apply ProgramProfile.no_discarded_loads
  intro entry member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact unified_load_guard index

/-- The actual selected entries have the same metadata in the extended input
registry. This is checked on their original Sail instruction constructors. -/
theorem pooled_external_fields (index : Fin 4) :
    NonDeterminism.Pooled.decoderFields (pooledEntry index).instruction =
      some (pooledEntry index).data := by
  fin_cases index <;> rfl

theorem pooled_external_sources {before : Reference.RiscV.Sail.State}
    (image : ROM.ImportedImage before) :
    ∀ entry ∈ pooledProgram, entry.SourceWith before NonDeterminism.Pooled.decoderFields := by
  intro entry member
  have original := pooled_sources image entry member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact ⟨original.bytes, original.decoded, pooled_external_fields index⟩

theorem pooled_external_image {before : Reference.RiscV.Sail.State}
    (image : ROM.ImportedImage before) :
    programImageRunWith NonDeterminism.Pooled.decoderFields before (pooledProgram.map ProgramEntry.pc) =
      some pooledProgram := image_run pooledProgram (pooled_external_sources image)

end Airbender.Compiler.PublicProgram
