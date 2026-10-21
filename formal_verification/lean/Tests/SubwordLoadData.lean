import Airbender.Review.Trace.Families.SubwordMemory.Loads
import Tests.SubwordWordBounds

namespace Tests.SubwordLoadData
open Airbender Verification Arithmetic Trace SubwordMemory Tests.SubwordBoundsWitness Tests.SubwordBoundsFixture
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- All eight complete native initialized decoded traces derive the original
    Sail extension value functions, preserving x0/aliases and exact ROM indexing. -/
theorem public_loads (sample : Fin 8) :
    ∀ row ∈ (trace sample).rows, ∃ selected ∈ (Tests.SubwordWordBounds.setup sample).program,
      selected.SourceWith (before sample) SubwordMemory.decoderFields ∧ DecodedFields row.assignment selected ∧
      NativeAddress row.assignment ∧ NativeLoadEffects (trace sample).rom row.assignment selected :=
  SubwordMemory.public_native_loads (Tests.SubwordWordBounds.constructed sample)
    (public_inputs sample) (accepted sample) (Tests.SubwordWordBounds.decoded sample)

theorem actual_loads (sample : Fin 8) :
    ∃ selected ∈ (Tests.SubwordWordBounds.setup sample).program,
      selected.SourceWith (before sample) SubwordMemory.decoderFields ∧ DecodedFields (assignment sample) selected ∧
      NativeAddress (assignment sample) ∧ NativeLoadEffects rom (assignment sample) selected :=
  public_loads sample (nativeRow sample) (by simp [trace])

/-- Native ROM data is independent of the initialized instruction shadow.
    The theorem retains that boundary instead of equating the two memories. -/
theorem actual_rom_word :
    (loadWord rom (assignment ⟨0,by decide⟩)).toBitVec = 0x123480fe ∧
    (dataWord (assignment ⟨0,by decide⟩)).toBitVec = 0x00008183 ∧
    (writtenWord (assignment ⟨0,by decide⟩)).toBitVec = 0xfffffffe := by
  decide +kernel

end Tests.SubwordLoadData
