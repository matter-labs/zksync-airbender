import Airbender.Review.Trace.Families.SubwordMemory.Stores
import Tests.SubwordWordBounds

namespace Tests.SubwordStoreData
open Airbender Verification Arithmetic Trace SubwordMemory Tests.SubwordBoundsWitness Tests.SubwordBoundsFixture
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Existing complete native initialized traces derive the new byte-window
    claim with the same actual public state and original decoded instructions. -/
theorem public_stores (sample : Fin 8) :
    ∀ row ∈ (trace sample).rows, ∃ selected ∈ (Tests.SubwordWordBounds.setup sample).program,
      selected.SourceWith (before sample) SubwordMemory.decoderFields ∧ DecodedFields row.assignment selected ∧
      NativeAddress row.assignment ∧ NativeStoreEffects row.assignment selected :=
  SubwordMemory.public_native_stores (Tests.SubwordWordBounds.constructed sample)
    (public_inputs sample) (accepted sample) (Tests.SubwordWordBounds.decoded sample)

theorem actual_stores (sample : Fin 8) :
    ∃ selected ∈ (Tests.SubwordWordBounds.setup sample).program,
      selected.SourceWith (before sample) SubwordMemory.decoderFields ∧ DecodedFields (assignment sample) selected ∧
      NativeAddress (assignment sample) ∧ NativeStoreEffects (assignment sample) selected :=
  public_stores sample (nativeRow sample) (by simp [trace])

/-- Full accepted SB at offset three preserves the other three old bytes and
    takes only the low source byte, including its high bit. -/
theorem actual_sb :
    (dataWord (assignment ⟨4,by decide⟩)).toBitVec = 0xdead12ab ∧
    (oldWord (assignment ⟨4,by decide⟩)).toBitVec = 0x89cd4567 ∧
    (writtenWord (assignment ⟨4,by decide⟩)).toBitVec = 0xabcd4567 := by
  decide +kernel

/-- Full accepted SH replaces the low halfword, ignoring the high source limb
    and preserving both high old bytes. -/
theorem actual_sh :
    (dataWord (assignment ⟨5,by decide⟩)).toBitVec = 0xdead12ab ∧
    (oldWord (assignment ⟨5,by decide⟩)).toBitVec = 0x89cd4567 ∧
    (writtenWord (assignment ⟨5,by decide⟩)).toBitVec = 0x89cd12ab := by
  decide +kernel

end Tests.SubwordStoreData
