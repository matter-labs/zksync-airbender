import Airbender.Review.Trace.Families.SubwordMemory.Address
import Tests.SubwordWordBounds

namespace Tests.SubwordAddresses
open Airbender Verification Arithmetic Trace SubwordMemory Tests.SubwordBoundsRows Tests.SubwordBoundsWitness Tests.SubwordBoundsFixture
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- The same full native decoded initialized traces now discharge every address
    interface, including stores, x0 and the source/destination alias. -/
theorem public_addresses (sample : Fin 8) :
    ∀ row ∈ (trace sample).rows, ∃ selected ∈ (Tests.SubwordWordBounds.setup sample).program,
      selected.SourceWith (before sample) SubwordMemory.decoderFields ∧ DecodedFields row.assignment selected ∧
      NativeAddress row.assignment :=
  SubwordMemory.public_native_addresses (Tests.SubwordWordBounds.constructed sample)
    (public_inputs sample) (accepted sample) (Tests.SubwordWordBounds.decoded sample)

theorem actual_addresses (sample : Fin 8) : NativeAddress (assignment sample) := by
  obtain ⟨_,_,_,_,address⟩ := public_addresses sample (nativeRow sample) (by simp [trace])
  exact address

/-- Native low offset and containing word are observed, rather than supplied
    as premises to the integrated address claim. -/
theorem observed_cells (sample : Fin 8) :
    (cellWord (assignment sample)).toBitVec = address sample ∧
    (addressWord (assignment sample)).toBitVec = sourceValue sample := by
  fin_cases sample <;> decide +kernel

end Tests.SubwordAddresses
