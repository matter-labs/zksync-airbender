import Airbender.Proofs.SubwordMemory.OffsetValues
import Airbender.Proofs.SubwordMemory.WriteValues
import Airbender.Proofs.SubwordMemory.Routing
import Airbender.Proofs.Tables.AlignedWordROM
import Airbender.Review.Helpers.Tables.SubwordLoadTheorems
import Airbender.Review.Helpers.Tables.SubwordStoreClearTheorems
import Airbender.Review.Helpers.Tables.SubwordStorePlaceTheorems

namespace Airbender.SubwordMemory.Proofs
open Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

variable {rom : WordROM} {w : Nat → ZMod mersenne31Modulus}

/-- Actual public ROM data reaches the certified load candidate and native write. -/
theorem rom_load_values
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (load : w 12 = 0) (range : (w 20).val < 64) :
    ROMWordValues rom w ∧ LoadValues w (dataKey w (selectedLimb w 41 42)) := by
  have queries := rom_load_routing holds load range
  have word := AlignedWordROMProofs.values (by decide : 1048576 < mersenne31Modulus) queries.word
  obtain ⟨keyBound,low,high,loBound,hiBound⟩ := SubwordLoad.native_values queries.data
  have ram : w 26 = 0 := by simpa [range] using (separator_values holds).1
  obtain ⟨candidateLow,candidateHigh⟩ := rom_load_candidate holds load ram
  obtain ⟨writeLow,writeHigh⟩ := load_write_mask holds load
  refine ⟨⟨word.1,word.2.1,word.2.2⟩,⟨keyBound,?_,?_,?_,writeLow,writeHigh⟩⟩
  · exact candidateLow.trans low
  · exact candidateHigh.trans high
  · simpa only [candidateLow,candidateHigh] using And.intro loBound hiBound

/-- RAM data queries determine both bounded candidate limbs before x0 masking. -/
theorem ram_load_values
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (load : w 12 = 0) (range : 64 ≤ (w 20).val) :
    LoadValues w (dataKey w (selectedLimb w 32 33)) := by
  have queries := ram_load_routing holds load range
  obtain ⟨keyBound,low,high,loBound,hiBound⟩ := SubwordLoad.native_values queries.data
  have ram : w 26 = 1 := by simpa [show ¬ (w 20).val < 64 by omega] using (separator_values holds).1
  obtain ⟨candidateLow,candidateHigh⟩ := ram_load_candidate holds load ram
  obtain ⟨writeLow,writeHigh⟩ := load_write_mask holds load
  refine ⟨keyBound,?_,?_,?_,writeLow,writeHigh⟩
  · exact candidateLow.trans low
  · exact candidateHigh.trans high
  · simpa only [candidateLow,candidateHigh] using And.intro loBound hiBound

/-- Both exact native store tables reach the actual written memory columns. -/
theorem store_values
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (store : w 12 = 1) : StoreValues w := by
  have queries := store_routing holds store
  obtain ⟨clearKey,cleared,unusedClear,clearBound⟩ := SubwordStoreClear.native_values queries.clear
  obtain ⟨placeKey,placed,unusedPlace,placeBound⟩ := SubwordStorePlace.native_values queries.place
  obtain ⟨low,high⟩ := store_write_mux holds store
  exact ⟨clearKey,placeKey,cleared,placed,⟨unusedClear,unusedPlace⟩,⟨clearBound,placeBound⟩,low,high⟩

end Airbender.SubwordMemory.Proofs
