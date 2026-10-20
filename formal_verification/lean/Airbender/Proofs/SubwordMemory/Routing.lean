import Airbender.Proofs.SubwordMemory.QueryFields
import Airbender.Review.Circuits.SubwordMemory.RoutingModel

namespace Airbender.SubwordMemory.Proofs
open Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

variable {rom : WordROM} {w : Nat → ZMod mersenne31Modulus}

theorem mode_routing (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) : ModeRouting w := by
  have separator := (separator_values holds).1
  rcases store_bit holds with load | store
  · by_cases range : (w 20).val < 64
    · have ram : w 26 = 0 := by simpa [range] using separator
      exact Or.inl ⟨load,range,rom_tags holds load ram⟩
    · have ram : w 26 = 1 := by simpa [range] using separator
      exact Or.inr (Or.inl ⟨load,by omega,ram_tags holds load ram⟩)
  · have ram := store_requires_ram holds store
    have range : 64 ≤ (w 20).val := by
      by_contra bad
      have zero : w 26 = 0 := by simpa [show (w 20).val < 64 by omega] using separator
      have impossible : (0 : ZMod mersenne31Modulus) = 1 := zero.symm.trans ram
      exact (by decide +kernel : (0 : ZMod mersenne31Modulus) ≠ 1) impossible
    exact Or.inr (Or.inr ⟨store,range,store_tags holds store⟩)

/-- Resolve the actual two accepted ROM-load queries after deriving their fields. -/
theorem rom_load_routing (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (load : w 12 = 0) (range : (w 20).val < 64) : ROMLoadRouting rom w := by
  have ram : w 26 = 0 := by simpa [range] using (separator_values holds).1
  obtain ⟨tag0,tag1⟩ := rom_tags holds load ram
  obtain ⟨key0,lo0,hi0,key1,lo1,hi1⟩ := rom_fields holds load ram
  have limb := (selected_limbs holds).1
  constructor
  · apply (NativeLookupProofs.rom_membership rom _).mp
    change (NativeSubwordLookup.table rom).Contains #[] #v[romWordKey w,w 41,w 42,46]
    simpa only [romWordKey,Nat.reduceMul,Nat.reduceAdd,key0,lo0,hi0,tag0] using native_queries holds ⟨0,by decide⟩
  · apply (NativeLookupProofs.load_membership rom _).mp
    change (NativeSubwordLookup.table rom).Contains #[]
      #v[dataKey w (selectedLimb w 41 42),w 44,w 45,45]
    simpa only [dataKey,selectedLimb,Nat.reduceMul,Nat.reduceAdd,key1,lo1,hi1,tag1,limb]
      using native_queries holds ⟨1,by decide⟩

/-- A RAM load's second slot is the actual all-zero query. -/
theorem ram_load_routing (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (load : w 12 = 0) (range : 64 ≤ (w 20).val) : RAMLoadRouting w := by
  have ram : w 26 = 1 := by simpa [show ¬ (w 20).val < 64 by omega] using (separator_values holds).1
  obtain ⟨tag0,_⟩ := ram_tags holds load ram
  obtain ⟨key0,lo0,hi0,key1,lo1,hi1⟩ := ram_fields holds load ram
  have limb := (selected_limbs holds).2.1
  constructor
  · apply (NativeLookupProofs.load_membership rom _).mp
    change (NativeSubwordLookup.table rom).Contains #[]
      #v[dataKey w (selectedLimb w 32 33),w 41,w 42,45]
    simpa only [dataKey,selectedLimb,Nat.reduceMul,Nat.reduceAdd,key0,lo0,hi0,tag0,limb]
      using native_queries holds ⟨0,by decide⟩
  · rw [key1,lo1,hi1]

/-- Store inputs use the old RAM word and the source register's low limb. -/
theorem store_routing (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom)) (store : w 12 = 1) : StoreRouting w := by
  obtain ⟨tag0,tag1⟩ := store_tags holds store
  obtain ⟨key0,lo0,hi0,key1,lo1,hi1⟩ := store_fields holds store
  have limb := (selected_limbs holds).2.2
  constructor
  · rcases mode_routing holds with romCase | ramCase | storeCase
    · have bad := romCase.1.symm.trans store
      exact False.elim ((by decide +kernel : (0 : ZMod mersenne31Modulus) ≠ 1) bad)
    · have bad := ramCase.1.symm.trans store
      exact False.elim ((by decide +kernel : (0 : ZMod mersenne31Modulus) ≠ 1) bad)
    · exact storeCase.2.1
  · apply (NativeLookupProofs.store_clear_membership rom _).mp
    change (NativeSubwordLookup.table rom).Contains #[]
      #v[dataKey w (selectedLimb w 37 38),w 41,w 42,54]
    simpa only [dataKey,selectedLimb,Nat.reduceMul,Nat.reduceAdd,key0,lo0,hi0,tag0,limb]
      using native_queries holds ⟨0,by decide⟩
  · apply (NativeLookupProofs.store_place_membership rom _).mp
    change (NativeSubwordLookup.table rom).Contains #[] #v[dataKey w (w 32),w 44,w 45,55]
    simpa only [dataKey,Nat.reduceMul,Nat.reduceAdd,key1,lo1,hi1,tag1]
      using native_queries holds ⟨1,by decide⟩

end Airbender.SubwordMemory.Proofs
