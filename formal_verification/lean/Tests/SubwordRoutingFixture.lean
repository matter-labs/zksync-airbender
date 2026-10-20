import Airbender.Review.Circuits.SubwordMemory.Routing
import Airbender.Review.Circuits.SubwordMemory.Lookups

namespace Tests.SubwordRoutingFixture
open Airbender Verification SubwordMemory
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

def rom : WordROM := ⟨[BitVec.ofNat 32 305430782,BitVec.ofNat 32 2309737967],by decide⟩

/-- Complete local native rows for lower/upper ROM loads, signed RAM loads,
    an x0 load, an odd-byte store and a halfword store. Public decoding/history
    are deliberately not asserted by these local nonemptiness fixtures. -/
def values : Fin 6 → Array Nat
  | 0 => #[0,0,4,0,1,1,2,3,0,0,0,0,0,4,0,8,0,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,32769,32769,1,3,0,0,0,65534,65535,33022,4660,33022,65534,65535,32769,0,98556,0,98556,0,0,33022,4660,46,33022,65534,65535,45,65534,65535,65534,65535,1227138194,0,2147450879,0,0,0,1,0,0,1,0,0,1,0]
  | 1 => #[0,0,4,0,1,1,2,3,0,0,0,5,0,4,0,8,0,6,0,6,0,0,2,3,1,1,0,0,0,0,4,0,32769,32769,1,3,0,0,0,35243,0,52719,35243,35243,35243,0,32769,0,0,87962,0,87962,1,52719,35243,46,1477035,35243,0,45,35243,0,35243,0,1227138194,0,2147450879,0,0,0,1,0,0,1,0,0,1,0]
  | 2 => #[0,0,4,0,1,1,2,3,0,0,0,0,0,4,0,8,0,1,64,1,64,0,1,1,1,0,1,0,0,0,0,64,32769,32769,1,3,0,0,0,65408,65535,65408,65535,65408,0,0,32769,0,65408,0,65408,0,98305,65408,65535,45,0,0,0,0,65408,65535,65408,65535,1227138194,0,2147450879,0,0,0,1,0,0,1,0,0,1,0]
  | 3 => #[0,0,4,0,1,1,2,0,1,0,0,1,0,4,0,8,0,2,64,2,64,0,2,3,1,1,1,0,0,0,0,64,32769,32769,1,0,0,0,0,0,0,32769,65535,65535,0,0,32769,0,0,32769,0,32769,425985,32769,65535,45,0,0,0,0,32769,65535,0,0,1227138194,0,2147450879,0,0,0,1,0,0,1,0,0,1,0]
  | 4 => #[0,0,4,0,1,1,2,3,0,0,0,0,1,4,0,8,0,3,64,3,64,0,3,3,1,1,1,0,0,0,2,0,4779,57005,0,0,64,17767,35277,17767,43981,205,0,0,43776,0,57005,35277,17767,43981,17767,43981,231885,205,0,54,201387,43776,0,55,0,0,0,0,1227138194,0,2147450879,0,0,0,1,0,0,1,0,0,1,0]
  | 5 => #[0,0,4,0,1,1,2,3,0,0,0,1,1,4,0,8,0,0,64,0,64,0,0,1,1,0,1,0,0,0,2,0,4779,57005,0,0,64,17767,35277,4779,35277,0,0,0,4779,0,4779,17767,4779,35277,4779,35277,279911,0,0,54,266923,4779,0,55,0,0,0,0,1227138194,0,2147450879,0,0,0,1,0,0,1,0,0,1,0]

def assignment (sample : Fin 6) (column : Nat) : ZMod mersenne31Modulus :=
  ((values sample)[column]?.getD 0 : Nat)

/-- Both queries are checked constructively against the complete native table. -/
theorem lookup_members (sample : Fin 6) (slot : Fin 2) :
    (NativeSubwordLookup.table rom).Contains #[]
      #v[assignment sample (52 + 4 * slot.val),assignment sample (53 + 4 * slot.val),
        assignment sample (54 + 4 * slot.val),assignment sample (55 + 4 * slot.val)] := by
  fin_cases sample <;> fin_cases slot
  · change (NativeSubwordLookup.table rom).Contains #[] #v[0,33022,4660,46]
    apply (native_lookup_rom rom #v[0,33022,4660]).mpr
    exact ⟨⟨0,by decide⟩,by decide +kernel⟩
  · change (NativeSubwordLookup.table rom).Contains #[] #v[33022,65534,65535,45]
    apply (native_lookup_load rom #v[33022,65534,65535]).mpr
    exact ⟨⟨33022,by decide⟩,by decide +kernel⟩
  · change (NativeSubwordLookup.table rom).Contains #[] #v[1,52719,35243,46]
    apply (native_lookup_rom rom #v[1,52719,35243]).mpr
    exact ⟨⟨1,by decide⟩,by decide +kernel⟩
  · change (NativeSubwordLookup.table rom).Contains #[] #v[1477035,35243,0,45]
    apply (native_lookup_load rom #v[1477035,35243,0]).mpr
    exact ⟨⟨1477035,by decide⟩,by decide +kernel⟩
  · change (NativeSubwordLookup.table rom).Contains #[] #v[98305,65408,65535,45]
    apply (native_lookup_load rom #v[98305,65408,65535]).mpr
    exact ⟨⟨98305,by decide⟩,by decide +kernel⟩
  · change (NativeSubwordLookup.table rom).Contains #[] #v[0,0,0,0]
    apply (native_lookup_zero rom #v[0,0,0]).mpr
    rfl
  · change (NativeSubwordLookup.table rom).Contains #[] #v[425985,32769,65535,45]
    apply (native_lookup_load rom #v[425985,32769,65535]).mpr
    exact ⟨⟨425985,by decide⟩,by decide +kernel⟩
  · change (NativeSubwordLookup.table rom).Contains #[] #v[0,0,0,0]
    apply (native_lookup_zero rom #v[0,0,0]).mpr
    rfl
  · change (NativeSubwordLookup.table rom).Contains #[] #v[231885,205,0,54]
    apply (native_lookup_store_clear rom #v[231885,205,0]).mpr
    exact ⟨⟨231885,by decide⟩,by decide +kernel⟩
  · change (NativeSubwordLookup.table rom).Contains #[] #v[201387,43776,0,55]
    apply (native_lookup_store_place rom #v[201387,43776,0]).mpr
    exact ⟨⟨201387,by decide⟩,by decide +kernel⟩
  · change (NativeSubwordLookup.table rom).Contains #[] #v[279911,0,0,54]
    apply (native_lookup_store_clear rom #v[279911,0,0]).mpr
    exact ⟨⟨279911,by decide⟩,by decide +kernel⟩
  · change (NativeSubwordLookup.table rom).Contains #[] #v[266923,4779,0,55]
    apply (native_lookup_store_place rom #v[266923,4779,0]).mpr
    exact ⟨⟨266923,by decide⟩,by decide +kernel⟩

end Tests.SubwordRoutingFixture
