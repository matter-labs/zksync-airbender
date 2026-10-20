import Airbender.Review.Circuits.SubwordMemory.Lookups
import Tests.SubwordArtifact
import Tests.SubwordOffset
import Tests.SubwordLoad
import Tests.SubwordStoreClear
import Tests.SubwordStorePlace

namespace Tests.SubwordLookups
open Airbender Verification SubwordMemory
set_option autoImplicit false

private abbrev accepts (rom : WordROM) (query : Vector (ZMod mersenne31Modulus) 4) : Prop :=
  (NativeSubwordLookup.table rom).Contains #[] query

theorem actual_zero (rom : WordROM) : accepts rom #v[0,0,0,0] :=
  (native_lookup_zero rom #v[0,0,0]).mpr rfl

theorem nonzero_inactive_rejected (rom : WordROM) : ¬ accepts rom #v[1,0,0,0] := by
  intro member
  have impossible := (native_lookup_zero rom #v[1,0,0]).mp member
  have wrong : (#v[1,0,0] : Vector (ZMod mersenne31Modulus) 3) ≠ #v[0,0,0] := by decide +kernel
  exact wrong impossible

theorem unsupported_selector_rejected (rom : WordROM) : ¬ accepts rom #v[0,0,0,1] := by
  intro member
  have selected := native_lookup_selector rom _ member
  have canonical : (#v[0,0,0,1] : Vector (ZMod mersenne31Modulus) 4)[3].val = 1 := by decide +kernel
  rw [canonical] at selected
  exact (by decide +kernel : (1 : Nat) ∉ [0,23,44,45,46,54,55]) selected

theorem byte_rom_tag_rejected (rom : WordROM) : ¬ accepts rom #v[0,0,0,24] := by
  intro member
  have selected := native_lookup_selector rom _ member
  have canonical : (#v[0,0,0,24] : Vector (ZMod mersenne31Modulus) 4)[3].val = 24 := by decide +kernel
  rw [canonical] at selected
  exact (by decide +kernel : (24 : Nat) ∉ [0,23,44,45,46,54,55]) selected

theorem separator_rom_edge (rom : WordROM) : accepts rom #v[63,0,63,23] := by
  apply (native_lookup_separator rom #v[63,0,63]).mpr
  refine ⟨⟨63, by decide⟩, ?_⟩
  decide +kernel

theorem separator_ram_edge (rom : WordROM) : accepts rom #v[64,1,0,23] := by
  apply (native_lookup_separator rom #v[64,1,0]).mpr
  refine ⟨⟨64, by decide⟩, ?_⟩
  decide +kernel

theorem offset_native_trap (rom : WordROM) : accepts rom #v[589825,1,5,44] := by
  apply (native_lookup_offset rom #v[589825,1,5]).mpr
  refine ⟨⟨589825, by decide⟩, ?_⟩
  decide +kernel

theorem offset_native_x0_raw_key (rom : WordROM) : accepts rom #v[1638401,1,1,44] := by
  apply (native_lookup_offset rom #v[1638401,1,1]).mpr
  refine ⟨⟨1638401, by decide⟩, ?_⟩
  decide +kernel

theorem load_signed_byte (rom : WordROM) : accepts rom #v[128,65408,65535,45] := by
  apply (native_lookup_load rom #v[128,65408,65535]).mpr
  refine ⟨⟨128, by decide⟩, ?_⟩
  decide +kernel

theorem load_signed_half (rom : WordROM) : accepts rom #v[294912,32768,65535,45] := by
  apply (native_lookup_load rom #v[294912,32768,65535]).mpr
  refine ⟨⟨294912, by decide⟩, ?_⟩
  decide +kernel

theorem load_unsigned_half (rom : WordROM) : accepts rom #v[1376255,65535,0,45] := by
  apply (native_lookup_load rom #v[1376255,65535,0]).mpr
  refine ⟨⟨1376255, by decide⟩, ?_⟩
  decide +kernel

theorem load_last_raw_key (rom : WordROM) : accepts rom #v[2097151,0,0,45] := by
  apply (native_lookup_load rom #v[2097151,0,0]).mpr
  refine ⟨⟨2097151, by decide⟩, ?_⟩
  decide +kernel

theorem store_clear_even (rom : WordROM) : accepts rom #v[65535,65280,0,54] := by
  apply (native_lookup_store_clear rom #v[65535,65280,0]).mpr
  refine ⟨⟨65535, by decide⟩, ?_⟩
  decide +kernel

theorem store_clear_odd (rom : WordROM) : accepts rom #v[131071,255,0,54] := by
  apply (native_lookup_store_clear rom #v[131071,255,0]).mpr
  refine ⟨⟨131071, by decide⟩, ?_⟩
  decide +kernel

theorem store_place_even (rom : WordROM) : accepts rom #v[65535,255,0,55] := by
  apply (native_lookup_store_place rom #v[65535,255,0]).mpr
  refine ⟨⟨65535, by decide⟩, ?_⟩
  decide +kernel

theorem store_place_odd (rom : WordROM) : accepts rom #v[131071,65280,0,55] := by
  apply (native_lookup_store_place rom #v[131071,65280,0]).mpr
  refine ⟨⟨131071, by decide⟩, ?_⟩
  decide +kernel

theorem wrong_offset_rejected (rom : WordROM) : ¬ accepts rom #v[589825,0,5,44] := by
  intro member
  exact Airbender.Tests.SubwordOffset.wrong_offset_rejected ((native_lookup_offset rom #v[589825,0,5]).mp member)

theorem wrong_trap_rejected (rom : WordROM) : ¬ accepts rom #v[589825,1,1,44] := by
  intro member
  exact Airbender.Tests.SubwordOffset.wrong_trap_rejected ((native_lookup_offset rom #v[589825,1,1]).mp member)

theorem wrong_load_low_rejected (rom : WordROM) : ¬ accepts rom #v[128,1,65535,45] := by
  intro member
  exact Airbender.Tests.SubwordLoad.wrong_low_rejected ((native_lookup_load rom #v[128,1,65535]).mp member)

theorem wrong_load_high_rejected (rom : WordROM) : ¬ accepts rom #v[128,65408,0,45] := by
  intro member
  exact Airbender.Tests.SubwordLoad.wrong_high_rejected ((native_lookup_load rom #v[128,65408,0]).mp member)

theorem wrong_clear_rejected (rom : WordROM) : ¬ accepts rom #v[65535,0,0,54] := by
  intro member
  exact Airbender.Tests.SubwordStoreClear.wrong_cleared_rejected ((native_lookup_store_clear rom #v[65535,0,0]).mp member)

theorem wrong_clear_unused_rejected (rom : WordROM) : ¬ accepts rom #v[170,0,1,54] := by
  intro member
  exact Airbender.Tests.SubwordStoreClear.wrong_unused_rejected ((native_lookup_store_clear rom #v[170,0,1]).mp member)

theorem wrong_place_rejected (rom : WordROM) : ¬ accepts rom #v[131071,255,0,55] := by
  intro member
  exact Airbender.Tests.SubwordStorePlace.wrong_placed_rejected ((native_lookup_store_place rom #v[131071,255,0]).mp member)

theorem wrong_place_unused_rejected (rom : WordROM) : ¬ accepts rom #v[170,170,1,55] := by
  intro member
  exact Airbender.Tests.SubwordStorePlace.wrong_unused_rejected ((native_lookup_store_place rom #v[170,170,1]).mp member)

/-- A valid clearing row cannot pass under the written-value placement tag. -/
theorem crossed_store_regions_rejected (rom : WordROM) : ¬ accepts rom #v[65535,65280,0,55] := by
  intro member
  have values := SubwordStorePlace.native_values
    ((native_lookup_store_place rom #v[65535,65280,0]).mp member)
  have wrong := values.2.1
  change (65280 : ZMod mersenne31Modulus) = 255 at wrong
  exact (by decide +kernel : (65280 : ZMod mersenne31Modulus) ≠ 255) wrong

theorem aligned_rom_member : accepts Tests.SubwordArtifact.rom #v[1,1,32767,46] :=
  (native_lookup_rom _ _).mpr Tests.SubwordArtifact.aligned_query_member

theorem byte_key_rejected : ¬ accepts Tests.SubwordArtifact.rom #v[4,1,32767,46] := by
  intro member
  exact Tests.SubwordArtifact.aligned_wrong_byte_key_rejected ((native_lookup_rom _ _).mp member)

theorem changed_rom_output_rejected : ¬ accepts Tests.SubwordArtifact.rom #v[1,2,32767,46] := by
  intro member
  exact Tests.SubwordArtifact.aligned_changed_output_rejected ((native_lookup_rom _ _).mp member)

theorem aligned_rom_tail : accepts Tests.SubwordArtifact.rom #v[1048575,4211,49152,46] := by
  apply (native_lookup_rom Tests.SubwordArtifact.rom #v[1048575,4211,49152]).mpr
  refine ⟨⟨1048575,by decide⟩,?_⟩
  decide +kernel

/-- Bounds apply to the field's canonical selector, retaining native field encoding. -/
theorem canonical_field_selector (rom : WordROM) :
    accepts rom #v[128,65408,65535,((mersenne31Modulus + 45 : Nat) : ZMod mersenne31Modulus)] := by
  have tag : ((mersenne31Modulus + 45 : Nat) : ZMod mersenne31Modulus) = 45 := by simp
  rw [tag]
  exact load_signed_byte rom

end Tests.SubwordLookups
