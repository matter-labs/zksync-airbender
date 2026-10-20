import Airbender.Proofs.SubwordMemory.NativeQueries
import Airbender.Proofs.SubwordMemory.NativeResolution

namespace Airbender.SubwordMemory
open Verification
set_option autoImplicit false

/-- Native acceptance supplies both complete dynamic queries and their selectors.
    Operation-specific routing and initialized instruction execution are separate. -/
theorem native_lookup_queries {p : Nat} [Fact p.Prime] {rom : WordROM} {w : Nat → ZMod p}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (slot : Fin 2) :
    (NativeSubwordLookup.table rom).Contains #[]
      #v[w (52 + 4 * slot.val),w (53 + 4 * slot.val),
         w (54 + 4 * slot.val),w (55 + 4 * slot.val)] :=
  Proofs.native_queries holds slot

/-- Every accepted selector is canonical and belongs to one of the actual regions. -/
theorem native_lookup_selector (rom : WordROM) (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (NativeSubwordLookup.table rom).Contains #[] query) :
    query[3].val ∈ [0,23,44,45,46,54,55] :=
  NativeLookupProofs.accepted_selector rom query member

theorem native_lookup_selectors {rom : WordROM} {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) (importedConstraints rom))
    (slot : Fin 2) :
    (w (55 + 4 * slot.val)).val ∈ [0,23,44,45,46,54,55] :=
  Proofs.native_selectors holds slot

/-- Resolve the native tag with a proved equivalence, not an equivalence premise. -/
theorem native_lookup_zero (rom : WordROM) (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeSubwordLookup.table rom).Contains #[] (query.push 0) ↔
      query = #v[0,0,0] :=
  NativeLookupProofs.zero_membership rom query

/-- Resolve the native tag with a proved equivalence, not an equivalence premise. -/
theorem native_lookup_separator (rom : WordROM) (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeSubwordLookup.table rom).Contains #[] (query.push 23) ↔
      romSeparatorTable.Contains #[] query :=
  NativeLookupProofs.separator_membership rom query

/-- Resolve the native tag with a proved equivalence, not an equivalence premise. -/
theorem native_lookup_offset (rom : WordROM) (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeSubwordLookup.table rom).Contains #[] (query.push 44) ↔
      SubwordOffset.table.Contains #[] query :=
  NativeLookupProofs.offset_membership rom query

/-- Resolve the native tag with a proved equivalence, not an equivalence premise. -/
theorem native_lookup_load (rom : WordROM) (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeSubwordLookup.table rom).Contains #[] (query.push 45) ↔
      SubwordLoad.table.Contains #[] query :=
  NativeLookupProofs.load_membership rom query

/-- Resolve the native tag with a proved equivalence, not an equivalence premise. -/
theorem native_lookup_rom (rom : WordROM) (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeSubwordLookup.table rom).Contains #[] (query.push 46) ↔
      (romAlignedWordTable rom).Contains #[] query :=
  NativeLookupProofs.rom_membership rom query

/-- Resolve the native tag with a proved equivalence, not an equivalence premise. -/
theorem native_lookup_store_clear (rom : WordROM) (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeSubwordLookup.table rom).Contains #[] (query.push 54) ↔
      SubwordStoreClear.table.Contains #[] query :=
  NativeLookupProofs.store_clear_membership rom query

/-- Resolve the native tag with a proved equivalence, not an equivalence premise. -/
theorem native_lookup_store_place (rom : WordROM) (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeSubwordLookup.table rom).Contains #[] (query.push 55) ↔
      SubwordStorePlace.table.Contains #[] query :=
  NativeLookupProofs.store_place_membership rom query

end Airbender.SubwordMemory
