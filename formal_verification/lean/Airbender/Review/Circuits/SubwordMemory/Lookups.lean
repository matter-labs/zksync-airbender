import Airbender.Proofs.SubwordMemory.NativeQueries

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

end Airbender.SubwordMemory
