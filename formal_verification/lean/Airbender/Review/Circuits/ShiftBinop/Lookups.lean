import Airbender.Proofs.ShiftBinop.NativeResolution
import Airbender.Proofs.ShiftBinop.NativeQueries

namespace Airbender.ShiftBinop
open Verification
set_option autoImplicit false

/-- All four queries and witness selectors are extracted from native constraints. -/
theorem native_lookup_queries {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (slot : Fin 4) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[]
      #v[w (39 + 4 * slot.val), w (40 + 4 * slot.val),
         w (41 + 4 * slot.val), w (42 + 4 * slot.val)] :=
  NativeLookupProofs.native_queries holds slot

theorem native_lookup_selectors {w : Nat → ZMod mersenne31Modulus}
    (holds : FlatOperation.ConstraintsHoldFlat (environment w) importedConstraints)
    (slot : Fin 4) :
    (w (42 + 4 * slot.val)).val ∈ [0, 4, 6, 7, 25, 47, 48, 49, 50, 51, 52, 53] :=
  NativeLookupProofs.native_selectors holds slot

/-- Accepted native queries retain an actual stored selector, including zero and CSR. -/
theorem native_lookup_selector (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] query) :
    query[3].val = 0 ∨ query[3].val = 4 ∨ query[3].val = 6 ∨ query[3].val = 7 ∨
      query[3].val = 25 ∨ query[3].val = 47 ∨ query[3].val = 48 ∨ query[3].val = 49 ∨
      query[3].val = 50 ∨ query[3].val = 51 ∨ query[3].val = 52 ∨ query[3].val = 53 :=
  NativeLookupProofs.accepted_selector query member

/-- The native selector resolves exact byte-table membership; no equivalence premise. -/
theorem native_lookup_binary (kind : BinaryKind) (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] (query.push kind.tag) ↔
      NativeBinary.Contains kind query :=
  NativeLookupProofs.binary_membership kind query

theorem native_lookup_scalar (kind : ShiftScalarKind) (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] (query.push kind.tag) ↔
      NativeShiftScalars.Contains kind query :=
  NativeLookupProofs.scalar_membership kind query

theorem native_lookup_sll_low (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] (query.push 48) ↔
      NativeSllLow.Contains query :=
  NativeLookupProofs.sll_low_membership query

theorem native_lookup_sll_high (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] (query.push 49) ↔
      NativeSllHigh.Contains query :=
  NativeLookupProofs.sll_high_membership query

theorem native_lookup_srl_low (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] (query.push 50) ↔
      NativeSrlLow.Contains query :=
  NativeLookupProofs.srl_low_membership query

theorem native_lookup_srl_high (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] (query.push 51) ↔
      NativeSrlHigh.Contains query :=
  NativeLookupProofs.srl_high_membership query

/-- Disabling a lookup requires the actual all-zero row. -/
theorem native_lookup_zero (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] (query.push 0) ↔
      query = #v[0, 0, 0] :=
  NativeLookupProofs.zero_membership query

/-- Only the exported compilation CSR profile; runtime CSR setup remains separate. -/
theorem native_lookup_compilation_csr (query : Vector (ZMod mersenne31Modulus) 3) :
    (NativeShiftLookup.table (p := mersenne31Modulus)).Contains #[] (query.push 25) ↔
      ∃ i : Fin NativeShiftCsr.data.length,
        query.push (25 : ZMod mersenne31Modulus) = NativeShiftCsr.data.row i :=
  NativeLookupProofs.compilation_csr_membership query

end Airbender.ShiftBinop
