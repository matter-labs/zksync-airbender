import Airbender.Proofs.SubwordMemory.StoreBounds

namespace Tests.SubwordPackedBounds
open Airbender Verification SubwordMemory
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- The largest valid native fields reach exactly the last 21-bit key. -/
theorem full_key_boundary :
    (65535 + 65536 * 3 + 262144 * 7 : Nat) = 2097151 ∧
    (2097151 : Nat) % 65536 = 65535 ∧ 2097151 / 65536 % 4 = 3 ∧
    2097151 / 262144 % 8 = 7 := by decide +kernel

theorem byte_merge_boundaries :
    SubwordStoreClear.cleared 65535 + SubwordStorePlace.placed 65535 = 65535 ∧
    SubwordStoreClear.cleared 131071 + SubwordStorePlace.placed 131071 = 65535 ∧
    SubwordStoreClear.cleared 262143 + SubwordStorePlace.placed 262143 = 65535 := by
  decide +kernel

/-- SH keeps the low source limb in the literal table, including odd offsets;
    native offset/trap acceptance, rather than table truncation, handles alignment. -/
theorem halfword_and_unused_keys :
    SubwordStoreClear.cleared 393215 = 0 ∧ SubwordStorePlace.placed 393215 = 65535 ∧
    SubwordStoreClear.cleared 2097151 = 0 ∧ SubwordStorePlace.placed 2097151 = 0 := by
  decide +kernel

/-- Separate contribution bounds alone cannot establish a bounded sum. -/
theorem separate_bounds_insufficient :
    (65535 : Nat) < 65536 ∧ 65535 + 65535 ≥ 65536 := by decide +kernel

/-- Raw funct3 bounds are essential to interpreting Mersenne31 packed fields.
    The integrated theorem derives them from actual original public decoding. -/
theorem field_wrap_requires_metadata :
    (262144 * (8192 : ZMod mersenne31Modulus)).val = 1 ∧ (8192 : Nat) ≥ 8 := by
  decide +kernel

end Tests.SubwordPackedBounds
