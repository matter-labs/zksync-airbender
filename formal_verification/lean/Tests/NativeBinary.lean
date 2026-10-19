import Airbender.Review.Helpers.Tables.NativeBinary

namespace Tests.NativeBinary
open Airbender Verification

/-- Every actual native row, not just selected examples, has checked semantics. -/
theorem all_rows (kind : BinaryKind) (i : Fin 65536) :
    NativeBinary.row kind i = (binaryRow kind i).push kind.tag := BinaryProofs.native_rows kind i

theorem zero_row : NativeBinary.dataZero.rowNat ⟨0,by decide⟩ = #v[0,0,0,0] :=
  BinaryProofs.native_zero

theorem actual_offsets : NativeBinary.dataZero.nativeOffset = 0 ∧
    NativeBinary.dataXor.nativeOffset = 1 ∧ NativeBinary.dataOr.nativeOffset = 65537 ∧
    NativeBinary.dataAnd.nativeOffset = 131073 := by exact ⟨rfl,rfl,rfl,rfl⟩

theorem exact_membership (kind : BinaryKind) (query : Vector (ZMod mersenne31Modulus) 3) :
    (binaryTable kind).Contains #[] query ↔ NativeBinary.Contains kind query :=
  native_binary_membership kind query

theorem complementary (kind : BinaryKind) :
    NativeBinary.Contains kind #v[90,165,kind.apply 90 165] := by
  apply (native_binary_membership kind _).mp
  change ∃ i : Fin 65536, (#v[90,165,kind.apply 90 165] : Vector (ZMod mersenne31Modulus) 3) =
    (binaryRow kind i).map Nat.cast
  refine ⟨⟨23205,by decide⟩,?_⟩
  ext lane bound
  interval_cases lane <;> simp [binaryRow]

theorem last_row (kind : BinaryKind) : NativeBinary.row kind ⟨65535,by decide⟩ =
    #v[255,255,kind.apply 255 255,kind.tag] := by
  rw [BinaryProofs.native_rows]
  ext lane bound
  interval_cases lane <;> simp [binaryRow]

theorem bad_byte_rejected (kind : BinaryKind) :
    ¬ NativeBinary.Contains kind (#v[256,0,0] : Vector (ZMod mersenne31Modulus) 3) := by
  intro member
  have bound := (native_binary_result kind _ member).1
  have canonical : (((256 : Nat) : ZMod mersenne31Modulus).val) = 256 := by
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt (by decide)]
  change (((256 : Nat) : ZMod mersenne31Modulus).val) < 256 at bound
  rw [canonical] at bound
  exact (Nat.lt_irrefl 256) bound

theorem bad_result_rejected :
    ¬ NativeBinary.Contains .xor (#v[90,165,254] : Vector (ZMod mersenne31Modulus) 3) := by
  intro member
  have result := (native_binary_result .xor _ member).2.2.2
  have unequal : (254 : BitVec 8) ≠ byteOperation BinaryKind.xor.tag 90 165 := by decide +kernel
  exact unequal result

end Tests.NativeBinary
