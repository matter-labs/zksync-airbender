import Airbender.Proofs.Tables.ShiftPrefixRows
import Airbender.Proofs.Tables.ImportedBinaryRows
import Airbender.Proofs.Tables.ImportedShiftRows
import Airbender.Proofs.Tables.SignColumns
import Airbender.Review.Helpers.Tables.Bytes

namespace Airbender.Verification
open Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/- Compose opaque region functions before instantiating imported columns. This
   prevents conditional normalization from traversing the complete data arrays. -/
private def assembled (zero sign xor or and truncate shift : Nat → Vector Nat 10)
    (n : Nat) : Vector Nat 10 :=
  if n < 1 then zero n
  else if n < 257 then sign (n - 1)
  else if n < 65793 then xor (n - 257)
  else if n < 131329 then or (n - 65793)
  else if n < 196865 then and (n - 131329)
  else if n < 262401 then truncate (n - 196865)
  else shift (n - 262401)

private theorem assembled_congr
    (zero sign xor or and truncate shift zero' sign' xor' or' and' truncate' shift' :
      Nat → Vector Nat 10)
    (hzero : ∀ n, n < 1 → zero n = zero' n)
    (hsign : ∀ n, n < 256 → sign n = sign' n)
    (hxor : ∀ n, n < 65536 → xor n = xor' n)
    (hor : ∀ n, n < 65536 → or n = or' n)
    (hand : ∀ n, n < 65536 → and n = and' n)
    (htruncate : ∀ n, n < 65536 → truncate n = truncate' n)
    (hshift : ∀ n, n < 262144 → shift n = shift' n)
    (n : Nat) (bound : n < 524545) :
    assembled zero sign xor or and truncate shift n =
      assembled zero' sign' xor' or' and' truncate' shift' n := by
  unfold assembled
  split_ifs with h0 h1 h2 h3 h4 h5
  · exact hzero n h0
  · exact hsign (n - 1) (by omega)
  · exact hxor (n - 257) (by omega)
  · exact hor (n - 65793) (by omega)
  · exact hand (n - 131329) (by omega)
  · exact htruncate (n - 196865) (by omega)
  · exact hshift (n - 262401) (by omega)

private def zeroReference (_ : Nat) : Vector Nat 10 := #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
private def signReference (n : Nat) : Vector Nat 10 :=
  #v[n, if n < 128 then 0 else 255, 0, 0, 0, 0, 0, 0, 0, 3]
private def truncateReference (n : Nat) : Vector Nat 10 :=
  let (a, b) := ByteUtils.splitTwoBytes ⟨n % 65536, Nat.mod_lt _ (by decide)⟩
  #v[a.val, b.val, a.val % 32, 0, 0, 0, 0, 0, 0, 8]
private def shiftReference (n : Nat) : Vector Nat 10 :=
  let out := (shiftByteContribution (n / 65536) (n / 256 % 256)
    (n / 8 % 32) (n % 8)).toNat
  #v[n / 65536, n / 256 % 256, n / 8 % 32, n % 8,
    out % 256, out / 256 % 256, out / 65536 % 256, out / 16777216 % 256, 0, 9]

private theorem zero_region (n : Nat) (bound : n < 1) :
    shiftRegionRow 0 n = zeroReference n := by
  have equal : n = 0 := by omega
  subst n
  exact ShiftPrefix.zero_row
private theorem sign_region (n : Nat) (bound : n < 256) :
    shiftRegionRow 1 n = signReference n := ShiftPrefix.sign_row n bound
private theorem xor_region (n : Nat) (bound : n < 65536) :
    shiftRegionRow ⟨2, by decide⟩ n = binaryByteRow 4 n := by
  simp only [shiftRegionRow, shiftData, Vector.getElem_mk, Fin.getElem_fin,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  exact BinaryColumns.xor_row n bound
private theorem or_region (n : Nat) (bound : n < 65536) :
    shiftRegionRow ⟨3, by decide⟩ n = binaryByteRow 6 n := by
  simp only [shiftRegionRow, shiftData, Vector.getElem_mk, Fin.getElem_fin,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  exact BinaryColumns.or_row n bound
private theorem and_region (n : Nat) (bound : n < 65536) :
    shiftRegionRow ⟨4, by decide⟩ n = binaryByteRow 7 n := by
  simp only [shiftRegionRow, shiftData, Vector.getElem_mk, Fin.getElem_fin,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  exact BinaryColumns.and_row n bound
private theorem truncate_region (n : Nat) (bound : n < 65536) :
    shiftRegionRow 5 n = truncateReference n := by
  have first : n % 65536 = n := Nat.mod_eq_of_lt bound
  simp only [shiftRegionRow, shiftData, Vector.getElem_mk, Fin.getElem_fin,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
    show (5 : Fin 7).val = 5 from rfl]
  simpa only [truncateReference, ByteUtils.splitTwoBytes, first] using
    BinaryColumns.truncation_row n bound
private theorem shift_region (n : Nat) (bound : n < 262144) :
    shiftRegionRow 6 n = shiftReference n := ShiftColumns.row n bound

private theorem imported_assembly (index : Fin 524545) :
    shiftBinopRow index = assembled (shiftRegionRow 0) (shiftRegionRow 1)
      (shiftRegionRow 2) (shiftRegionRow 3) (shiftRegionRow 4)
      (shiftRegionRow 5) (shiftRegionRow 6) index.val := by rfl

private theorem reference_assembly (index : Fin 524545) :
    assembled zeroReference signReference (binaryByteRow 4) (binaryByteRow 6)
      (binaryByteRow 7) truncateReference shiftReference index.val =
        referenceShiftBinopRow index := by
  unfold assembled referenceShiftBinopRow referenceShiftNatRow
  by_cases zero : index.val = 0
  · simp only [zero, Nat.reduceLT, if_true, zeroReference]
  · have not_first : ¬index.val < 1 := by omega
    simp only [not_first, if_false, zero]
    rfl

/-- Imported native rows represent the original full-domain mathematical relation. -/
theorem shiftBinopRow_eq_reference (index : Fin 524545) :
    shiftBinopRow index = referenceShiftBinopRow index := by
  exact (imported_assembly index).trans
    ((assembled_congr _ _ _ _ _ _ _ _ _ _ _ _ _ _ zero_region sign_region
      xor_region or_region and_region truncate_region shift_region index.val index.isLt).trans
        (reference_assembly index))

end Airbender.Verification
