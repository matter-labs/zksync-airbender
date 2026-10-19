import Airbender.Review.Helpers.Tables.NativeBinaryRows
import Airbender.Proofs.Tables.BinaryXorCertificate
import Airbender.Proofs.Tables.BinaryOrCertificate
import Airbender.Proofs.Tables.BinaryAndCertificate
import Airbender.Proofs.Tables.BinaryColumns
import Mathlib.Tactic.IntervalCases
import Airbender.Proofs.Mersenne31

namespace Airbender.Verification.BinaryProofs
open Setup Setup.Proofs NativeBinary
set_option warningAsError true
set_option Elab.async false

private theorem checks (kind : BinaryKind) :
    checkBlocks (fun n => kind.apply (n / 256) (n % 256)) 0
      (columns kind)[2].blocks.toList = true := by
  cases kind
  · exact BinaryCertificate.xor_outputs
  · exact BinaryCertificate.or_outputs
  · exact BinaryCertificate.and_outputs

private theorem output_get (kind : BinaryKind) (i : Fin 65536) :
    (columns kind)[2].get? i.val = some (kind.apply (i.val / 256) (i.val % 256)) := by
  have result := checkBlocks_sound _ _ 0 i.val (checks kind) (by rw [coverage]; exact i.isLt)
  simpa only [Column.get?,Nat.zero_add] using result

/-- Every actual native binary row, including all tags, without equivalence premises. -/
theorem native_rows (kind : BinaryKind) (i : Fin 65536) :
    row kind i = (binaryRow kind i).push kind.tag := by
  ext lane bound
  interval_cases lane <;>
    simp [row,binaryRow,first,second,output_get,tagged]

/-- The native conditional zero row is retained literally. -/
theorem native_zero : dataZero.rowNat ⟨0,by decide⟩ = #v[0,0,0,0] := by decide +kernel

/-- Exact native exported row membership agrees with original Clean semantics. -/
theorem native_membership (kind : BinaryKind) (query : Vector (ZMod mersenne31Modulus) 3) :
    (binaryTable kind).Contains #[] query ↔ Contains kind query := by
  change (∃ i : Fin 65536, query = (binaryRow kind i).map Nat.cast) ↔ _
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨i,by simp [native_rows,Vector.map_push]⟩
  · rintro ⟨i,same⟩
    refine ⟨i,?_⟩
    ext lane bound
    have selected := congrArg (fun v : Vector (ZMod mersenne31Modulus) 4 => v[lane]) same
    simpa [native_rows,Vector.map_push,Vector.getElem_push,bound] using selected

/-- Native byte keys and exact bitwise result follow from actual row membership. -/
theorem native_result (kind : BinaryKind) (query : Vector (ZMod mersenne31Modulus) 3)
    (member : Contains kind query) :
    query[0].val < 256 ∧ query[1].val < 256 ∧ query[2].val < 256 ∧
      BitVec.ofNat 8 query[2].val = byteOperation kind.tag
        (BitVec.ofNat 8 query[0].val) (BitVec.ofNat 8 query[1].val) := by
  have clean : ∃ i : Fin 65536, query = (binaryRow kind i).map Nat.cast :=
    (native_membership kind query).mpr member
  obtain ⟨i,same⟩ := clean
  have left : i.val / 256 < 256 := by have := i.isLt; omega
  have right : i.val % 256 < 256 := Nat.mod_lt _ (by decide)
  have result : kind.apply (i.val / 256) (i.val % 256) =
      (byteOperation kind.tag (BitVec.ofNat 8 (i.val / 256))
        (BitVec.ofNat 8 (i.val % 256))).toNat := by
    cases kind <;> simp [BinaryKind.apply,BinaryKind.tag,byteOperation,
      Nat.mod_eq_of_lt left,Nat.mod_eq_of_lt right]
  have small : kind.apply (i.val / 256) (i.val % 256) < 256 := by rw [result]; exact BitVec.isLt _
  have canonical (n : Nat) (bound : n < 256) : (n : ZMod mersenne31Modulus).val = n := by
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt (by change n < 2147483647; omega)]
  subst query
  simp only [binaryRow,Vector.getElem_map,Vector.getElem_mk,List.getElem_toArray,
    List.getElem_cons_zero,List.getElem_cons_succ,canonical _ left,canonical _ right,canonical _ small]
  exact ⟨left,right,small,by rw [result]; simp⟩

end Airbender.Verification.BinaryProofs
