import Airbender.Proofs.ReducedMachine.NativeBitwiseData
import Airbender.Proofs.ReducedMachine.NativePool
import Airbender.Review.Helpers.Tables.NativeBinary

namespace Airbender.ReducedMachine.NativeBitwiseTableProofs
open NativeFixed Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

/-- Actual full-pool selection transports to the unchanged certified byte
    relation only after exact native literal identities, never an assumption. -/
theorem membership (kind : BinaryKind) (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query)
    (selected : query[3] = (kind.tag : ZMod mersenne31Modulus)) :
    NativeBinary.Contains kind #v[query[0],query[1],query[2]] := by
  have reconstruct : (#v[query[0],query[1],query[2]]).push (kind.tag : ZMod mersenne31Modulus) = query := by
    ext lane bound
    interval_cases lane <;> simp [selected]
  cases kind
  · obtain ⟨i,same⟩ := NativePoolProofs.selected_region query member .xor selected
    change query = dataT4.row i at same
    have rows := congrArg (fun data : Setup.TableData 4 =>
      (data.columns.map (fun column => (column.get? i.val).getD 0)).map
        (fun n : Nat => (n : ZMod mersenne31Modulus))) NativeBitwiseDataProofs.xor_data
    exact ⟨i,reconstruct.trans (same.trans rows)⟩
  · obtain ⟨i,same⟩ := NativePoolProofs.selected_region query member .or selected
    change query = dataT6.row i at same
    have rows := congrArg (fun data : Setup.TableData 4 =>
      (data.columns.map (fun column => (column.get? i.val).getD 0)).map
        (fun n : Nat => (n : ZMod mersenne31Modulus))) NativeBitwiseDataProofs.or_data
    exact ⟨i,reconstruct.trans (same.trans rows)⟩
  · obtain ⟨i,same⟩ := NativePoolProofs.selected_region query member .and selected
    change query = dataT7.row i at same
    have rows := congrArg (fun data : Setup.TableData 4 =>
      (data.columns.map (fun column => (column.get? i.val).getD 0)).map
        (fun n : Nat => (n : ZMod mersenne31Modulus))) NativeBitwiseDataProofs.and_data
    exact ⟨i,reconstruct.trans (same.trans rows)⟩

/-- All actual byte keys/outputs are bounded and force the exact bitwise value. -/
theorem result (kind : BinaryKind) (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query)
    (selected : query[3] = (kind.tag : ZMod mersenne31Modulus)) :
    query[0].val < 256 ∧ query[1].val < 256 ∧ query[2].val < 256 ∧
      BitVec.ofNat 8 query[2].val = byteOperation kind.tag
        (BitVec.ofNat 8 query[0].val) (BitVec.ofNat 8 query[1].val) :=
  native_binary_result kind _ (membership kind query member selected)

end Airbender.ReducedMachine.NativeBitwiseTableProofs
