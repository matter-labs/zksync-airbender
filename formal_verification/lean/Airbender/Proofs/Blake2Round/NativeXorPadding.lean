import Airbender.Proofs.Blake2Round.NativeXorKeyHelpers

namespace Airbender.Blake2Round.Proofs
open Airbender.Setup Airbender.Setup.Proofs NativeXorKeyHelpers
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

theorem plain_padding_get (kind : Fin 3) (j : Fin 2) (n : Nat)
    (hn : n < (xorData ⟨kind.val, by omega⟩).length) :
    (xorData ⟨kind.val, by omega⟩).columns[j.val + 3].get? n = some 0 := by
  have shape : (xorData ⟨kind.val, by omega⟩).columns[j.val + 3] =
      Column.mk #[.affine (xorData ⟨kind.val, by omega⟩).length 0 0] := by
    fin_cases kind <;> fin_cases j <;> rfl
  rw [shape]
  simp [Column.get?, getFromBlocks, Block.get?, Block.length, hn]

theorem carry_padding_get (kind : Fin 2) (n : Nat)
    (hn : n < (xorData (carryKind kind)).length) :
    (xorData (carryKind kind)).columns[4].get? n = some 0 := by
  have shape : (xorData (carryKind kind)).columns[4] =
      Column.mk #[.affine (xorData (carryKind kind)).length 0 0] := by
    fin_cases kind <;> rfl
  rw [shape]
  simp [Column.get?, getFromBlocks, Block.get?, Block.length, hn]

theorem native_tag_get (kind : Fin 6) (n : Nat) (hn : n < (xorData kind).length) :
    (xorData kind).columns[5].get? n = some (#v[4, 19, 20, 55, 56, 57][kind]) := by
  have shape : (xorData kind).columns[5] =
      Column.mk #[.affine (xorData kind).length (#v[4, 19, 20, 55, 56, 57][kind]) 0] := by
    fin_cases kind <;> rfl
  rw [shape]
  simp [Column.get?, getFromBlocks, Block.get?, Block.length, hn]

end Airbender.Blake2Round.Proofs
