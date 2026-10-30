import Airbender.Import.SetupEmbed

namespace Airbender.Setup.Proofs
set_option warningAsError true

/-- Read a dense index view without expanding its complete stored array. -/
theorem dense_ofFn_get {size : Nat} (values : Fin size → Nat) (index : Fin size) :
    (Block.dense (Vector.ofFn values).toArray).get? index.val = some (values index) := by
  simp [Block.get?, Block.length, index.isLt]

/-- A following native region does not affect reads within the dense prefix. -/
theorem column_dense_ofFn_get {size : Nat} (values : Fin size → Nat)
    (rest : Array Block) (index : Fin size) :
    (Column.mk (#[.dense (Vector.ofFn values).toArray] ++ rest)).get? index.val =
      some (values index) := by
  simp [Column.get?, getFromBlocks, Block.get?, Block.length, index.isLt]

end Airbender.Setup.Proofs
