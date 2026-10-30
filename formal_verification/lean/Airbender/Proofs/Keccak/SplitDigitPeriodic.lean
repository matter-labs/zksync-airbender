import Airbender.Proofs.Keccak.SplitDigitColumns

namespace Airbender.Setup.Proofs
set_option warningAsError true

/-- Read a repeated native index view without expanding its stored array. -/
theorem column_periodic_ofFn_get {size : Nat} (repetitions : Nat) (positive : 0 < size)
    (values : Fin size → Nat) (rest : Array Block) (index : Fin (repetitions * size)) :
    (Column.mk (#[.periodic repetitions 0 (Vector.ofFn values).toArray] ++ rest)).get? index.val =
      some (values ⟨index.val % size, Nat.mod_lt _ positive⟩) := by
  simp [Column.get?, getFromBlocks, Block.get?, Block.length, index.isLt,
    Nat.mod_lt _ positive]

/-- One selected native digit is unchanged by the compact index view. -/
theorem digitIndex_singleton (position index : Nat) :
    digitIndex #[position] index = index / 16 ^ position % 16 := by
  simp [digitIndex]

/-- Three selected native digits retain their increasing-position order. -/
theorem digitIndex_three (one two three index : Nat) :
    digitIndex #[one, two, three] index = index / 16 ^ one % 16 +
      16 * (index / 16 ^ two % 16) + 256 * (index / 16 ^ three % 16) := by
  simp [digitIndex]
  omega

end Airbender.Setup.Proofs
