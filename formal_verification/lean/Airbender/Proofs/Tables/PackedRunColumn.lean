import Airbender.Proofs.Tables.PackedRunArithmetic

namespace Airbender.Setup.Proofs.PackedRunColumn
open PackedColumn PackedRun
set_option warningAsError true

def ofBlock : Block → Option Run
  | .affine count first (.ofNat stride) => some ⟨count, stride, #[first]⟩
  | .dense values => some ⟨1, 0, values⟩
  | .periodic count (.ofNat stride) values => some ⟨count, stride, values⟩
  | _ => none

theorem ofBlock_sound (block : Block) (data : Run) (encoded : ofBlock block = some data) :
    block.length = data.length ∧
      ∀ index, index < block.length → block.get? index = some (data.value index) := by
  cases block with
  | affine count first step =>
    cases step with
    | negSucc step => simp [ofBlock] at encoded
    | ofNat stride =>
      simp only [ofBlock, Option.some.injEq] at encoded
      subst data
      constructor
      · simp [Block.length, Run.length]
      · intro index within
        simp only [Block.length] at within
        simp only [Block.get?, Block.length, if_pos within]
        have natural : (first : Int) + Int.ofNat stride * index = ((first + stride * index : Nat) : Int) := by norm_cast
        simp only [natural, Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast]
        simp [Run.value, Nat.mod_one]
  | dense values =>
    simp only [ofBlock, Option.some.injEq] at encoded
    subst data
    constructor
    · simp [Block.length, Run.length]
    · intro index within
      simp only [Block.length] at within
      simp [Block.get?, Block.length, within, Run.value, Nat.mod_eq_of_lt within]
  | periodic count step values =>
    cases step with
    | negSucc step => simp [ofBlock] at encoded
    | ofNat stride =>
      simp only [ofBlock, Option.some.injEq] at encoded
      subst data
      constructor
      · rfl
      · intro index within
        simp only [Block.length] at within
        simp only [Block.get?, Block.length, if_pos within]
        have natural : ((values[index % values.size]?.getD 0 : Nat) : Int) +
            Int.ofNat stride * ((index : Int) / values.size) =
            ((values[index % values.size]?.getD 0 + stride * (index / values.size) : Nat) : Int) := by norm_cast
        simp only [natural, Int.natCast_nonneg, ↓reduceIte, Int.toNat_natCast]
        simp [Run.value]


end Airbender.Setup.Proofs.PackedRunColumn
