import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Review.Helpers.Decoder.NativeData

namespace Airbender.Trace.NativeDecoder.Proofs
open Airbender.Setup
set_option warningAsError true
set_option Elab.async false

/-- Read actual stored discriminators, without interpreting other leading fields. -/
def fixedTags : List Block → Bool
  | [] => true
  | .affine _ first step :: rest =>
      decide (first < 55 ∧ first ≠ 46 ∧ step = 0) && fixedTags rest
  | .dense values :: rest =>
      values.all (fun tag => decide (tag < 55 ∧ tag ≠ 46)) && fixedTags rest
  | _ => false

theorem fixedTags_sound (blocks : List Block) (checked : fixedTags blocks = true) (n : Nat) :
    (getFromBlocks blocks n).getD 0 < 55 ∧ (getFromBlocks blocks n).getD 0 ≠ 46 := by
  induction blocks generalizing n with
  | nil => simp [getFromBlocks]
  | cons block rest ih =>
    cases block with
    | dense values =>
      simp only [fixedTags, Bool.and_eq_true] at checked
      by_cases inside : n < values.size
      · have sampled := Array.all_eq_true.mp checked.1 n inside
        have bounds : values[n] < 55 ∧ values[n] ≠ 46 := of_decide_eq_true sampled
        simpa [getFromBlocks, Block.length, Block.get?, inside] using bounds
      · simpa only [getFromBlocks, Block.length, if_neg inside] using
          ih checked.2 (n - values.size)
    | periodic _ _ _ => simp [fixedTags] at checked
    | affine length first step =>
      simp only [fixedTags, Bool.and_eq_true, decide_eq_true_eq] at checked
      obtain ⟨⟨small, different, rfl⟩, tail⟩ := checked
      by_cases inside : n < length
      · simpa [getFromBlocks, Block.length, Block.get?, inside] using And.intro small different
      · simpa only [getFromBlocks, Block.length, if_neg inside] using ih tail (n - length)

theorem fixedTags_ne_decoder {p : Nat} [Fact p.Prime] (hp : FieldCapacity.NoWrap p 65536)
    (column : Column) (checked : fixedTags column.blocks.toList = true) (n : Nat) :
    (46 : ZMod p) ≠ (signedValue ((column.get? n).getD 0) : ZMod p) := by
  have actual := fixedTags_sound _ checked n
  change (column.get? n).getD 0 < 55 ∧ (column.get? n).getD 0 ≠ 46 at actual
  have lift : (column.get? n).getD 0 ≤ babyBearModulus / 2 := by
    change _ ≤ 1006632960
    omega
  rw [signedValue, if_pos lift]
  intro equal
  have values := congrArg ZMod.val equal
  simp only [Int.cast_natCast, ZMod.val_ofNat, ZMod.val_natCast] at values
  rw [Nat.mod_eq_of_lt (show 46 < p by omega),
    Nat.mod_eq_of_lt (show (column.get? n).getD 0 < p by omega)] at values
  exact actual.2 values.symm

/-- Exact imported tags exclude the entire fixed leading. This derives the
    decoder-region view from the complete-domain logical lookup contract. -/
theorem lookup_to_slice {p : Nat} [Fact p.Prime] (setup : PackedSetup)
    (query : Vector (ZMod p) 9)
    (leading : ∀ n, (46 : ZMod p) ≠
      (signedValue ((setup.prefixTags.get? n).getD 0) : ZMod p))
    (holds : setup.lookup query) : setup.table.Contains #[] (activeQuery query) := by
  obtain ⟨index, equal⟩ := holds
  split at equal
  · exact False.elim (leading index.val equal.2)
  · change ∃ position : Fin (setup.realRows.length + setup.padding.length),
      activeQuery query = (setup.row position).map (fun n => (signedValue n : ZMod p))
    exact ⟨⟨index.val - setup.offset, by have := index.isLt; omega⟩, equal⟩

end Airbender.Trace.NativeDecoder.Proofs
