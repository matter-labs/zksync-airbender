import Airbender.Proofs.Tables.PeriodicColumns

namespace Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false

def constantBlock (expected : Nat) : Block → Bool
  | .affine _ first step => first == expected && step == 0
  | .dense values => values.all (· == expected)
  | .periodic _ step values => step == 0 && values.all (· == expected)

private theorem constantBlock_sound (expected : Nat) (block : Block) (checked : constantBlock expected block = true)
    (n : Nat) (bound : n < block.length) : block.get? n = some expected := by
  cases block with
  | affine length first step =>
    simp only [constantBlock, Bool.and_eq_true, beq_iff_eq] at checked
    obtain ⟨rfl, rfl⟩ := checked
    simp [Block.get?, bound]
  | dense values =>
    have sample := Array.all_eq_true.mp checked n bound
    simp only [beq_iff_eq] at sample
    simp only [Block.get?, if_pos bound, Array.getElem?_eq_getElem bound, sample]
  | periodic count step values =>
    simp only [constantBlock, Bool.and_eq_true, beq_iff_eq] at checked
    obtain ⟨rfl, checked⟩ := checked
    have positive : 0 < values.size := by
      simp only [Block.length] at bound
      by_contra h
      have : values.size = 0 := by omega
      simp [this] at bound
    have hm : n % values.size < values.size := Nat.mod_lt _ positive
    have sample := Array.all_eq_true.mp checked (n % values.size) hm
    simp only [beq_iff_eq] at sample
    simp [Block.get?, bound, hm, sample]

/-- Skip the prefix by its actual block lengths; every remaining block must
    contain only the stored constant value. This checks huge tails structurally. -/
def constantTail (expected : Nat) : Nat → List Block → Bool
  | _, [] => true
  | cutoff, block :: rest =>
    if block.length ≤ cutoff then constantTail expected (cutoff - block.length) rest
    else constantBlock expected block && constantTail expected 0 rest

theorem constantTail_sound (expected cutoff : Nat) (blocks : List Block) (checked : constantTail expected cutoff blocks = true)
    (n : Nat) (lower : cutoff ≤ n) (bound : n < (blocks.map Block.length).sum) :
    getFromBlocks blocks n = some expected := by
  induction blocks generalizing cutoff n with
  | nil => simp at bound
  | cons block rest ih =>
    simp only [List.map_cons, List.sum_cons] at bound
    by_cases skipped : block.length ≤ cutoff
    · have next : constantTail expected (cutoff - block.length) rest = true := by
        simpa only [constantTail, if_pos skipped] using checked
      rw [getFromBlocks, if_neg (by omega)]
      exact ih _ next _ (by omega) (by omega)
    · have next : constantBlock expected block = true ∧ constantTail expected 0 rest = true := by
        simpa only [constantTail, if_neg skipped, Bool.and_eq_true] using checked
      rw [getFromBlocks]
      split
      · exact constantBlock_sound expected block next.1 n (by assumption)
      · exact ih 0 next.2 _ (by omega) (by omega)

end Airbender.Setup.Proofs
