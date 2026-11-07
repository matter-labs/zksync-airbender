import Airbender.Import.SetupEmbed

namespace Airbender.Setup.Proofs
set_option warningAsError true

/-- Structural certificate over stored constant blocks, with chunk-aligned
    boundaries. No expansion of a table's rows is needed. -/
def AlignedConstants : List Block → Prop
  | [] => True
  | .affine length _ stride :: tail =>
      stride = 0 ∧ length % 32768 = 0 ∧ AlignedConstants tail
  | _ => False

instance (blocks : List Block) : Decidable (AlignedConstants blocks) := by
  induction blocks with
  | nil => exact isTrue True.intro
  | cons block tail ih =>
    letI := ih
    cases block <;> dsimp only [AlignedConstants] <;> infer_instance

/-- Every key in a 32,768-key chunk reads the same actual imported constant. -/
theorem alignedConstants_get (blocks : List Block) (valid : AlignedConstants blocks)
    (n : Nat) : getFromBlocks blocks n = getFromBlocks blocks (n / 32768 * 32768) := by
  induction blocks generalizing n with
  | nil => rfl
  | cons block tail ih =>
    cases block with
    | dense _ => simp [AlignedConstants] at valid
    | periodic _ _ _ => simp [AlignedConstants] at valid
    | affine length first stride =>
      obtain ⟨rfl, aligned, rest⟩ := valid
      by_cases inside : n < length
      · have sampled : n / 32768 * 32768 < length := by omega
        simp [getFromBlocks, Block.get?, Block.length, inside, sampled]
      · have sampled : ¬ n / 32768 * 32768 < length := by omega
        have sub : n / 32768 * 32768 - length =
            (n - length) / 32768 * 32768 := by omega
        simp only [getFromBlocks, Block.length, if_neg inside, if_neg sampled, sub]
        exact ih rest (n - length)

end Airbender.Setup.Proofs
