import Airbender.Proofs.Tables.ReferenceControl
import Airbender.Review.Helpers.Tables.PairData
import Airbender.Proofs.Tables.AlignedConstants
import Airbender.Review.Circuits.JumpBranchSlt.Tables.Control

namespace Airbender.Verification.ImportedControl
open Setup Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768

private theorem conditional_aligned :
    AlignedConstants conditionalData.columns[1].blocks.toList := by decide +kernel

private theorem conditional_samples : ∀ q : Fin 128,
    conditionalData.columns[1].get? (q.val * 32768) =
      some (conditionalValue (q.val * 32768)) := by decide +kernel

private theorem conditional_coarse (n : Nat) :
    conditionalValue n = conditionalValue (n / 32768 * 32768) := by
  generalize hm : n / 32768 * 32768 = m
  have a : n / 32768 = m / 32768 := by omega
  have b : n / 65536 = m / 65536 := by omega
  have c : n / 131072 = m / 131072 := by omega
  have d : n / 262144 = m / 262144 := by omega
  have e : n / 524288 = m / 524288 := by omega
  simp only [conditionalValue, a, b, c, d, e]

private theorem conditional_value (i : Fin 4194304) :
    conditionalData.columns[1].get? i.val = some (conditionalValue i.val) := by
  have bound := i.isLt
  have aligned := alignedConstants_get conditionalData.columns[1].blocks.toList
    conditional_aligned i.val
  have sampled := conditional_samples ⟨i.val / 32768, by omega⟩
  change getFromBlocks conditionalData.columns[1].blocks.toList i.val = _
  rw [aligned]
  exact sampled.trans (congrArg some (conditional_coarse i.val).symm)

/-- Every native key, including invalid combinations, retains its actual
    conditional-resolution value; the check covers all 4,194,304 rows. -/
theorem conditional_row (i : Fin 4194304) :
    setupPairRow conditionalData (by decide) i = (i.val, conditionalValue i.val) := by
  have key : conditionalData.columns[0].get? i.val = some i.val := by
    change getFromBlocks [.affine 4194304 0 1] i.val = some i.val
    simp [getFromBlocks, Block.get?, Block.length, i.isLt]
  simp only [setupPairRow, show conditionalData.offset = 0 from rfl, Nat.zero_add,
    key, conditional_value i, Option.getD_some]

end Airbender.Verification.ImportedControl
