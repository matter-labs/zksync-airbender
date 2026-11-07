import Airbender.Proofs.ReducedMachine.NativePool
import Airbender.Review.Circuits.JumpBranchSlt.Tables.Control
import Airbender.Proofs.Tables.PeriodicColumns
import Mathlib.Tactic.IntervalCases

namespace Airbender.ReducedMachine.NativeBranchCleanupProofs
open NativeFixed Setup Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

-- Copied unchanged from the checked v2 scalar certificate.
private theorem affine_get (length first step n : Nat) (bound : n < length) :
    Block.get? (.affine length first (step : Int)) n = some (first + step * n) := by
  simp only [Block.get?, Block.length, if_pos bound]
  have casts : (first : Int) + (step : Int) * n = ((first + step * n : Nat) : Int) := by simp
  rw [casts, if_pos (Int.natCast_nonneg _), Int.toNat_natCast]

private theorem single_get (block : Block) (n : Nat) (bound : n < block.length) :
    (⟨#[block]⟩ : Column).get? n = block.get? n := by
  change getFromBlocks [block] n = _
  rw [getFromBlocks, if_pos bound]

/-- Every exported native cleanup value, including its table ID. The 65k domain
    is symbolic: only the four stored periodic template entries are inspected. -/
theorem rows (i : Fin 65536) :
    dataT17.rowNat i = (jumpCleanupRow i).push 17 := by
  have key : dataT17.columns[0].get? i.val = some i.val := by
    change (⟨#[.affine 65536 0 1]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 65536 0 1 i.val i.isLt
  have bit : dataT17.columns[1].get? i.val = some (i.val / 2 % 2) := by
    change (⟨#[.periodic 16384 0 #[0, 0, 1, 1]]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    have read := Setup.Proofs.periodic_get #[0, 0, 1, 1] 16384 0 i.val (by decide) i.isLt
    change Block.get? (.periodic 16384 0 #[0, 0, 1, 1]) i.val = _ at read
    rw [read]
    simp only [Nat.zero_mul, Nat.add_zero]
    have cases : i.val % 4 = 0 ∨ i.val % 4 = 1 ∨ i.val % 4 = 2 ∨ i.val % 4 = 3 := by omega
    rcases cases with h | h | h | h <;> simp [h] <;> omega
  have cleaned : dataT17.columns[2].get? i.val = some (4 * (i.val / 4)) := by
    change (⟨#[.periodic 16384 4 (Array.replicate 4 0)]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    have read := Setup.Proofs.periodic_get (Array.replicate 4 0) 16384 4 i.val (by decide) i.isLt
    change Block.get? (.periodic 16384 4 (Array.replicate 4 0)) i.val = _ at read
    rw [read]
    simp
  have tag : dataT17.columns[3].get? i.val = some 17 := by
    change (⟨#[.affine 65536 17 0]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 65536 17 0 i.val i.isLt
  apply Vector.ext
  intro lane bound
  interval_cases lane <;> simp [TableData.rowNat, key, bit, cleaned, tag, jumpCleanupRow]


/-- Exact semantics of the actual tag17 region in the complete native pool. -/
theorem values {key bit cleaned : ZMod mersenne31Modulus}
    (member : (table (p := mersenne31Modulus)).Contains #[] #v[key,bit,cleaned,17]) :
    key.val < 65536 ∧ bit = (key.val / 2 % 2 : Nat) ∧
      cleaned = (4*(key.val / 4) : Nat) := by
  obtain ⟨i,same⟩ := NativePoolProofs.selected_region _ member .cleanup rfl
  change #v[key,bit,cleaned,17] = dataT17.row i at same
  have actual : #v[key,bit,cleaned,17] = ((jumpCleanupRow i).push 17).map Nat.cast := by
    simpa only [TableData.row,rows] using same
  have head : key = (i.val : ZMod mersenne31Modulus) := by
    simpa [jumpCleanupRow] using congrArg (fun q : Vector (ZMod mersenne31Modulus) 4 => q[0]) actual
  have canonical : key.val = i.val := by
    rw [head,ZMod.val_natCast_of_lt (lt_trans i.isLt (by decide))]
  refine ⟨by rw [canonical]; exact i.isLt,?_,?_⟩
  · rw [canonical]
    simpa [jumpCleanupRow] using congrArg (fun q : Vector (ZMod mersenne31Modulus) 4 => q[1]) actual
  · rw [canonical]
    simpa [jumpCleanupRow] using congrArg (fun q : Vector (ZMod mersenne31Modulus) 4 => q[2]) actual

end Airbender.ReducedMachine.NativeBranchCleanupProofs
