import Airbender.Review.Circuits.ReducedMachine.Tables.RuntimeCSR
import Airbender.Proofs.Mersenne31
import Mathlib.Tactic.IntervalCases

namespace Airbender.ReducedMachine.NativeRuntimeCSRProofs
open NativeRuntimeCSR Setup
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

private theorem affine_get (length first step n : Nat) (bound : n < length) :
    Block.get? (.affine length first (step : Int)) n = some (first + step * n) := by
  simp only [Block.get?, Block.length, if_pos bound]
  have casts : (first : Int) + (step : Int) * n = ((first + step * n : Nat) : Int) := by simp
  rw [casts, if_pos (Int.natCast_nonneg _), Int.toNat_natCast]

private theorem single_get (block : Block) (n : Nat) (bound : n < block.length) :
    (⟨#[block]⟩ : Column).get? n = block.get? n := by
  change getFromBlocks [block] n = _
  rw [getFromBlocks, if_pos bound]


private theorem support_tail_bounds (n : Nat) (lower : 1992 ≤ n) (upper : n < 4096) :
    (¬ n-1984 < 1) ∧ (¬ n-1984-1 < 6) ∧ (¬ n-1984-1-6 < 1) ∧ n-1984-1-6-1 < 2104 := by omega

/-- Both complete stored output columns, including all unsupported keys. -/
theorem rows (i : Fin 4096) : data.rowNat i = row i.val := by
  have key : data.columns[0].get? i.val = some i.val := by
    change (⟨#[.affine 4096 0 1]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 4096 0 1 i.val i.isLt
  have support : data.columns[1].get? i.val = some (supported i.val) := by
    change getFromBlocks [.affine 1984 0 0,.dense #[1],.affine 6 0 0,.dense #[1],.affine 2104 0 0] i.val = _
    by_cases front : i.val < 1984
    · rw [getFromBlocks]
      simp only [Block.length,if_pos front]
      have meaning : supported i.val = 0 := by simp [supported]; omega
      simpa [meaning] using affine_get 1984 0 0 i.val front
    · by_cases middle : i.val < 1992
      · have cases : i.val=1984 ∨ i.val=1985 ∨ i.val=1986 ∨ i.val=1987 ∨ i.val=1988 ∨ i.val=1989 ∨ i.val=1990 ∨ i.val=1991 := by omega
        rcases cases with h | h | h | h | h | h | h | h
        all_goals simp [h,supported,getFromBlocks,Block.length,Block.get?]
      · obtain ⟨first,second,third,last⟩ := support_tail_bounds i.val (by omega) i.isLt
        simp only [getFromBlocks,Block.length,show (#[1] : Array Nat).size = 1 from rfl,
          if_neg front,if_neg first,if_neg second,if_neg third,if_pos last]
        have meaning : supported i.val = 0 := by simp [supported]; omega
        simpa [meaning] using affine_get 2104 0 0 (i.val-1984-1-6-1) last
  have delegate : data.columns[2].get? i.val = some (delegated i.val) := by
    change getFromBlocks [.affine 1991 0 0,.dense #[1],.affine 2104 0 0] i.val = _
    by_cases front : i.val < 1991
    · rw [getFromBlocks]
      simp only [Block.length,if_pos front]
      have meaning : delegated i.val = 0 := by simp [delegated]; omega
      simpa [meaning] using affine_get 1991 0 0 i.val front
    · by_cases equal : i.val = 1991
      · simp [equal,delegated,getFromBlocks,Block.length,Block.get?]
      · have next : ¬ i.val-1991 < 1 := by omega
        have last : i.val-1991-1 < 2104 := by have := i.isLt; omega
        simp only [getFromBlocks,Block.length,show (#[1] : Array Nat).size = 1 from rfl,
          if_neg front,if_neg next,if_pos last]
        have meaning : delegated i.val = 0 := by simp [delegated,equal]
        simpa [meaning] using affine_get 2104 0 0 (i.val-1991-1) last
  have tag : data.columns[3].get? i.val = some 25 := by
    change (⟨#[.affine 4096 25 0]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 4096 25 0 i.val i.isLt
  apply Vector.ext
  intro lane bound
  interval_cases lane <;> simp [TableData.rowNat,row,key,support,delegate,tag]

/-- The exact runtime region gives a canonical12bit key and precise flags.
    It is not assumed equal to the historical fixture or complete native pool. -/
theorem values {key support delegate : ZMod mersenne31Modulus}
    (member : Contains #v[key,support,delegate,25]) : key.val < 4096 ∧
      support = (supported key.val : Nat) ∧ delegate = (delegated key.val : Nat) := by
  obtain ⟨i,same⟩ := member
  have actual : #v[key,support,delegate,25] = (row i.val).map Nat.cast := by
    simpa only [TableData.row,rows] using same
  have head : key = (i.val : ZMod mersenne31Modulus) := by
    simpa [row] using congrArg (fun q : Vector (ZMod mersenne31Modulus) 4 => q[0]) actual
  have canonical : key.val = i.val := by rw [head,ZMod.val_natCast_of_lt (lt_trans i.isLt (by decide))]
  refine ⟨by rw [canonical]; exact i.isLt,?_,?_⟩
  · rw [canonical]
    simpa [row] using congrArg (fun q : Vector (ZMod mersenne31Modulus) 4 => q[1]) actual
  · rw [canonical]
    simpa [row] using congrArg (fun q : Vector (ZMod mersenne31Modulus) 4 => q[2]) actual
end Airbender.ReducedMachine.NativeRuntimeCSRProofs
