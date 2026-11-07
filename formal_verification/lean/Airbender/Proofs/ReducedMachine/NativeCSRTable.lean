import Airbender.Proofs.ReducedMachine.NativePool
import Airbender.Review.Circuits.ReducedMachine.Tables.CSR
import Mathlib.Tactic.IntervalCases

namespace Airbender.ReducedMachine.NativeCSRTableProofs
open NativeFixed Setup Verification
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

/-- Complete actual 4096-row table certificate from symbolic zero intervals
    and six/two finite exceptional slots. No generated table is made opaque. -/
theorem rows (i : Fin 4096) : dataT25.rowNat i = csrRow i.val := by
  have key : dataT25.columns[0].get? i.val = some i.val := by
    change (⟨#[.affine 4096 0 1]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 4096 0 1 i.val i.isLt
  have supported : dataT25.columns[1].get? i.val = some (csrSupported i.val) := by
    change getFromBlocks [.affine 1984 0 0,.dense #[1,0,0,0,1,1],.affine 2106 0 0] i.val = _
    by_cases front : i.val < 1984
    · rw [getFromBlocks]
      simp only [Block.length,if_pos front]
      have meaning : csrSupported i.val = 0 := by simp [csrSupported]; omega
      simpa [meaning] using affine_get 1984 0 0 i.val front
    · by_cases middle : i.val < 1990
      · have cases : i.val=1984 ∨ i.val=1985 ∨ i.val=1986 ∨ i.val=1987 ∨ i.val=1988 ∨ i.val=1989 := by omega
        rcases cases with h | h | h | h | h | h
        all_goals simp [h,csrSupported,getFromBlocks,Block.length,Block.get?]
      · rw [getFromBlocks]
        simp only [Block.length]
        rw [if_neg front,getFromBlocks]
        simp only [Block.length]
        simp only [show (#[1,0,0,0,1,1] : Array Nat).size = 6 from rfl]
        rw [if_neg (by omega),getFromBlocks]
        simp only [Block.length]
        rw [if_pos (by have := i.isLt; omega)]
        have meaning : csrSupported i.val = 0 := by simp [csrSupported]; omega
        simpa [meaning] using affine_get 2106 0 0 (i.val-1984-6) (by have := i.isLt; omega)
  have delegated : dataT25.columns[2].get? i.val = some (csrDelegated i.val) := by
    change getFromBlocks [.affine 1988 0 0,.dense #[1,1],.affine 2106 0 0] i.val = _
    by_cases front : i.val < 1988
    · rw [getFromBlocks]
      simp only [Block.length,if_pos front]
      have meaning : csrDelegated i.val = 0 := by simp [csrDelegated]; omega
      simpa [meaning] using affine_get 1988 0 0 i.val front
    · by_cases middle : i.val < 1990
      · have cases : i.val=1988 ∨ i.val=1989 := by omega
        rcases cases with h | h
        all_goals simp [h,csrDelegated,getFromBlocks,Block.length,Block.get?]
      · rw [getFromBlocks]
        simp only [Block.length]
        rw [if_neg front,getFromBlocks]
        simp only [Block.length]
        simp only [show (#[1,1] : Array Nat).size = 2 from rfl]
        rw [if_neg (by omega),getFromBlocks]
        simp only [Block.length]
        rw [if_pos (by have := i.isLt; omega)]
        have meaning : csrDelegated i.val = 0 := by simp [csrDelegated]; omega
        simpa [meaning] using affine_get 2106 0 0 (i.val-1988-2) (by have := i.isLt; omega)
  have tag : dataT25.columns[3].get? i.val = some 25 := by
    change (⟨#[.affine 4096 25 0]⟩ : Column).get? i.val = _
    rw [single_get _ _ i.isLt]
    simpa using affine_get 4096 25 0 i.val i.isLt
  apply Vector.ext
  intro lane bound
  interval_cases lane <;> simp [TableData.rowNat,csrRow,key,supported,delegated,tag]

/-- Full native pool tag isolation and the complete certificate recover exact
    key domain/support/delegation outputs, without a table-equivalence premise. -/
theorem values {key supported delegated : ZMod mersenne31Modulus}
    (member : (table (p := mersenne31Modulus)).Contains #[] #v[key,supported,delegated,25]) :
    key.val < 4096 ∧ supported = (csrSupported key.val : Nat) ∧ delegated = (csrDelegated key.val : Nat) := by
  obtain ⟨i,same⟩ := NativePoolProofs.selected_region _ member .csr rfl
  change #v[key,supported,delegated,25] = dataT25.row i at same
  have actual : #v[key,supported,delegated,25] = (csrRow i.val).map Nat.cast := by
    simpa only [TableData.row,rows] using same
  have head : key = (i.val : ZMod mersenne31Modulus) := by
    simpa [csrRow] using congrArg (fun q : Vector (ZMod mersenne31Modulus) 4 => q[0]) actual
  have canonical : key.val = i.val := by
    rw [head,ZMod.val_natCast_of_lt (lt_trans i.isLt (by decide))]
  refine ⟨by rw [canonical]; exact i.isLt,?_,?_⟩
  · rw [canonical]
    simpa [csrRow] using congrArg (fun q : Vector (ZMod mersenne31Modulus) 4 => q[1]) actual
  · rw [canonical]
    simpa [csrRow] using congrArg (fun q : Vector (ZMod mersenne31Modulus) 4 => q[2]) actual

end Airbender.ReducedMachine.NativeCSRTableProofs
