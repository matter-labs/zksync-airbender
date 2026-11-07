import Mathlib.Tactic.FinCases
import Airbender.Review.Circuits.Blake2Worker.Tables
import Airbender.Proofs.Tables.PeriodicColumns
import Airbender.Review.Helpers.Tables.NativeBinary

namespace Airbender.Blake2Worker.FixedProofs
open Setup Setup.Proofs Fixed Verification
set_option warningAsError true
set_option Elab.async false
set_option autoImplicit false

theorem length_eq (kind : Kind) : (data kind).length = kind.bound * kind.bound := by cases kind <;> rfl

theorem extent (kind : Kind) : kind.offset + (data kind).length ≤ 344384 := by cases kind <;> decide

private theorem periodic_first (base n : Nat) (positive : 0 < base) (bound : n < base*base) :
    (⟨#[.periodic base 1 (Array.replicate base 0)]⟩ : Column).get? n = some (n/base) := by
  change getFromBlocks [.periodic base 1 (Array.replicate base 0)] n = _
  rw [getFromBlocks,if_pos (by simpa only [Block.length,Array.size_replicate] using bound)]
  have read := periodic_get (Array.replicate base 0) base 1 n (by simpa using positive) (by simpa using bound)
  change Block.get? (.periodic base 1 (Array.replicate base 0)) n = _ at read
  rw [read]
  simp

private theorem periodic_second (base n : Nat) (positive : 0 < base) (bound : n < base*base) :
    (⟨#[.periodic base 0 (Array.range base)]⟩ : Column).get? n = some (n%base) := by
  change getFromBlocks [.periodic base 0 (Array.range base)] n = _
  rw [getFromBlocks,if_pos (by simpa only [Block.length,Array.size_range] using bound)]
  have read := periodic_get (Array.range base) base 0 n (by simpa using positive) (by simpa using bound)
  change Block.get? (.periodic base 0 (Array.range base)) n = _ at read
  rw [read]
  simp

theorem first (kind : Kind) (i : Fin (data kind).length) :
    (data kind).columns[0].get? i.val = some (i.val/kind.bound) := by
  have column : (data kind).columns[0] = ⟨#[.periodic kind.bound 1 (Array.replicate kind.bound 0)]⟩ := by cases kind <;> rfl
  rw [column]
  apply periodic_first
  · cases kind <;> decide
  · rw [← length_eq]; exact i.isLt

theorem second (kind : Kind) (i : Fin (data kind).length) :
    (data kind).columns[1].get? i.val = some (i.val%kind.bound) := by
  have column : (data kind).columns[1] = ⟨#[.periodic kind.bound 0 (Array.range kind.bound)]⟩ := by cases kind <;> rfl
  rw [column]
  apply periodic_second
  · cases kind <;> decide
  · rw [← length_eq]; exact i.isLt

theorem tagged (kind : Kind) (i : Fin (data kind).length) :
    (data kind).columns[3].get? i.val = some kind.tag := by
  have column : (data kind).columns[3] = ⟨#[.affine (data kind).length kind.tag 0]⟩ := by cases kind <;> rfl
  rw [column]
  change getFromBlocks [.affine (data kind).length kind.tag 0] i.val = _
  rw [getFromBlocks]
  simp only [Block.length]
  rw [if_pos i.isLt]
  simp [Block.get?,Block.length,i.isLt]

theorem fields (kind : Kind) (i : Fin (data kind).length) :
    (((data kind).row i : Vector (ZMod mersenne31Modulus) 4)[0]).val = i.val/kind.bound ∧
    (((data kind).row i : Vector (ZMod mersenne31Modulus) 4)[1]).val = i.val%kind.bound ∧
    (((data kind).row i : Vector (ZMod mersenne31Modulus) 4)[3]).val = kind.tag := by
  have positive : 0 < kind.bound := by cases kind <;> decide
  have bound : i.val < kind.bound*kind.bound := by rw [← length_eq]; exact i.isLt
  have b0 : i.val/kind.bound < kind.bound := (Nat.div_lt_iff_lt_mul positive).mpr bound
  have b1 : i.val%kind.bound < kind.bound := Nat.mod_lt _ positive
  have modulus : kind.bound ≤ mersenne31Modulus := by cases kind <;> decide
  have tagBound : kind.tag < mersenne31Modulus := by cases kind <;> decide
  simp only [TableData.row,TableData.rowNat,Vector.getElem_map,first,second,tagged,Option.getD_some]
  rw [ZMod.val_natCast_of_lt (lt_of_lt_of_le b0 modulus),ZMod.val_natCast_of_lt (lt_of_lt_of_le b1 modulus),ZMod.val_natCast_of_lt tagBound]
  exact ⟨rfl,rfl,rfl⟩

theorem member_region (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query) :
    ∃ kind : Kind, ∃ i : Fin (data kind).length, query = (data kind).row i := by
  obtain ⟨i,same⟩ := member
  change query = (rowNat i).map Nat.cast at same
  rw [rowNat] at same
  by_cases h : i.val < 65536
  · rw [dif_pos h] at same
    exact ⟨.byte,_,same⟩
  rw [dif_neg h] at same
  by_cases h : i.val < 65600
  · rw [dif_pos h] at same
    exact ⟨.three,_,same⟩
  rw [dif_neg h] at same
  by_cases h : i.val < 65856
  · rw [dif_pos h] at same
    exact ⟨.four,_,same⟩
  rw [dif_neg h] at same
  by_cases h : i.val < 82240
  · rw [dif_pos h] at same
    exact ⟨.seven,_,same⟩
  rw [dif_neg h] at same
  exact ⟨.nine,_,same⟩

theorem pool_row (kind : Kind) (i : Fin (data kind).length) :
    rowNat ⟨kind.offset+i.val,by have := extent kind; have := i.isLt; omega⟩ = (data kind).rowNat i := by
  cases kind
  · have bound : i.val < 65536 := i.isLt
    simp only [Kind.offset]
    rw [rowNat]
    rw [dif_pos (by change 0+i.val < 65536; omega)]
    have same : (⟨0+i.val-0,by change 0+i.val-0 < 65536; omega⟩ : Fin dataT4.length) = i := Fin.ext (by change 0+i.val-0 = i.val; omega)
    exact congrArg dataT4.rowNat same
  · have bound : i.val < 64 := i.isLt
    simp only [Kind.offset]
    rw [rowNat]
    rw [dif_neg (by change ¬ 65536+i.val < 65536; omega)]
    rw [dif_pos (by change 65536+i.val < 65600; omega)]
    have same : (⟨65536+i.val-65536,by change 65536+i.val-65536 < 64; omega⟩ : Fin dataT26.length) = i := Fin.ext (by change 65536+i.val-65536 = i.val; omega)
    exact congrArg dataT26.rowNat same
  · have bound : i.val < 256 := i.isLt
    simp only [Kind.offset]
    rw [rowNat]
    rw [dif_neg (by change ¬ 65600+i.val < 65536; omega)]
    rw [dif_neg (by change ¬ 65600+i.val < 65600; omega)]
    rw [dif_pos (by change 65600+i.val < 65856; omega)]
    have same : (⟨65600+i.val-65600,by change 65600+i.val-65600 < 256; omega⟩ : Fin dataT27.length) = i := Fin.ext (by change 65600+i.val-65600 = i.val; omega)
    exact congrArg dataT27.rowNat same
  · have bound : i.val < 16384 := i.isLt
    simp only [Kind.offset]
    rw [rowNat]
    rw [dif_neg (by change ¬ 65856+i.val < 65536; omega)]
    rw [dif_neg (by change ¬ 65856+i.val < 65600; omega)]
    rw [dif_neg (by change ¬ 65856+i.val < 65856; omega)]
    rw [dif_pos (by change 65856+i.val < 82240; omega)]
    have same : (⟨65856+i.val-65856,by change 65856+i.val-65856 < 16384; omega⟩ : Fin dataT28.length) = i := Fin.ext (by change 65856+i.val-65856 = i.val; omega)
    exact congrArg dataT28.rowNat same
  · have bound : i.val < 262144 := i.isLt
    simp only [Kind.offset]
    rw [rowNat]
    rw [dif_neg (by change ¬ 82240+i.val < 65536; omega)]
    rw [dif_neg (by change ¬ 82240+i.val < 65600; omega)]
    rw [dif_neg (by change ¬ 82240+i.val < 65856; omega)]
    rw [dif_neg (by change ¬ 82240+i.val < 82240; omega)]
    have same : (⟨82240+i.val-82240,by change 82240+i.val-82240 < 262144; omega⟩ : Fin dataT29.length) = i := Fin.ext (by change 82240+i.val-82240 = i.val; omega)
    exact congrArg dataT29.rowNat same

theorem every_row (kind : Kind) (i : Fin (data kind).length) :
    (table (p := mersenne31Modulus)).Contains #[] ((data kind).row i) := by
  change ∃ index : Fin 344384, (data kind).row i = (rowNat index).map Nat.cast
  refine ⟨⟨kind.offset+i.val,by have := extent kind; have := i.isLt; omega⟩,?_⟩
  rw [pool_row]
  rfl

theorem inputs (query : Vector (ZMod mersenne31Modulus) 4)
    (member : (table (p := mersenne31Modulus)).Contains #[] query) :
    ∃ kind : Kind, query[3].val = kind.tag ∧ query[0].val < kind.bound ∧ query[1].val < kind.bound := by
  obtain ⟨kind,i,rfl⟩ := member_region query member
  obtain ⟨first,second,tag⟩ := fields kind i
  have positive : 0 < kind.bound := by cases kind <;> decide
  have bound : i.val < kind.bound*kind.bound := by rw [← length_eq]; exact i.isLt
  exact ⟨kind,tag,first ▸ (Nat.div_lt_iff_lt_mul positive).mpr bound,second ▸ Nat.mod_lt _ positive⟩

/-- Exact literal columns only; worker pool offset0 is distinct from old offset1. -/
theorem byte_columns : dataT4.columns = NativeBinary.dataXor.columns := rfl

theorem xor3 (i : Fin 64) :
    ((dataT26.row i : Vector (ZMod mersenne31Modulus) 4)[2]).val = i.val/8 ^^^ i.val%8 := by
  fin_cases i <;> decide +kernel

theorem xor4 (i : Fin 256) :
    ((dataT27.row i : Vector (ZMod mersenne31Modulus) 4)[2]).val = i.val/16 ^^^ i.val%16 := by
  fin_cases i <;> decide +kernel

end Airbender.Blake2Worker.FixedProofs
