module
public import Slop.UnifiedReduced.RV.Setup
public import Slop.Arithmetic.Word

@[expose] public section

namespace Airbender.UnifiedReduced.Setup.Proofs.RV
open Trace Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

private theorem fixed_nonrom (i : Fin 1048961) : (fixedRow i)[9] ≠ 34 := by
  unfold fixedRow
  dsimp only
  split
  · simp only [binaryRow, Vector.getElem_set_self]
    have bound := shift_tag_bound ⟨i.val, by assumption⟩
    unfold binaryTag
    split_ifs <;> omega
  · split
    · change 1 ≠ 34; decide
    · split
      · change 5 ≠ 34; decide
      · split
        · change 2 ≠ 34; decide
        · split
          · change 51 ≠ 34; decide
          · change 47 + (i.val - 786817) / 65536 ≠ 34; omega

theorem rom_region {words : Nat → BitVec 32} {i : Fin 2097537}
    (selected : (rowWith words i)[9] = 34) :
    ∃ key : Fin 1048576, rowWith words i =
      #v[4 * key.val, (Word.ofBitVec (words key.val)).lo,
        (Word.ofBitVec (words key.val)).hi, 0, 0, 0, 0, 0, 0, 34] := by
  by_cases fixed : i.val < 1048961
  · have equal : rowWith words i = fixedRow ⟨i.val, fixed⟩ := dite_eq_left fixed
    rw [equal] at selected
    exact False.elim (fixed_nonrom ⟨i.val, fixed⟩ selected)
  · have bound := i.isLt
    refine ⟨⟨i.val - 1048961, by omega⟩, ?_⟩
    simp only [rowWith, dite_eq_right fixed]

theorem rom_lookup [Fact p.Prime] (hp : 4194304 ≤ p)
    {words : Nat → BitVec 32} {entry : Vector (Expression (ZMod p)) 10}
    {env : Environment (ZMod p)}
    (holds : (Lookup.mk (tableWith words).toRaw entry).Contains env)
    (selected : entry[9].eval env = 34) :
    (entry[0].eval env).val < ROM.limit ∧ (entry[0].eval env).val % 4 = 0 ∧
      (Word.mk (entry[1].eval env).val (entry[2].eval env).val).toBitVec =
        words ((entry[0].eval env).val / 4) ∧
      ∀ j : Fin 6, entry[j.val + 3].eval env = 0 := by
  obtain ⟨index, tag, columns⟩ := lookup_row (by omega) holds 34 (by decide) (by simpa using selected)
  obtain ⟨key, layout⟩ := rom_region tag
  have address : (entry[0].eval env).val = 4 * key.val := by
    have equation := congrArg ZMod.val (columns 0 (by decide))
    rw [layout] at equation
    simpa only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      ZMod.val_natCast_of_lt (by have := key.isLt; omega : 4 * key.val < p)] using equation
  have values : Word.mk (entry[1].eval env).val (entry[2].eval env).val =
      Word.ofBitVec (words key.val) := by
    have bounds := Word.ofBitVec_bound (words key.val)
    apply congrArg₂ Word.mk
    · have equation := congrArg ZMod.val (columns 1 (by decide))
      rw [layout] at equation
      change (entry[1].eval env).val = ((Word.ofBitVec (words key.val)).lo : ZMod p).val at equation
      exact equation.trans (ZMod.val_natCast_of_lt (lt_trans bounds.1 (by dsimp [limbBase]; omega)))
    · have equation := congrArg ZMod.val (columns 2 (by decide))
      rw [layout] at equation
      change (entry[2].eval env).val = ((Word.ofBitVec (words key.val)).hi : ZMod p).val at equation
      exact equation.trans (ZMod.val_natCast_of_lt (lt_trans bounds.2 (by dsimp [limbBase]; omega)))
  refine ⟨by rw [address]; dsimp [ROM.limit]; have := key.isLt; omega,
    by rw [address]; omega, ?_, ?_⟩
  · rw [address, values]
    simpa using Word.ofBitVec_roundtrip (words key.val)
  · intro j
    have equation := columns (j.val + 3) (by have := j.isLt; omega)
    rw [layout] at equation
    fin_cases j <;> simpa using equation

end Airbender.UnifiedReduced.Setup.Proofs.RV
