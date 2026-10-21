import Airbender.Proofs.Arithmetic.Word
import Mathlib.Tactic.FinCases

namespace Airbender.SubwordMemory.Proofs
open Arithmetic
set_option autoImplicit false

/-- Natural assembly of a subword replacement; native field/query assembly is
    connected separately. Adapted from the pinned v3 store arithmetic. -/
def mergedStore (byte highByte highHalf : Bool) (source old : Word) : Word :=
  let half := if highHalf then old.hi else old.lo
  let changed := if byte then
    (if highByte then half % 256 else 256 * (half / 256)) +
      source.lo % 256 * (if highByte then 256 else 1)
    else source.lo
  ⟨if highHalf then old.lo else changed, if highHalf then changed else old.hi⟩

theorem merged_store_bound (byte highByte highHalf : Bool) {source old : Word}
    (sourceBound : source.Bounded) (oldBound : old.Bounded) :
    (mergedStore byte highByte highHalf source old).Bounded := by
  obtain ⟨sl,sh⟩ := sourceBound
  obtain ⟨ol,oh⟩ := oldBound
  unfold limbBase at sl sh ol oh
  cases byte <;> cases highByte <;> cases highHalf
  all_goals simp only [mergedStore,Word.Bounded,limbBase,Bool.false_eq_true,if_false,if_true]
  all_goals constructor <;> omega

/-- The mathematical merge changes exactly the selected byte window.
    This reuses v3's natural/BitVec argument with native v2 clearing arithmetic,
    at the default recursion and heartbeat limits. -/
theorem merged_store_bytes (byte highByte highHalf : Bool) {source old : Word}
    (sourceBound : source.Bounded) (oldBound : old.Bounded)
    (aligned : byte = false → highByte = false) :
    let offset := (if highByte then 1 else 0) + 2 * (if highHalf then 1 else 0)
    ∀ i : Fin 4,
      (mergedStore byte highByte highHalf source old).toBitVec.extractLsb' (8 * i.val) 8 =
        if offset ≤ i.val ∧ i.val < offset + (if byte then 1 else 2)
        then (source.toBitVec.setWidth (8 * (if byte then 1 else 2))).extractLsb' (8 * (i.val - offset)) 8
        else old.toBitVec.extractLsb' (8 * i.val) 8 := by
  have sourceNat := Word.toBitVec_toNat sourceBound
  have oldNat := Word.toBitVec_toNat oldBound
  have newNat := Word.toBitVec_toNat (merged_store_bound byte highByte highHalf sourceBound oldBound)
  obtain ⟨sl,sh⟩ := sourceBound
  obtain ⟨ol,oh⟩ := oldBound
  unfold limbBase at sl sh ol oh
  dsimp only
  intro i
  cases byte <;> cases highByte <;> cases highHalf <;> fin_cases i
  all_goals solve
    | (have := aligned rfl; contradiction)
    | (simp only [Bool.false_eq_true,if_false,if_true] at newNat ⊢
       apply BitVec.eq_of_toNat_eq
       simp only [BitVec.extractLsb',BitVec.toNat_ofNat,BitVec.toNat_setWidth,sourceNat,oldNat,newNat]
       simp only [Bool.false_eq_true,if_false,if_true]
       norm_num only [Nat.reducePow,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub,Nat.le_refl,
         Nat.zero_le,Nat.reduceLT,and_self,true_and,false_and,if_false,if_true,
         Nat.shiftRight_eq_div_pow,Nat.div_one]
       simp only [BitVec.toNat_ofNat,mergedStore,Word.value,limbBase,Bool.false_eq_true,if_false,if_true]
       omega)

end Airbender.SubwordMemory.Proofs
