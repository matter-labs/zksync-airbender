import Airbender.Review.Blake2Round.Preparation

namespace Airbender.Blake2Round.Preparation.Proofs
open Arithmetic

set_option warningAsError true



theorem splitWord_bounded (value : UInt32) : (splitWord value).Bounded := by
  have range := value.toNat_lt
  constructor
  · exact Nat.mod_lt _ (by decide)
  · change value.toNat / limbBase < limbBase
    unfold limbBase
    omega

theorem set_bounded {n : Nat} {words : Vector Word n} {replacement : Word}
    (bounds : ∀ i : Fin n, words[i].Bounded) (index : Fin n) (good : replacement.Bounded) :
    ∀ i : Fin n, (words.set index.val replacement index.isLt)[i].Bounded := by
  intro i
  simp only [Fin.getElem_fin, Vector.getElem_set]
  split_ifs
  · exact good
  · exact bounds i

theorem append_bounded {n m : Nat} {left : Vector Word n} {right : Vector Word m}
    (leftBound : ∀ i : Fin n, left[i].Bounded) (rightBound : ∀ i : Fin m, right[i].Bounded) :
    ∀ i : Fin (n + m), (left ++ right)[i].Bounded := by
  intro i
  simp only [Fin.getElem_fin, Vector.getElem_append]
  split_ifs with low
  · exact leftBound ⟨i.val, low⟩
  · exact rightBound ⟨i.val - n, by have := i.isLt; omega⟩

theorem iv_bounded : ∀ i : Fin 8, iv[i].Bounded := by
  intro i
  simp only [iv, Fin.getElem_fin, Vector.getElem_map]
  exact splitWord_bounded _

theorem configuredIV_bounded : ∀ i : Fin 8, configuredIV[i].Bounded :=
  set_bounded iv_bounded 0 (splitWord_bounded _)

theorem compressionIV_bounded : ∀ i : Fin 8, compressionIV[i].Bounded :=
  set_bounded (set_bounded iv_bounded 4 (splitWord_bounded _)) 6 (splitWord_bounded _)

theorem output_bounded {input : Input}
    (stateBound : ∀ i : Fin 8, input.state[i].Bounded)
    (extendedBound : ∀ i : Fin 16, input.extended[i].Bounded)
    (messageBound : ∀ i : Fin 16, input.message[i].Bounded) :
    (∀ i : Fin 8, (step input).chaining[i].Bounded) ∧
    (∀ i : Fin 16, (step input).extended[i].Bounded) ∧
    (∀ i : Fin 16, (step input).message[i].Bounded) := by
  have chain : ∀ i : Fin 8,
      (if input.compression then configuredIV else input.state)[i].Bounded := by
    intro i
    cases mode : input.compression
    · simpa [mode] using stateBound i
    · simpa [mode] using configuredIV_bounded i
  have suffix : ∀ i : Fin 8,
      (if input.compression then compressionIV else (iv.set 4 input.extended[12]).set 6 input.extended[14])[i].Bounded := by
    intro i
    cases mode : input.compression
    · have normal := set_bounded (set_bounded iv_bounded 4 (extendedBound 12)) 6 (extendedBound 14) i
      simpa [mode] using normal
    · simpa [mode] using compressionIV_bounded i
  have extended : ∀ i : Fin 16, (step input).extended[i].Bounded := by
    intro i
    cases first : input.firstRound
    · simpa [step, first] using extendedBound i
    · simpa [step, first] using append_bounded chain suffix i
  have messagePrefix : ∀ i : Fin 8, (input.message.take 8)[i].Bounded := by
    intro i
    simp only [Fin.getElem_fin, Vector.getElem_take]
    exact messageBound ⟨i.val, by have := i.isLt; omega⟩
  have message : ∀ i : Fin 16, (step input).message[i].Bounded := by
    intro i
    cases mode : input.compression
    · simpa [step, mode] using messageBound i
    · cases right : input.inputIsRight
      · have bound := append_bounded stateBound messagePrefix i
        change (input.state.toArray ++ input.message.toArray.extract 0 8)[i.val].Bounded at bound
        cases first : input.firstRound <;> simp only [step, mode, right, first,
          Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        all_goals change (input.state.toArray ++ input.message.toArray.extract 0 8)[i.val].Bounded
        all_goals exact bound
      · have bound := append_bounded messagePrefix stateBound i
        change (input.message.toArray.extract 0 8 ++ input.state.toArray)[i.val].Bounded at bound
        cases first : input.firstRound <;> simp only [step, mode, right, first,
          Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        all_goals change (input.message.toArray.extract 0 8 ++ input.state.toArray)[i.val].Bounded
        all_goals exact bound
  exact ⟨chain, extended, message⟩

end Airbender.Blake2Round.Preparation.Proofs
