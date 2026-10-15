import Airbender.Review.Trace.Workers.Blake2Round.Compression
import Airbender.Proofs.Arithmetic.Word

namespace Airbender.Blake2Round.Proofs
open Arithmetic
set_option warningAsError true
set_option maxRecDepth 16384

private theorem canonical_word {word : Word} (bounded : word.Bounded) :
    Word.ofBitVec (BitVec.ofNat 32 word.value) = word := by
  apply Word.eq_of_value (Word.ofBitVec_bound _) bounded
  simpa only [Word.toBitVec, Word.ofBitVec_value] using Word.toBitVec_toNat bounded

private theorem canonical_words {n : Nat} (words : Vector Word n)
    (bounded : ∀ i : Fin n, words[i].Bounded) :
    (words.map Word.value).map (fun value => Word.ofBitVec (BitVec.ofNat 32 value)) = words := by
  apply Vector.ext
  intro i bound
  simpa only [Vector.getElem_map, Fin.getElem_fin] using canonical_word (bounded ⟨i, bound⟩)

theorem row_compression {input : Row.Input} {output : Row.Output} {flags : Fin 8}
    (effect : Row.spec input output)
    (modes : input.reducedRounds = decide (flags.val % 2 = 1) ∧
      input.inputIsRight = decide (flags.val / 2 % 2 = 1) ∧ input.compression = decide (flags.val / 4 = 1))
    (stateBound : ∀ i : Fin 8, output.state[i].Bounded)
    (extendedBound : ∀ i : Fin 16, output.extended[i].Bounded) :
    (output.state, output.extended) = Compression.step flags input.round (input.state, input.extended) input.message := by
  obtain ⟨_, mixing, finalization, _⟩ := effect
  dsimp only [Mixing.spec] at mixing
  have extended := congrArg (fun words : Vector Nat 16 =>
    words.map (fun value => Word.ofBitVec (BitVec.ofNat 32 value))) mixing
  rw [canonical_words output.extended extendedBound] at extended
  simp only [Row.preparationInput] at extended
  dsimp only [Compression.step]
  rw [← modes.1, ← modes.2.1, ← modes.2.2]
  change (output.state, output.extended) =
    (if Finalization.isFinal ⟨input.round, input.reducedRounds, input.state,
      (Preparation.step (Row.preparationInput input)).chaining, _⟩ then _ else input.state, _)
  rw [← extended]
  apply Prod.ext
  · dsimp only [Finalization.spec] at finalization
    split_ifs at finalization ⊢ with final
    · have state := congrArg (fun words : Vector Nat 8 =>
        words.map (fun value => Word.ofBitVec (BitVec.ofNat 32 value))) finalization
      rwa [canonical_words output.state stateBound] at state
    · exact finalization
  · rfl

end Airbender.Blake2Round.Proofs
