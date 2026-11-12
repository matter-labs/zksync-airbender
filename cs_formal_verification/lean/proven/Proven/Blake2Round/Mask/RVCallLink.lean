module
public import Proven.Blake2Round.RVCompression

@[expose] public section
namespace Airbender.Blake2Round.Mask.Proofs
open Arithmetic Trace Trace.Proofs Delegation.Proofs Blake2Round.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- A native two-block effect and its physical frame give one actual RV round call. -/
theorem two_block_call {S T : RV.State} {state : RV.Word} {first : Vector RV.Word 8}
    {second : Vector RV.Word 16} {control : RV.Word}
    (stateAligned : state.toNat % 128 = 0)
    (effect : RV.Delegation.effect .blakeRound (S.getReg 10) (S.getReg 11) (S.getReg 12) S.mem =
      some (⟨RV.writesAt state first ++ RV.writesAt (state + 32) second, 12, control⟩ : RV.Effect))
    (stateWords : (rvBlockWords T state 8 0).map Word.toBitVec = first)
    (extendedWords : (rvBlockWords T state 16 8).map Word.toBitVec = second)
    (x12 : T.getReg 12 = control)
    (regs : ∀ reg : BitVec 5, reg ≠ 12 → T.getReg reg = S.getReg reg)
    (words : ∀ a : RV.Word, a.toNat % 4 = 0 → (∀ j : Fin 24, a ≠ state + BitVec.ofNat 32 (4 * j.val)) →
      RV.read T.mem a 4 = RV.read S.mem a 4)
    (rom : T.rom = S.rom) (input : T.input = S.input) (pc : RV.Word) :
    ∃ next, RV.calls [.blakeRound] (S.setPC pc) = some next ∧ RV.Same next (T.setPC (pc + 4)) := by
  have fits : state.toNat + 96 ≤ 2 ^ 32 := by have := state.isLt; omega
  have secondFits : (state + 32#32).toNat = state.toNat + 32 := by
    have thirtyTwo : (32#32).toNat = 32 := by rfl
    simp only [BitVec.toNat_add, thirtyTwo]
    omega
  apply call_same (S := S.setPC pc) (T := T) (k := .blakeRound)
    (by exact effect) _ rom input _ _
  · intro aw member
    rcases List.mem_append.mp member with first | second
    · exact (RV.writesAt_in state _ (by omega) (by simp only [RV.RAM_END]; omega) aw first).1
    · exact (RV.writesAt_in (state + 32#32) _ (by omega) (by simp only [RV.RAM_END]; omega) aw second).1
  · intro reg
    by_cases r12 : reg = 12
    · subst r12
      simp only [true_and, show (12 : BitVec 5) ≠ 0 by decide, ne_eq, not_false_eq_true, ite_true]
      exact x12
    · simp only [r12, false_and, ite_false]
      exact regs reg r12
  · intro a alignedA
    rw [storeAll_setPC]
    exact two_block_words stateAligned stateWords extendedWords words a alignedA

end Airbender.Blake2Round.Mask.Proofs
