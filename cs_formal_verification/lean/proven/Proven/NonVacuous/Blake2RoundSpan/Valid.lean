module
public import Proven.NonVacuous.Blake2RoundSpan.Columns
public import Proven.NonVacuous.Blake2RoundSpan.GHonest

@[expose] public section

/-! The ranges the honest round row needs (`RowInput.Valid`): a 128-aligned state pointer and a 64-aligned message
    pointer, canonical words, previous clocks below the write clock and an invocation clock that is 1 mod 4 with
    room for the writes. Then every prepared lane, scheduled word, G call input and written word is canonical. -/

namespace Airbender.NonVacuous.Blake2RoundSpan
open Arithmetic

namespace RowInput

structure Valid (x : RowInput) : Prop where
  statePointer : x.statePointer.Bounded ∧ x.statePointer.lo % 128 = 0
  messagePointer : x.messagePointer.Bounded ∧ x.messagePointer.lo % 64 = 0
  state : ∀ i < 8, (x.state i).Bounded
  extended : ∀ i < 16, (x.extended i).Bounded
  message : ∀ i < 16, (x.message i).Bounded
  previous : ∀ j < 43, x.previous j < x.invocation + 2
  invocation : x.invocation % 4 = 1
  room : x.invocation + 2 < Trace.timestampBase

theorem ivWord_bounded : ∀ i < 8, (ivWord i).lo < 65536 ∧ (ivWord i).hi < 65536 := by decide +kernel

variable {x : RowInput} (valid : x.Valid)
include valid

theorem Valid.lane {L : Nat} (hL : L < 16) : (x.lane L).Bounded := by
  unfold RowInput.lane
  split_ifs with first small edge
  · exact valid.state L small
  · exact valid.extended L hL
  · simp only [Word.Bounded, limbBase]; exact ivWord_bounded (L - 8) (by omega)
  · exact valid.extended L hL

theorem Valid.sched (j : Nat) : (x.sched j).Bounded := valid.message _ (Fin.isLt _)

theorem Valid.colCall {k : Nat} (hk : k < 4) : GValid (x.colCall k) :=
  ⟨valid.lane (by omega), valid.lane (by omega), valid.lane (by omega), valid.lane (by omega), valid.sched _,
    valid.sched _⟩

theorem Valid.mixed {L : Nat} (hL : L < 16) : (x.mixed L).Bounded := by
  obtain ⟨k, hk, rfl | rfl | rfl | rfl⟩ : ∃ k < 4, L = k ∨ L = 4 + k ∨ L = 8 + k ∨ L = 12 + k :=
    ⟨L % 4, by omega, by omega⟩
  all_goals first
    | rw [x.mixed_a hk] | rw [x.mixed_b hk] | rw [x.mixed_c hk] | rw [x.mixed_d hk]
  all_goals
    have outputs := (valid.colCall hk).outputs
    simp only [Word.Bounded, limbBase, RowInput.outA, RowInput.outB, RowInput.outC, RowInput.outD]
    omega

theorem Valid.diagCall {k : Nat} (hk : k < 4) : GValid (x.diagCall k) :=
  ⟨valid.mixed (by omega), valid.mixed (by omega), valid.mixed (by omega), valid.mixed (by omega), valid.sched _,
    valid.sched _⟩

theorem Valid.out {L : Nat} (hL : L < 16) : (x.out L).Bounded := by
  obtain ⟨k, hk, rfl | rfl | rfl | rfl⟩ : ∃ k < 4, L = k ∨ L = 4 + (k + 1) % 4 ∨ L = 8 + (k + 2) % 4 ∨
      L = 12 + (k + 3) % 4 :=
    if h : L < 4 then ⟨L, h, Or.inl rfl⟩
    else if h' : L < 8 then ⟨(L + 3) % 4, by omega, Or.inr (Or.inl (by omega))⟩
    else if h'' : L < 12 then ⟨(L + 2) % 4, by omega, Or.inr (Or.inr (Or.inl (by omega)))⟩
    else ⟨(L + 1) % 4, by omega, Or.inr (Or.inr (Or.inr (by omega)))⟩
  all_goals first
    | rw [x.out_a hk] | rw [x.out_b hk] | rw [x.out_c hk] | rw [x.out_d hk]
  all_goals
    have outputs := (valid.diagCall hk).outputs
    simp only [Word.Bounded, limbBase, RowInput.outA, RowInput.outB, RowInput.outC, RowInput.outD]
    omega

end RowInput

end Airbender.NonVacuous.Blake2RoundSpan
