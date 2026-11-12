module
public import Proven.Import.Json.Strings

@[expose] public section

/-! Completeness of the parser without the duplicate-name check: every JSON text parses to its value. Since the
parser is a function, a JSON text has exactly one value. -/

namespace Airbender.Json.Parser
open Airbender.Json

/-- The input does not continue with a digit (what may follow an integer). -/
def NoDigitHead (r : List UInt8) : Prop := ∀ b ∈ r.head?, isDigit b = false

theorem ws_not_digit {b : UInt8} (h : b = 0x20 ∨ b = 0x09 ∨ b = 0x0A ∨ b = 0x0D) : isDigit b = false := by
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem noDigitHead_ws {w : List UInt8} {c : UInt8} (r : List UInt8) (hw : Ws w) (hc : isDigit c = false) :
    NoDigitHead (w ++ c :: r) := by
  cases w with
  | nil => simpa [NoDigitHead] using hc
  | cons b w => simpa [NoDigitHead] using ws_not_digit (hw b (by simp))

theorem noDigitHead_ws_nil {w : List UInt8} (hw : Ws w) : NoDigitHead w := by
  cases w with
  | nil => simp [NoDigitHead]
  | cons b w => simpa [NoDigitHead] using ws_not_digit (hw b (by simp))

/-- What a value text starts with: not whitespace, `]` or `}`. -/
def ValueStart (b : UInt8) : Prop := isWs b = false ∧ b ≠ 0x5D ∧ b ≠ 0x7D

theorem valueText_head {v : Value} {bs : List UInt8} (h : ValueText v bs) :
    ∃ b t, bs = b :: t ∧ ValueStart b := by
  cases h with
  | null => exact ⟨_, _, utf8_null, by unfold ValueStart; decide⟩
  | true => exact ⟨_, _, utf8_true, by unfold ValueStart; decide⟩
  | false => exact ⟨_, _, utf8_false, by unfold ValueStart; decide⟩
  | @int n =>
    rw [utf8_int]
    split
    · exact ⟨_, _, rfl, by unfold ValueStart; decide⟩
    · obtain ⟨b, t, hbt⟩ : ∃ b t, utf8 (toString n.natAbs) = b :: t := by
        cases h : utf8 (toString n.natAbs) with
        | nil => exact absurd h (utf8_nat_ne_nil _)
        | cons b t => exact ⟨b, t, rfl⟩
      have hd := digits_of_toDigits n.natAbs b (by rw [hbt]; simp)
      refine ⟨b, t, hbt, ?_, ?_, ?_⟩
      · rw [isDigit_iff] at hd
        simp only [isWs, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> intro hb <;> subst hb <;> simp at hd
      · rw [isDigit_iff] at hd; intro hb; subst hb; simp at hd
      · rw [isDigit_iff] at hd; intro hb; subst hb; simp at hd
  | str => exact ⟨_, _, rfl, by unfold ValueStart; decide⟩
  | emptyArr => exact ⟨_, _, rfl, by unfold ValueStart; decide⟩
  | arr => exact ⟨_, _, rfl, by unfold ValueStart; decide⟩
  | emptyObj => exact ⟨_, _, rfl, by unfold ValueStart; decide⟩
  | obj => exact ⟨_, _, rfl, by unfold ValueStart; decide⟩

theorem valueText_length {v : Value} {bs : List UInt8} (h : ValueText v bs) : 1 ≤ bs.length := by
  obtain ⟨b, t, rfl, -⟩ := valueText_head h; simp

/-- Skipping whitespace before a value text. -/
theorem skipWs_value {w bs : List UInt8} {v : Value} (r : List UInt8) (hw : Ws w) (h : ValueText v bs) :
    skipWs (w ++ bs ++ r) = bs ++ r := by
  obtain ⟨b, t, rfl, hb, -⟩ := valueText_head h
  rw [List.append_assoc, skipWs_ws _ hw, List.cons_append, skipWs_of_not_ws _ hb]

theorem skipWs_close {w : List UInt8} {c : UInt8} (r : List UInt8) (hw : Ws w) (hc : isWs c = false) :
    skipWs (w ++ c :: r) = c :: r := by
  rw [skipWs_ws _ hw, skipWs_of_not_ws _ hc]

theorem elementsText_skip {items : List Value} {bs : List UInt8} (h : ElementsText items bs) (r : List UInt8) :
    ∃ c r', skipWs (bs ++ r) = c :: r' ∧ (c == 0x5D) = false := by
  cases h with
  | @one w₁ v bv w₂ hw₁ hv hw₂ =>
    obtain ⟨b, t, rfl, -, hb, -⟩ := valueText_head hv
    refine ⟨b, t ++ w₂ ++ r, ?_, by simpa using hb⟩
    rw [show w₁ ++ b :: t ++ w₂ ++ r = w₁ ++ (b :: t) ++ (w₂ ++ r) by simp, skipWs_value _ hw₁ hv]; simp
  | @cons w₁ v bv w₂ vs rest hw₁ hv hw₂ _ =>
    obtain ⟨b, t, rfl, -, hb, -⟩ := valueText_head hv
    refine ⟨b, t ++ w₂ ++ 0x2C :: rest ++ r, ?_, by simpa using hb⟩
    rw [show w₁ ++ b :: t ++ w₂ ++ 0x2C :: rest ++ r = w₁ ++ (b :: t) ++ (w₂ ++ 0x2C :: rest ++ r) by simp,
      skipWs_value _ hw₁ hv]; simp

theorem keyText {k : String} {ks : List UInt8} (h : ValueText (.str k) ks) :
    ∃ bk, ks = 0x22 :: bk ++ [0x22] ∧ CharsText k.toList bk := by
  cases h with
  | str hcs => exact ⟨_, rfl, hcs⟩

theorem membersText_skip {ms : List (String × Value)} {bs : List UInt8} (h : MembersText ms bs)
    (r : List UInt8) : ∃ r', skipWs (bs ++ r) = 0x22 :: r' := by
  cases h with
  | @one w₁ k ks w₂ w₃ v bv w₄ hw₁ hk =>
    obtain ⟨bk, rfl, -⟩ := keyText hk
    refine ⟨bk ++ [0x22] ++ w₂ ++ 0x3A :: w₃ ++ bv ++ w₄ ++ r, ?_⟩
    rw [show w₁ ++ (0x22 :: bk ++ [0x22]) ++ w₂ ++ 0x3A :: w₃ ++ bv ++ w₄ ++ r =
      w₁ ++ (0x22 :: (bk ++ [0x22] ++ w₂ ++ 0x3A :: w₃ ++ bv ++ w₄ ++ r)) by simp,
      skipWs_close _ hw₁ (by decide)]
  | @cons w₁ k ks w₂ w₃ v bv w₄ ms' rest hw₁ hk =>
    obtain ⟨bk, rfl, -⟩ := keyText hk
    refine ⟨bk ++ [0x22] ++ w₂ ++ 0x3A :: w₃ ++ bv ++ w₄ ++ 0x2C :: rest ++ r, ?_⟩
    rw [show w₁ ++ (0x22 :: bk ++ [0x22]) ++ w₂ ++ 0x3A :: w₃ ++ bv ++ w₄ ++ 0x2C :: rest ++ r =
      w₁ ++ (0x22 :: (bk ++ [0x22] ++ w₂ ++ 0x3A :: w₃ ++ bv ++ w₄ ++ 0x2C :: rest ++ r)) by simp,
      skipWs_close _ hw₁ (by decide)]

theorem key_complete {k : String} {ks : List UInt8} (h : ValueText (.str k) ks) (f : Nat) (r : List UInt8)
    (hf : ks.length < f + 1) : ∃ bk, ks = 0x22 :: bk ++ [0x22] ∧ chars f "" (bk ++ 0x22 :: r) = .ok (k, r) := by
  obtain ⟨bk, rfl, hcs⟩ := keyText h
  obtain ⟨s, hs, hl⟩ := chars_complete hcs f "" r (by simp at hf; omega)
  simp only [String.toList_empty, List.nil_append] at hl
  exact ⟨bk, rfl, by rw [hs, String.toList_inj.1 hl]⟩

theorem value_complete_all : ∀ f : Nat,
    (∀ v bs r, ValueText v bs → bs.length < f → NoDigitHead r → value f (bs ++ r) = .ok (v, r)) ∧
    (∀ items bs r acc, ElementsText items bs → bs.length + 1 < f →
      elements f (bs ++ 0x5D :: r) acc = .ok (acc.reverse ++ items, r)) ∧
    (∀ ms bs r acc, MembersText ms bs → bs.length + 1 < f →
      members f (bs ++ 0x7D :: r) acc = .ok (acc.reverse ++ ms, r))
  | 0 => ⟨fun _ _ _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | f + 1 => by
    obtain ⟨hv, he, hm⟩ := value_complete_all f
    refine ⟨?_, ?_, ?_⟩
    · intro v bs r h hlen hr
      cases h with
      | null => rw [utf8_null]; simp [value, dropPrefix_complete]
      | true => rw [utf8_true]; simp [value, dropPrefix_complete]
      | false => rw [utf8_false]; simp [value, dropPrefix_complete]
      | @int n =>
        have hi := int_complete n hr
        obtain ⟨b, t, hbt, -⟩ := valueText_head (ValueText.int (n := n))
        rw [hbt] at hi ⊢
        have hb : b = 0x2D ∨ isDigit b = true := by
          revert hbt; rw [utf8_int]; split
          · intro h; simp at h; exact Or.inl h.1.symm
          · intro h; exact Or.inr (digits_of_toDigits n.natAbs b (by rw [h]; simp))
        have hne : ∀ c : UInt8, c ∈ [0x22, 0x5B, 0x7B, 0x6E, 0x74, 0x66] → (b == c) = false := by
          intro c hc; simp only [beq_eq_false_iff_ne, ne_eq]; intro hbc; subst hbc
          rcases hb with hb | hb
          · subst hb; simp at hc
          · rw [isDigit_iff] at hb; simp at hc; rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hb
        simp only [List.cons_append, value, hne 0x22 (by simp), hne 0x5B (by simp), hne 0x7B (by simp),
          hne 0x6E (by simp), hne 0x74 (by simp), hne 0x66 (by simp), Bool.false_eq_true, ↓reduceIte]
        rw [← List.cons_append, hi]
      | @str s bs' hcs =>
        obtain ⟨s', hs, hl⟩ := chars_complete hcs f "" r (by simp at hlen; omega)
        simp only [String.toList_empty, List.nil_append] at hl
        rw [String.toList_inj.1 hl] at hs
        simp [value, hs]
      | @emptyArr w hw =>
        simp only [List.cons_append, List.append_assoc, List.nil_append, value]
        rw [skipWs_close _ hw (by decide)]
        simp
      | @arr items bs' hel =>
        obtain ⟨c, r', hc, hc'⟩ := elementsText_skip hel (0x5D :: r)
        simp only [List.cons_append, List.append_assoc, List.nil_append, value]
        rw [hc]
        simp only [hc', he _ _ _ _ hel (by simp at hlen; omega)]
        simp
      | @emptyObj w hw =>
        simp only [List.cons_append, List.append_assoc, List.nil_append, value]
        rw [skipWs_close _ hw (by decide)]
        simp
      | @obj ms bs' hme =>
        obtain ⟨r', hc⟩ := membersText_skip hme (0x7D :: r)
        simp only [List.cons_append, List.append_assoc, List.nil_append, value]
        rw [hc]
        simp only [hm _ _ _ _ hme (by simp at hlen; omega)]
        simp
    · intro items bs r acc h hlen
      cases h with
      | @one w₁ v bv w₂ hw₁ hbv hw₂ =>
        simp only [elements]
        rw [show w₁ ++ bv ++ w₂ ++ 0x5D :: r = w₁ ++ bv ++ (w₂ ++ 0x5D :: r) by simp, skipWs_value _ hw₁ hbv,
          hv _ _ _ hbv (by simp at hlen; omega) (noDigitHead_ws _ hw₂ (by decide))]
        dsimp only
        rw [skipWs_close _ hw₂ (by decide)]
        simp
      | @cons w₁ v bv w₂ vs rest hw₁ hbv hw₂ hrest =>
        have := valueText_length hbv
        simp only [elements]
        rw [show w₁ ++ bv ++ w₂ ++ 0x2C :: rest ++ 0x5D :: r = w₁ ++ bv ++ (w₂ ++ 0x2C :: (rest ++ 0x5D :: r)) by
            simp, skipWs_value _ hw₁ hbv,
          hv _ _ _ hbv (by simp at hlen; omega) (noDigitHead_ws _ hw₂ (by decide))]
        dsimp only
        rw [skipWs_close _ hw₂ (by decide)]
        simp only [show ((0x2C : UInt8) == 0x2C) = true from rfl, ↓reduceIte]
        rw [he _ _ _ _ hrest (by simp at hlen; omega)]
        simp
    · intro ms bs r acc h hlen
      cases h with
      | @one w₁ k ks w₂ w₃ v bv w₄ hw₁ hk hw₂ hw₃ hbv hw₄ =>
        obtain ⟨bk, rfl, hc⟩ := key_complete hk f (w₂ ++ 0x3A :: (w₃ ++ bv ++ (w₄ ++ 0x7D :: r)))
          (by simp at hlen ⊢; omega)
        simp only [members]
        rw [show w₁ ++ (0x22 :: bk ++ [0x22]) ++ w₂ ++ 0x3A :: w₃ ++ bv ++ w₄ ++ 0x7D :: r =
          w₁ ++ 0x22 :: (bk ++ 0x22 :: (w₂ ++ 0x3A :: (w₃ ++ bv ++ (w₄ ++ 0x7D :: r)))) by simp,
          skipWs_close _ hw₁ (by decide)]
        simp only [show ((0x22 : UInt8) == 0x22) = true from rfl, ↓reduceIte]
        rw [hc]
        dsimp only
        rw [skipWs_close _ hw₂ (by decide)]
        simp only [show ((0x3A : UInt8) == 0x3A) = true from rfl, ↓reduceIte]
        rw [skipWs_value _ hw₃ hbv, hv _ _ _ hbv (by simp at hlen; omega) (noDigitHead_ws _ hw₄ (by decide))]
        dsimp only
        rw [skipWs_close _ hw₄ (by decide)]
        simp
      | @cons w₁ k ks w₂ w₃ v bv w₄ ms' rest hw₁ hk hw₂ hw₃ hbv hw₄ hrest =>
        have := valueText_length hbv
        obtain ⟨bk, rfl, hc⟩ := key_complete hk f (w₂ ++ 0x3A :: (w₃ ++ bv ++ (w₄ ++ 0x2C :: (rest ++ 0x7D :: r))))
          (by simp at hlen ⊢; omega)
        simp only [members]
        rw [show w₁ ++ (0x22 :: bk ++ [0x22]) ++ w₂ ++ 0x3A :: w₃ ++ bv ++ w₄ ++ 0x2C :: rest ++ 0x7D :: r =
          w₁ ++ 0x22 :: (bk ++ 0x22 :: (w₂ ++ 0x3A :: (w₃ ++ bv ++ (w₄ ++ 0x2C :: (rest ++ 0x7D :: r))))) by simp,
          skipWs_close _ hw₁ (by decide)]
        simp only [show ((0x22 : UInt8) == 0x22) = true from rfl, ↓reduceIte]
        rw [hc]
        dsimp only
        rw [skipWs_close _ hw₂ (by decide)]
        simp only [show ((0x3A : UInt8) == 0x3A) = true from rfl, ↓reduceIte]
        rw [skipWs_value _ hw₃ hbv, hv _ _ _ hbv (by simp at hlen; omega) (noDigitHead_ws _ hw₄ (by decide))]
        dsimp only
        rw [skipWs_close _ hw₄ (by decide)]
        simp only [show ((0x2C : UInt8) == 0x2C) = true from rfl, ↓reduceIte]
        rw [hm _ _ _ _ hrest (by simp at hlen; omega)]
        simp

theorem parseList_complete {l : List UInt8} {v : Value} (h : Text l v) : parseList l = .ok v := by
  obtain ⟨w₁, bs, w₂, hw₁, hbs, hw₂, rfl⟩ := h
  simp only [parseList]
  rw [skipWs_value _ hw₁ hbs, (value_complete_all _).1 _ _ _ hbs (by simp; omega) (noDigitHead_ws_nil hw₂)]
  have : skipWs w₂ = [] := by simpa [skipWs] using skipWs_ws [] hw₂
  simp [this]

theorem text_unique' {l : List UInt8} {v w : Value} (hv : Text l v) (hw : Text l w) : v = w := by
  have := (parseList_complete hv).symm.trans (parseList_complete hw)
  simpa using this

end Airbender.Json.Parser
