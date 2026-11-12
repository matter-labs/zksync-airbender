module
public import Slop.Import.Json.Lexical

@[expose] public section

/-! Strings: one character (`CharText`) and the characters up to the closing quote (`CharsText`), sound and
complete. -/

namespace Airbender.Json.Parser
open Airbender.Json

theorem hexChar_sound {a b c d : UInt8} {ch : Char} (h : hexChar? a b c d = some ch) :
    CharText ch [0x5C, 0x75, a, b, c, d] := by
  unfold hexChar? at h
  split at h
  · rename_i d₃ d₂ d₁ d₀ h₃ h₂ h₁ h₀
    dsimp only at h
    split at h
    · rename_i hv
      simp only [Option.some.injEq] at h
      subst h
      refine CharText.unicode (ds := [a, b, c, d]) (d₃ := d₃) (d₂ := d₂) (d₁ := d₁) (d₀ := d₀) ?_ ?_ ?_
      · rw [UInt32.lt_iff_toNat_lt]; simp [Char.ofNatAux]; omega
      · simp [h₃, h₂, h₁, h₀]
      · simp [Char.ofNatAux]; omega
    · simp at h
  · simp at h

theorem hexChar_complete {c : Char} {ds : List UInt8} {d₃ d₂ d₁ d₀ : Nat} (hc : c.val < 0x10000)
    (hm : ds.map hexDigit? = [some d₃, some d₂, some d₁, some d₀])
    (hv : c.val.toNat = ((d₃ * 16 + d₂) * 16 + d₁) * 16 + d₀) :
    ∃ a b c' d, ds = [a, b, c', d] ∧ hexChar? a b c' d = some c := by
  rcases ds with _ | ⟨a, _ | ⟨b, _ | ⟨c', _ | ⟨d, _ | ⟨e, ds⟩⟩⟩⟩⟩ <;> simp at hm
  obtain ⟨h₃, h₂, h₁, h₀⟩ := hm
  refine ⟨a, b, c', d, rfl, ?_⟩
  have hv' : c.toNat = ((d₃ * 16 + d₂) * 16 + d₁) * 16 + d₀ := hv
  have hlt : c.toNat < 0x10000 := by rw [UInt32.lt_iff_toNat_lt] at hc; exact hc
  have hval := c.valid
  simp only [UInt32.isValidChar, Nat.isValidChar] at hval
  have hval' : c.toNat < 0xd800 ∨ (0xdfff < c.toNat ∧ c.toNat < 0x110000) := hval
  unfold hexChar?
  simp only [h₃, h₂, h₁, h₀]
  rw [dite_eq_left_of_eq_true (eq_true (by omega))]
  simp only [Option.some.injEq]
  apply Char.ext; apply UInt32.toNat_inj.1
  simp [Char.ofNatAux]; omega

theorem unescape_sound {e : UInt8} {c : Char} (h : unescape? e = some c) : (c, e) ∈ shortEscapes := by
  simp only [unescape?, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl⟩ := h
  have hm := List.mem_of_find?_eq_some hp
  have he := List.find?_some hp
  simp only [beq_iff_eq] at he
  rw [← he]; exact hm

theorem unescape_complete {c : Char} {e : UInt8} (h : (c, e) ∈ shortEscapes) :
    unescape? e = some c ∧ e ≠ 0x75 := by
  simp only [shortEscapes, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;> decide

theorem charText_ne_nil {c : Char} {bc : List UInt8} (h : CharText c bc) : bc ≠ [] := by
  cases h with
  | raw => rw [utf8_char]; obtain ⟨b, t, he, -⟩ := encode_head c; simp [he]
  | short => simp
  | unicode => simp

theorem chars_step (f : Nat) (acc : String) {c : Char} {bc : List UInt8} (hc : CharText c bc)
    (t : List UInt8) : chars (f + 1) acc (bc ++ t) = chars f (acc.push c) t := by
  cases hc with
  | raw h₁ h₂ h₃ =>
    rw [utf8_char]
    obtain ⟨b, u, he, hb⟩ := encode_head c
    have h₂' := char_ne_iff.1 h₂
    have h₃' := char_ne_iff.1 h₃
    have hq : (b == 0x22) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro hb'; subst hb'
      rcases hb with ⟨_, hb⟩ | ⟨_, hb⟩ <;> simp at hb <;> simp_all <;> omega
    have hs : (b == 0x5C) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro hb'; subst hb'
      rcases hb with ⟨_, hb⟩ | ⟨_, hb⟩ <;> simp at hb <;> simp_all <;> omega
    rw [he]
    simp only [List.cons_append, chars, hq, hs, Bool.false_eq_true, ↓reduceIte]
    rw [← List.cons_append, ← he, rawChar_complete]
    have h₁' : (0x20 ≤ c.val) = True := eq_true h₁
    simp [h₁, h₂, h₃]
  | short hm =>
    obtain ⟨hu, he⟩ := unescape_complete hm
    simp [chars, hu, he]
  | unicode hlt hm hv =>
    obtain ⟨a, b, c', d, rfl, hh⟩ := hexChar_complete hlt hm hv
    simp [chars, hh]

theorem chars_complete {cs : List Char} {bs : List UInt8} (h : CharsText cs bs) :
    ∀ (f : Nat) (acc : String) (r : List UInt8), bs.length < f →
      ∃ s, chars f acc (bs ++ 0x22 :: r) = .ok (s, r) ∧ s.toList = acc.toList ++ cs := by
  induction h with
  | nil =>
    intro f acc r hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp at hf; omega⟩
    exact ⟨acc, by simp [chars], by simp⟩
  | @cons c bc cs rest hc _ ih =>
    intro f acc r hf
    have hne := charText_ne_nil hc
    have hlen : 1 ≤ bc.length := by cases bc <;> simp_all
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp at hf; omega⟩
    obtain ⟨s, hs, hl⟩ := ih f (acc.push c) r (by simp at hf; omega)
    refine ⟨s, ?_, ?_⟩
    · rw [List.append_assoc, chars_step f acc hc, hs]
    · rw [hl, String.toList_push]; simp

theorem chars_sound : ∀ (f : Nat) (acc : String) (l r : List UInt8) (s : String),
    chars f acc l = .ok (s, r) →
      ∃ cs bs, CharsText cs bs ∧ l = bs ++ 0x22 :: r ∧ s.toList = acc.toList ++ cs
  | 0, _, _, _, _, h => by simp [chars] at h
  | _ + 1, _, [], _, _, h => by simp [chars] at h
  | f + 1, acc, b :: t, r, s, h => by
    simp only [chars] at h
    split at h
    · rename_i hb
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [beq_iff_eq] at hb; subst hb
      exact ⟨[], [], .nil, rfl, by simp⟩
    · split at h
      · rename_i hb
        simp only [beq_iff_eq] at hb; subst hb
        split at h
        · rename_i e t
          split at h
          · rename_i he
            simp only [beq_iff_eq] at he; subst he
            split at h
            · rename_i h₃ h₂ h₁ h₀ t
              split at h
              · rename_i c hh
                obtain ⟨cs, bs, hcs, hl, hs⟩ := chars_sound f _ _ _ _ h
                refine ⟨c :: cs, [0x5C, 0x75, h₃, h₂, h₁, h₀] ++ bs, .cons (hexChar_sound hh) hcs, ?_, ?_⟩
                · simp [hl]
                · rw [hs, String.toList_push]; simp
              · simp at h
            · simp at h
          · split at h
            · rename_i c hu
              obtain ⟨cs, bs, hcs, hl, hs⟩ := chars_sound f _ _ _ _ h
              refine ⟨c :: cs, [0x5C, e] ++ bs, .cons (.short (unescape_sound hu)) hcs, ?_, ?_⟩
              · simp [hl]
              · rw [hs, String.toList_push]; simp
            · simp at h
        · simp at h
      · split at h
        · rename_i c t' hr
          split at h
          · rename_i hok
            simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hok
            obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hok
            obtain ⟨cs, bs, hcs, hl, hs⟩ := chars_sound f _ _ _ _ h
            refine ⟨c :: cs, utf8 c.toString ++ bs, .cons (.raw h₁ h₂ h₃) hcs, ?_, ?_⟩
            · rw [rawChar_sound hr, hl, utf8_char]; simp
            · rw [hs, String.toList_push]; simp
          · simp at h
        · simp at h

end Airbender.Json.Parser
