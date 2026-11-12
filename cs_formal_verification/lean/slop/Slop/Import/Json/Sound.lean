module
public import Slop.Import.Json.Strings

@[expose] public section

/-! Soundness of the parser: what it accepts is a JSON text of the value it returns, without duplicate names. -/

namespace Airbender.Json.Parser
open Airbender.Json

theorem value_sound_all : ∀ f : Nat,
    (∀ l v r, value f l = .ok (v, r) → ∃ bs, ValueText v bs ∧ l = bs ++ r) ∧
    (∀ l acc vs r, elements f l acc = .ok (vs, r) →
      ∃ items bs, ElementsText items bs ∧ l = bs ++ 0x5D :: r ∧ vs = acc.reverse ++ items) ∧
    (∀ l acc ms r, members f l acc = .ok (ms, r) →
      ∃ mems bs, MembersText mems bs ∧ l = bs ++ 0x7D :: r ∧ ms = acc.reverse ++ mems)
  | 0 => ⟨by simp [value], by simp [elements], by simp [members]⟩
  | f + 1 => by
    obtain ⟨hv, he, hm⟩ := value_sound_all f
    refine ⟨?_, ?_, ?_⟩
    · intro l v r h
      match l with
      | [] => simp [value] at h
      | b :: t =>
        simp only [value] at h
        split at h
        · rename_i hb
          simp only [beq_iff_eq] at hb; subst hb
          split at h
          · rename_i s r' hc
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨cs, bs, hcs, rfl, hs⟩ := chars_sound _ _ _ _ _ hc
            simp only [String.toList_empty, List.nil_append] at hs
            exact ⟨_, .str (hs ▸ hcs), by simp⟩
          · simp at h
        split at h
        · rename_i hb
          simp only [beq_iff_eq] at hb; subst hb
          split at h
          · rename_i c r' hsk
            split at h
            · rename_i hc
              simp only [beq_iff_eq] at hc; subst hc
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨w, hw, ht⟩ := skipWs_sound t
              rw [hsk] at ht; subst ht
              exact ⟨_, .emptyArr hw, by simp⟩
            · split at h
              · rename_i vs r'' hel
                simp only [Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                obtain ⟨items, bs, hit, rfl, hvs⟩ := he _ _ _ _ hel
                simp only [List.reverse_nil, List.nil_append] at hvs; subst hvs
                exact ⟨_, .arr hit, by simp⟩
              · simp at h
          · simp at h
        split at h
        · rename_i hb
          simp only [beq_iff_eq] at hb; subst hb
          split at h
          · rename_i c r' hsk
            split at h
            · rename_i hc
              simp only [beq_iff_eq] at hc; subst hc
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨w, hw, ht⟩ := skipWs_sound t
              rw [hsk] at ht; subst ht
              exact ⟨_, .emptyObj hw, by simp⟩
            · split at h
              · rename_i ms r'' hme
                simp only [Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                obtain ⟨mems, bs, hme', rfl, hms⟩ := hm _ _ _ _ hme
                simp only [List.reverse_nil, List.nil_append] at hms; subst hms
                exact ⟨_, .obj hme', by simp⟩
              · simp at h
          · simp at h
        split at h
        · rename_i hb
          simp only [beq_iff_eq] at hb; subst hb
          split at h
          · rename_i r' hd
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨_, .null, by rw [utf8_null, dropPrefix_sound hd]; simp⟩
          · simp at h
        split at h
        · rename_i hb
          simp only [beq_iff_eq] at hb; subst hb
          split at h
          · rename_i r' hd
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨_, .true, by rw [utf8_true, dropPrefix_sound hd]; simp⟩
          · simp at h
        split at h
        · rename_i hb
          simp only [beq_iff_eq] at hb; subst hb
          split at h
          · rename_i r' hd
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨_, .false, by rw [utf8_false, dropPrefix_sound hd]; simp⟩
          · simp at h
        split at h
        · rename_i n r' hi
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨_, .int, int_sound hi⟩
        · simp at h
    · intro l acc vs r h
      simp only [elements] at h
      split at h
      · simp at h
      · rename_i v r₁ hval
        obtain ⟨bv, hbv, hl⟩ := hv _ _ _ hval
        obtain ⟨w₁, hw₁, e₁⟩ := skipWs_sound l
        rw [hl] at e₁; subst e₁
        split at h
        · rename_i c r₂ hsk
          obtain ⟨w₂, hw₂, e₂⟩ := skipWs_sound r₁
          rw [hsk] at e₂; subst e₂
          split at h
          · rename_i hc
            simp only [beq_iff_eq] at hc; subst hc
            obtain ⟨items, bs, hit, rfl, rfl⟩ := he _ _ _ _ h
            exact ⟨v :: items, _, .cons hw₁ hbv hw₂ hit, by simp, by simp⟩
          · split at h
            · rename_i hc
              simp only [beq_iff_eq] at hc; subst hc
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨[v], _, .one hw₁ hbv hw₂, by simp, by simp⟩
            · simp at h
        · simp at h
    · intro l acc ms r h
      simp only [members] at h
      split at h
      · rename_i c t hsk
        obtain ⟨w₁, hw₁, e₁⟩ := skipWs_sound l
        rw [hsk] at e₁; subst e₁
        split at h
        · rename_i hc
          simp only [beq_iff_eq] at hc; subst hc
          split at h
          · simp at h
          · rename_i k r₁ hk
            obtain ⟨cs, bk, hcs, rfl, hks⟩ := chars_sound _ _ _ _ _ hk
            simp only [String.toList_empty, List.nil_append] at hks
            have hkey : ValueText (.str k) (0x22 :: bk ++ [0x22]) := .str (hks ▸ hcs)
            split at h
            · rename_i c r₂ hsk₂
              obtain ⟨w₂, hw₂, e₂⟩ := skipWs_sound r₁
              rw [hsk₂] at e₂; subst e₂
              split at h
              · rename_i hc
                simp only [beq_iff_eq] at hc; subst hc
                split at h
                · simp at h
                · rename_i v r₃ hval
                  obtain ⟨bv, hbv, hl⟩ := hv _ _ _ hval
                  obtain ⟨w₃, hw₃, e₃⟩ := skipWs_sound r₂
                  rw [hl] at e₃; subst e₃
                  split at h
                  · rename_i c r₄ hsk₄
                    obtain ⟨w₄, hw₄, e₄⟩ := skipWs_sound r₃
                    rw [hsk₄] at e₄; subst e₄
                    split at h
                    · rename_i hc
                      simp only [beq_iff_eq] at hc; subst hc
                      obtain ⟨mems, bs, hme, rfl, rfl⟩ := hm _ _ _ _ h
                      exact ⟨(k, v) :: mems, _, .cons hw₁ hkey hw₂ hw₃ hbv hw₄ hme, by simp, by simp⟩
                    · split at h
                      · rename_i hc
                        simp only [beq_iff_eq] at hc; subst hc
                        simp only [Except.ok.injEq, Prod.mk.injEq] at h
                        obtain ⟨rfl, rfl⟩ := h
                        exact ⟨[(k, v)], _, .one hw₁ hkey hw₂ hw₃ hbv hw₄, by simp, by simp⟩
                      · simp at h
                  · simp at h
              · simp at h
            · simp at h
        · simp at h
      · simp at h

theorem parseList_sound {l : List UInt8} {v : Value} (h : parseList l = .ok v) : Text l v := by
  simp only [parseList] at h
  split at h
  · rename_i v' r hval
    split at h
    · rename_i hr
      simp only [Except.ok.injEq] at h; subst h
      obtain ⟨bs, hbs, hl⟩ := (value_sound_all _).1 _ _ _ hval
      obtain ⟨w₁, hw₁, e₁⟩ := skipWs_sound l
      obtain ⟨w₂, hw₂, e₂⟩ := skipWs_sound r
      simp only [List.isEmpty_iff] at hr
      rw [hr, List.append_nil] at e₂
      rw [hl, e₂] at e₁
      exact ⟨w₁, bs, w₂, hw₁, hbs, hw₂, by rw [e₁]; simp⟩
    · simp at h
  · simp at h

mutual
theorem noDup_sound : ∀ v : Value, noDup v = true → NoDuplicateKeys v
  | .null, _ => .null
  | .bool _, _ => .bool
  | .int _, _ => .int
  | .str _, _ => .str
  | .arr items, h => .arr (noDupItems_sound items (by simpa [noDup] using h))
  | .obj ms, h => by
    simp only [noDup, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .obj h.1 (noDupMembers_sound ms h.2)
theorem noDupItems_sound : ∀ items : List Value, noDupItems items = true → ∀ v ∈ items, NoDuplicateKeys v
  | [], _ => by simp
  | v :: vs, h => by
    simp only [noDupItems, Bool.and_eq_true] at h
    have hv := noDup_sound v h.1
    have hvs := noDupItems_sound vs h.2
    intro w hw
    simp only [List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact hv
    · exact hvs w hw
theorem noDupMembers_sound : ∀ ms : List (String × Value), noDupMembers ms = true →
    ∀ m ∈ ms, NoDuplicateKeys m.2
  | [], _ => by simp
  | (k, v) :: ms, h => by
    simp only [noDupMembers, Bool.and_eq_true] at h
    have hv := noDup_sound v h.1
    have hms := noDupMembers_sound ms h.2
    intro w hw
    simp only [List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact hv
    · exact hms w hw
end

theorem parse_sound' {bytes : ByteArray} {v : Value} (h : parse bytes = .ok v) :
    Text bytes.toList v ∧ NoDuplicateKeys v := by
  simp only [parse] at h
  split at h
  · rename_i v' hp
    split at h
    · rename_i hd
      simp only [Except.ok.injEq] at h; subst h
      exact ⟨byteArray_toList bytes ▸ parseList_sound hp, noDup_sound _ hd⟩
    · simp at h
  · simp at h

end Airbender.Json.Parser
