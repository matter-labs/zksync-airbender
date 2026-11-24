module
public import Human.Import.Exec.JsonParser
import all Init.Data.Int.Repr -- Int.repr is not exposed

@[expose] public section

/-! Lexical pieces of the JSON parser, each sound and complete for its grammar piece: whitespace, literals,
integers, characters and strings. -/

namespace Airbender.Json.Parser
open Airbender.Json

/-! ## Bytes and UTF-8 -/

theorem byteArray_loop_eq (b : ByteArray) :
    ∀ n i r, b.size - i = n → ByteArray.toList.loop b i r = r.reverse ++ b.data.toList.drop i
  | 0, i, r, h => by
    have hs : b.size = b.data.toList.length := by rfl
    rw [ByteArray.toList.loop]
    simp only [show ¬ i < b.size by omega, ↓reduceIte]
    rw [List.drop_eq_nil_of_le (by omega), List.append_nil]
  | n + 1, i, r, h => by
    have hs : b.size = b.data.toList.length := by rfl
    have hi : i < b.data.toList.length := by omega
    rw [ByteArray.toList.loop]
    simp only [show i < b.size by omega, ↓reduceIte]
    rw [byteArray_loop_eq b n (i + 1) _ (by omega)]
    conv => rhs; rw [List.drop_eq_getElem_cons hi]
    have : b.get! i = b.data.toList[i] := by
      simp only [ByteArray.get!]
      rw [getElem!_pos b.data i (by simpa using hi)]
      simp
    simp [this]

theorem byteArray_toList (b : ByteArray) : b.toList = b.data.toList := by
  simpa [ByteArray.toList] using byteArray_loop_eq b _ 0 [] rfl

theorem utf8_eq (s : String) : utf8 s = s.toList.flatMap String.utf8EncodeChar := by
  rw [utf8, byteArray_toList, String.toUTF8_eq_toByteArray, ← String.ofList_toList (s := s),
    String.toByteArray_ofList, String.toList_ofList, List.utf8Encode, List.toList_data_toByteArray]

theorem utf8_char (c : Char) : utf8 c.toString = String.utf8EncodeChar c := by
  simp [utf8_eq, Char.toString, String.toList_singleton]

theorem utf8_append (s t : String) : utf8 (s ++ t) = utf8 s ++ utf8 t := by
  simp [utf8_eq, String.toList_append]

theorem char_toNat_le (c : Char) : c.toNat ≤ 0x10ffff := by
  have := c.valid; simp only [UInt32.isValidChar, Nat.isValidChar] at this
  show c.val.toNat ≤ _; omega

theorem char_toUInt8 (c : Char) : c.toUInt8.toNat = c.toNat % 256 := UInt32.toNat_toUInt8 c.val

theorem char_ne_iff {c d : Char} : c ≠ d ↔ c.toNat ≠ d.toNat := by
  constructor
  · intro h h'; exact h (Char.ext (UInt32.toNat_inj.1 h'))
  · intro h h'; exact h (h' ▸ rfl)

theorem ofNat_byte (b : UInt8) (h : b.toNat < 128) : (Char.ofNat b.toNat).toNat = b.toNat := by
  rw [Char.ofNat, dite_eq_left_of_eq_true (eq_true (by unfold Nat.isValidChar; omega))]
  simp [Char.ofNatAux, Char.toNat]

/-- The first byte of a character's encoding: the character itself below U+0080, at least 0x80 otherwise. -/
theorem encode_head (c : Char) :
    ∃ b t, String.utf8EncodeChar c = b :: t ∧
      ((c.toNat < 128 ∧ b.toNat = c.toNat) ∨ (128 ≤ c.toNat ∧ 128 ≤ b.toNat)) := by
  have hc := char_toNat_le c
  simp only [String.utf8EncodeChar, Char.toNat_val]
  split
  · exact ⟨_, _, rfl, Or.inl ⟨by omega, by simp only [UInt8.toNat_ofNat']; omega⟩⟩
  · split
    · exact ⟨_, _, rfl, Or.inr ⟨by omega, by simp only [UInt8.toNat_ofNat']; omega⟩⟩
    · split
      · exact ⟨_, _, rfl, Or.inr ⟨by omega, by simp only [UInt8.toNat_ofNat']; omega⟩⟩
      · exact ⟨_, _, rfl, Or.inr ⟨by omega, by simp only [UInt8.toNat_ofNat']; omega⟩⟩

theorem encode_ascii (c : Char) (h : c.toNat < 128) : String.utf8EncodeChar c = [c.toUInt8] :=
  String.utf8EncodeChar_eq_singleton (Char.utf8Size_eq_one_iff.2 (by
    rw [UInt32.le_iff_toNat_le]; exact Nat.le_of_lt_succ h))

theorem rawChar_sound {l r : List UInt8} {c : Char} (h : rawChar? l = some (c, r)) :
    l = String.utf8EncodeChar c ++ r := by
  match l with
  | [] => simp [rawChar?] at h
  | b :: t =>
    simp only [rawChar?] at h
    split at h
    · rename_i hb
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hb' : b.toNat < 128 := by simpa [UInt8.lt_iff_toNat_lt] using hb
      have hv := ofNat_byte b hb'
      rw [encode_ascii _ (by omega)]
      simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true]
      apply UInt8.toNat_inj.1
      rw [char_toUInt8, hv]; omega
    · split at h
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rename_i hp
          obtain ⟨u, hu⟩ := (List.isPrefixOf_iff_prefix.1 hp)
          rw [← hu]; simp
        · simp at h
      · simp at h

theorem rawChar_complete (c : Char) (t : List UInt8) :
    rawChar? (String.utf8EncodeChar c ++ t) = some (c, t) := by
  obtain ⟨b, u, he, hb⟩ := encode_head c
  rcases hb with ⟨hc, hb⟩ | ⟨hc, hb⟩
  · rw [encode_ascii c hc] at he ⊢
    simp only [List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    simp only [List.cons_append, List.nil_append, rawChar?]
    have h8 : c.toUInt8.toNat = c.toNat := by rw [char_toUInt8]; omega
    rw [ite_eq_left (by simp only [UInt8.lt_iff_toNat_lt]; rw [h8]; exact hc)]
    rw [h8, Char.ofNat_toNat]
  · rw [he]
    simp only [List.cons_append, rawChar?]
    rw [ite_eq_right (by simp only [UInt8.lt_iff_toNat_lt]; simp; omega)]
    rw [← List.cons_append, ← he]
    have hlen : (String.utf8EncodeChar c).length ≤ 4 := by
      rw [String.length_utf8EncodeChar]; exact Char.utf8Size_le_four c
    rw [List.take_append, List.take_of_length_le hlen, List.toByteArray_append,
      ByteArray.utf8DecodeChar?_utf8EncodeChar_append]
    simp

/-! ## Whitespace -/

theorem isWs_iff (b : UInt8) : isWs b = true ↔ (b = 0x20 ∨ b = 0x09 ∨ b = 0x0A ∨ b = 0x0D) := by
  simp [isWs, or_assoc]

theorem skipWs_sound : ∀ l : List UInt8, ∃ w, Ws w ∧ l = w ++ skipWs l
  | [] => ⟨[], by simp [Ws], rfl⟩
  | b :: l => by
    by_cases h : isWs b = true
    · obtain ⟨w, hw, he⟩ := skipWs_sound l
      refine ⟨b :: w, ?_, ?_⟩
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact (isWs_iff x).1 h
        · exact hw x hx
      · simp only [skipWs, h, ite_true, List.cons_append]; exact congrArg _ he
    · exact ⟨[], by simp [Ws], by simp [skipWs, h]⟩

theorem skipWs_ws : ∀ {w : List UInt8} (l : List UInt8), Ws w → skipWs (w ++ l) = skipWs l
  | [], _, _ => rfl
  | b :: w, l, h => by
    have hb : isWs b = true := (isWs_iff b).2 (h b (by simp))
    simp only [List.cons_append, skipWs, hb, ite_true]
    exact skipWs_ws l (fun x hx => h x (by simp [hx]))

theorem skipWs_of_not_ws {b : UInt8} (l : List UInt8) (h : isWs b = false) : skipWs (b :: l) = b :: l := by
  simp [skipWs, h]

/-- After `skipWs`, the input does not start with whitespace. -/
theorem skipWs_head : ∀ (l : List UInt8) (b : UInt8) (r : List UInt8), skipWs l = b :: r → isWs b = false
  | [], _, _, h => by simp [skipWs] at h
  | c :: l, b, r, h => by
    by_cases hc : isWs c = true
    · simp only [skipWs, hc, ite_true] at h; exact skipWs_head l b r h
    · simp only [skipWs, hc] at h
      simp only [Bool.false_eq_true, ite_false, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simpa using hc

/-! ## Literals -/

theorem dropPrefix_sound : ∀ {p l r : List UInt8}, dropPrefix? p l = some r → l = p ++ r
  | [], l, r, h => by simp [dropPrefix?] at h; simp [h]
  | _ :: _, [], _, h => by simp [dropPrefix?] at h
  | q :: p, b :: l, r, h => by
    simp only [dropPrefix?] at h
    split at h
    · rename_i hq; simp at hq; subst hq; simp [dropPrefix_sound h]
    · simp at h

theorem dropPrefix_complete : ∀ (p r : List UInt8), dropPrefix? p (p ++ r) = some r
  | [], _ => rfl
  | q :: p, r => by simp [dropPrefix?, dropPrefix_complete p r]

theorem utf8_null : utf8 "null" = 0x6E :: nullTail := by simp [utf8_eq, nullTail]; decide
theorem utf8_true : utf8 "true" = 0x74 :: trueTail := by simp [utf8_eq, trueTail]; decide
theorem utf8_false : utf8 "false" = 0x66 :: falseTail := by simp [utf8_eq, falseTail]; decide

/-! ## Integers -/

theorem isDigit_iff (b : UInt8) : isDigit b = true ↔ 48 ≤ b.toNat ∧ b.toNat ≤ 57 := by
  simp [isDigit, UInt8.le_iff_toNat_le]

theorem isDigit_char {c : Char} (h : c.isDigit = true) : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  simpa [Char.isDigit, UInt32.le_iff_toNat_le] using h

theorem flatMap_digits : ∀ (cs : List Char), (∀ c ∈ cs, c.isDigit = true) →
    cs.flatMap String.utf8EncodeChar = cs.map Char.toUInt8
  | [], _ => rfl
  | c :: cs, h => by
    have hc := isDigit_char (h c (by simp))
    rw [List.flatMap_cons, encode_ascii c (by omega), flatMap_digits cs (fun d hd => h d (by simp [hd]))]
    rfl

theorem toDigits_isDigit (n : Nat) : ∀ c ∈ Nat.toDigits 10 n, c.isDigit = true := fun _ hc =>
  Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc

/-- The decimal digits of `n`, as bytes. -/
theorem utf8_nat (n : Nat) : utf8 (toString n) = (Nat.toDigits 10 n).map Char.toUInt8 := by
  rw [utf8_eq, show (toString n).toList = Nat.toDigits 10 n from Nat.toList_repr]
  exact flatMap_digits _ (toDigits_isDigit n)

theorem digits_of_toDigits (n : Nat) : ∀ b ∈ utf8 (toString n), isDigit b = true := by
  rw [utf8_nat]
  intro b hb
  simp only [List.mem_map] at hb
  obtain ⟨c, hc, rfl⟩ := hb
  have := isDigit_char (toDigits_isDigit n c hc)
  rw [isDigit_iff, char_toUInt8]; omega

theorem digitsValue_foldl : ∀ (cs : List Char), (∀ c ∈ cs, c.isDigit = true) → ∀ init : Nat,
    (cs.map Char.toUInt8).foldl (fun n d => 10 * n + (d - 0x30).toNat) init = Nat.ofDigitChars 10 cs init
  | [], _, _ => by simp
  | c :: cs, h, init => by
    have hc := isDigit_char (h c (by simp))
    simp only [List.map_cons, List.foldl_cons]
    rw [digitsValue_foldl cs (fun d hd => h d (by simp [hd])), Nat.ofDigitChars_cons]
    have h8 := char_toUInt8 c
    have : (c.toUInt8 - 0x30).toNat = c.toNat - '0'.toNat := by
      rw [UInt8.toNat_sub_of_le _ _ (by rw [UInt8.le_iff_toNat_le, h8]; simp; omega), h8]
      simp; omega
    rw [this]

theorem digitsValue_utf8 (n : Nat) : digitsValue (utf8 (toString n)) = n := by
  rw [digitsValue, utf8_nat, digitsValue_foldl _ (toDigits_isDigit n)]
  exact Nat.ofDigitChars_ten_toDigits

theorem utf8_nat_ne_nil (n : Nat) : utf8 (toString n) ≠ [] := by
  rw [utf8_nat]; simp [Nat.toDigits_ne_nil]

theorem utf8_int (n : Int) :
    utf8 (toString n) = if n < 0 then 0x2D :: utf8 (toString n.natAbs) else utf8 (toString n.natAbs) := by
  show utf8 (Int.repr n) = _
  cases n with
  | ofNat m => simp [Int.repr]
  | negSucc m =>
    simp only [Int.repr, Int.negSucc_lt_zero, ite_true]
    rw [utf8_append]
    simp [utf8_eq]; rfl

/-- Taking the digit run of a digit list followed by a non-digit. -/
theorem takeWhile_digits {ds r : List UInt8} (hd : ∀ b ∈ ds, isDigit b = true)
    (hr : ∀ b ∈ r.head?, isDigit b = false) :
    (ds ++ r).takeWhile isDigit = ds ∧ (ds ++ r).dropWhile isDigit = r := by
  constructor
  · rw [List.takeWhile_append_of_pos hd]
    cases r with
    | nil => simp
    | cons b r => simp at hr; simp [hr]
  · induction ds with
    | nil => cases r with
      | nil => simp
      | cons b r => simp at hr; simp [hr]
    | cons d ds ih =>
      simp only [List.cons_append, List.dropWhile_cons, hd d (by simp), ite_true]
      exact ih (fun b hb => hd b (by simp [hb]))

theorem int_sound {l r : List UInt8} {n : Int} (h : int? l = some (n, r)) : l = utf8 (toString n) ++ r := by
  match l with
  | [] => simp [int?] at h
  | b :: t =>
    simp only [int?] at h
    split at h
    · split at h
      · rename_i hb heq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp at hb; subst hb
        rw [beq_iff_eq.1 heq]; simp
      · simp at h
    · split at h
      · rename_i heq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [beq_iff_eq.1 heq]; simp
      · simp at h

theorem int_complete (n : Int) {r : List UInt8} (hr : ∀ b ∈ r.head?, isDigit b = false) :
    int? (utf8 (toString n) ++ r) = some (n, r) := by
  have hd := digits_of_toDigits n.natAbs
  obtain ⟨ht, hdrop⟩ := takeWhile_digits hd hr
  rw [utf8_int]
  split
  · rename_i hn
    simp only [List.cons_append, int?, show ((0x2D : UInt8) == 0x2D) = true from rfl, ite_true]
    rw [ht, hdrop, digitsValue_utf8]
    have : -(n.natAbs : Int) = n := by omega
    rw [this, utf8_int, ite_eq_left hn]
    simp
  · rename_i hn
    obtain ⟨b, t, hbt⟩ : ∃ b t, utf8 (toString n.natAbs) = b :: t := by
      cases h : utf8 (toString n.natAbs) with
      | nil => exact absurd h (utf8_nat_ne_nil _)
      | cons b t => exact ⟨b, t, rfl⟩
    have hb : isDigit b = true := hd b (by rw [hbt]; simp)
    have hb' : (b == 0x2D) = false := by
      rw [isDigit_iff] at hb; simp; intro h; subst h; simp at hb
    rw [hbt]
    simp only [List.cons_append, int?, hb', Bool.false_eq_true, ite_false]
    rw [← List.cons_append, ← hbt, ht, hdrop, digitsValue_utf8]
    have : ((n.natAbs : Nat) : Int) = n := by omega
    rw [this, utf8_int, ite_eq_right hn]
    simp

end Airbender.Json.Parser
