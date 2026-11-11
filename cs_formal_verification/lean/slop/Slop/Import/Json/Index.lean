module
public import Slop.Import.Json.Lexical

@[expose] public section

/-! The index parser (`parse`, Human/Import/Exec/JsonParser.lean) returns what the list parser returns
(`parseReference`, ListParser.lean): each function at index `i` agrees with its list counterpart on the bytes from
`i` on (`suffix a i`), the returned index standing for the bytes after it. -/

namespace Airbender.Json.Parser
open Airbender.Json


/-- The input from index `i` on. -/
abbrev suffix (a : ByteArray) (i : Nat) : List UInt8 := a.data.toList.drop i

theorem suffix_lt {a : ByteArray} {i : Nat} (h : i < a.size) : suffix a i = a[i] :: suffix a (i + 1) := by
  have h' : i < a.data.toList.length := by simpa using h
  rw [suffix, List.drop_eq_getElem_cons h']
  simp [ByteArray.getElem_eq_getElem_data]

theorem suffix_ge {a : ByteArray} {i : Nat} (h : a.size ≤ i) : suffix a i = [] :=
  List.drop_eq_nil_of_le (by simpa using h)

theorem suffix_add (a : ByteArray) (i k : Nat) : suffix a (i + k) = (suffix a i).drop k := by
  simp [suffix, List.drop_drop]

theorem extract_toList (a : ByteArray) (i j : Nat) : (a.extract i j).data.toList = (suffix a i).take (j - i) := by
  simp

theorem beq_iff {x y : ByteArray} : (x == y) = true ↔ x = y := by
  constructor
  · intro h
    have : (x.data == y.data) = true := h
    exact ByteArray.ext (by simpa using this)
  · rintro rfl
    show (x.data == x.data) = true
    simp

/-- The `l.length` bytes at `i` are `l`. -/
theorem extract_beq {a : ByteArray} {i k : Nat} {l : List UInt8}
    (h : (a.extract i (i + k) == l.toByteArray) = true) : suffix a i = l ++ suffix a (i + k) := by
  have h1 := congrArg (fun x : ByteArray => x.data.toList) (beq_iff.1 h)
  simp only [extract_toList, Nat.add_sub_cancel_left, List.data_toByteArray, List.toList_toArray] at h1
  rw [suffix_add, ← h1, List.take_append_drop]

theorem extract_beq_of {a : ByteArray} {i k : Nat} {l r : List UInt8} (hk : l.length = k)
    (h : suffix a i = l ++ r) : (a.extract i (i + k) == l.toByteArray) = true := by
  apply beq_iff.2
  apply ByteArray.ext
  apply Array.toList_inj.1
  simp only [extract_toList, Nat.add_sub_cancel_left, List.data_toByteArray, List.toList_toArray]
  rw [h, ← hk, List.take_left]


/-! ### Whitespace -/

/-- From `i` to `j` there are only spaces. -/
def Spaces (a : ByteArray) (i j : Nat) : Prop := i ≤ j ∧ ∃ m, suffix a i = List.replicate m 0x20 ++ suffix a j

theorem Spaces.refl (a : ByteArray) (i : Nat) : Spaces a i i := ⟨Nat.le_refl i, 0, rfl⟩

theorem Spaces.trans {a : ByteArray} {i j k : Nat} (h₁ : Spaces a i j) (h₂ : Spaces a j k) : Spaces a i k := by
  obtain ⟨hij, m, hm⟩ := h₁
  obtain ⟨hjk, n, hn⟩ := h₂
  exact ⟨Nat.le_trans hij hjk, m + n, by rw [hm, hn, ← List.append_assoc, List.replicate_append_replicate]⟩

theorem spaces_chunk {a : ByteArray} {i k : Nat} (h : (a.extract i (i + k) == spaces k) = true) :
    Spaces a i (i + k) :=
  ⟨Nat.le_add_right i k, k, extract_beq h⟩

theorem stepIf_spaces (a : ByteArray) (k i : Nat) : Spaces a i (stepIf a k (spaces k) i) := by
  unfold stepIf
  split
  · exact spaces_chunk ‹_›
  · exact Spaces.refl a i

theorem spaceAt_spaces (a : ByteArray) (i : Nat) : Spaces a i (spaceAt a i) := by
  unfold spaceAt
  split
  · rename_i hj
    split
    · rename_i hb
      refine ⟨Nat.le_add_right _ 1, 1, ?_⟩
      rw [suffix_lt hj, beq_iff_eq.1 hb]; rfl
    · exact Spaces.refl a _
  · exact Spaces.refl a _

theorem spacesAt_spaces (a : ByteArray) (i : Nat) : Spaces a i (spacesAt a i) := by
  rw [spacesAt]
  split
  · rename_i h
    exact (spaces_chunk h.2).trans (spacesAt_spaces a (i + 64))
  · have h₁ := (((((stepIf_spaces a 32 i).trans (stepIf_spaces a 16 _)).trans (stepIf_spaces a 8 _)).trans
      (stepIf_spaces a 4 _)).trans (stepIf_spaces a 2 _))
    exact h₁.trans (spaceAt_spaces a _)
termination_by a.size - i
decreasing_by omega

theorem skipWs_spaces {a : ByteArray} {i j : Nat} (h : Spaces a i j) : skipWs (suffix a i) = skipWs (suffix a j) := by
  obtain ⟨_, m, hm⟩ := h
  rw [hm, skipWs_ws _ (fun b hb => by rw [List.eq_of_mem_replicate hb]; exact Or.inl rfl)]

theorem skipWsAt_eq (a : ByteArray) (i : Nat) : suffix a (skipWsAt a i) = skipWs (suffix a i) := by
  rw [skipWsAt]
  split
  · rename_i hi
    rw [suffix_lt hi]
    dsimp only
    split
    · rename_i hw
      have hs := spacesAt_spaces a (i + 1)
      simp only [skipWs, hw, ite_true]
      have hlt : i < spacesAt a (i + 1) := by have := hs.1; omega
      simp only [hlt, ↓reduceIte]
      rw [skipWsAt_eq a (spacesAt a (i + 1)), skipWs_spaces hs]
    · rename_i hw
      rw [skipWs_of_not_ws _ (by simpa using hw), ← suffix_lt hi]
  · rename_i hi
    rw [suffix_ge (by omega)]; rfl
termination_by a.size - i
decreasing_by have := (spacesAt_spaces a (i + 1)).1; omega


/-! ### Integers -/

theorem digitsAt_eq (a : ByteArray) (i acc : Nat) :
    digitsAt a i acc = (i + ((suffix a i).takeWhile isDigit).length,
      ((suffix a i).takeWhile isDigit).foldl (fun n d => 10 * n + (d - 0x30).toNat) acc) := by
  rw [digitsAt]
  split
  · rename_i hi
    dsimp only
    rw [suffix_lt hi]
    split
    · rename_i hd
      rw [digitsAt_eq a (i + 1)]
      simp [hd, Nat.add_assoc, Nat.add_comm 1]
    · rename_i hd
      simp [hd]
  · rename_i hi
    rw [suffix_ge (by omega)]; simp
termination_by a.size - i

/-- The bytes from `i` to `i + k` are a prefix `p` of the input from `i`, of length `k`. -/
theorem toUTF8_beq_extract {a : ByteArray} {i k : Nat} {s : String} {p : List UInt8}
    (hp : (suffix a i).take k = p) : (s.toUTF8 == a.extract i (i + k)) = (utf8 s == p) := by
  have he : (a.extract i (i + k)).data.toList = (suffix a i).take k := by
    rw [extract_toList, Nat.add_sub_cancel_left]
  rw [Bool.eq_iff_iff, beq_iff, beq_iff_eq, utf8, byteArray_toList, ← hp, ← he]
  constructor
  · intro h; rw [h]
  · intro h; exact ByteArray.ext (Array.toList_inj.1 h)

theorem take_takeWhile (l : List UInt8) : l.take (l.takeWhile isDigit).length = l.takeWhile isDigit :=
  calc l.take (l.takeWhile isDigit).length
      = (l.takeWhile isDigit ++ l.dropWhile isDigit).take (l.takeWhile isDigit).length := by
        rw [List.takeWhile_append_dropWhile]
    _ = l.takeWhile isDigit := List.take_left

theorem drop_takeWhile (l : List UInt8) : l.drop (l.takeWhile isDigit).length = l.dropWhile isDigit :=
  calc l.drop (l.takeWhile isDigit).length
      = (l.takeWhile isDigit ++ l.dropWhile isDigit).drop (l.takeWhile isDigit).length := by
        rw [List.takeWhile_append_dropWhile]
    _ = l.dropWhile isDigit := List.drop_left

/-- The position form of an optional result. -/
def restO (a : ByteArray) {α : Type} (r : Option (α × Nat)) : Option (α × List UInt8) := r.map fun p => (p.1, suffix a p.2)

theorem intAt_eq (a : ByteArray) (i : Nat) : restO a (intAt a i) = int? (suffix a i) := by
  unfold intAt
  split
  · rename_i hi
    rw [suffix_lt hi]
    simp only [int?]
    split
    · rename_i hb
      rw [digitsAt_eq]
      dsimp only
      rw [show i + 1 + ((suffix a (i + 1)).takeWhile isDigit).length =
        i + (1 + ((suffix a (i + 1)).takeWhile isDigit).length) by omega,
        toUTF8_beq_extract (p := 0x2D :: (suffix a (i + 1)).takeWhile isDigit)
          (by rw [suffix_lt hi, Nat.add_comm, List.take_succ_cons, take_takeWhile, beq_iff_eq.1 hb])]
      simp only [digitsValue]
      split
      · rename_i hc
        simp only [hc, ↓reduceIte, restO, Option.map_some]
        rw [← Nat.add_assoc, suffix_add a (i + 1), drop_takeWhile]
      · rename_i hc
        simp only [hc, Bool.false_eq_true, ↓reduceIte, restO, Option.map_none]
    · rw [digitsAt_eq, ← suffix_lt hi]
      dsimp only
      rw [toUTF8_beq_extract (p := (suffix a i).takeWhile isDigit) (take_takeWhile _)]
      simp only [digitsValue]
      split
      · rename_i hc
        simp only [hc, ↓reduceIte, restO, Option.map_some]
        rw [suffix_add a i, drop_takeWhile]
      · rename_i hc
        simp only [hc, Bool.false_eq_true, ↓reduceIte, restO, Option.map_none]
  · rename_i hi
    rw [suffix_ge (by omega)]; rfl


/-! ### Characters and strings -/

theorem extract_eq_toByteArray (a : ByteArray) (i k : Nat) :
    a.extract i (i + k) = ((suffix a i).take k).toByteArray :=
  ByteArray.ext (Array.toList_inj.1 (by
    rw [extract_toList, Nat.add_sub_cancel_left, List.data_toByteArray, List.toList_toArray]))

theorem isPrefixOf_take {p l : List UInt8} {n : Nat} (h : p.length ≤ n) :
    p.isPrefixOf (l.take n) = p.isPrefixOf l := by
  rw [Bool.eq_iff_iff, List.isPrefixOf_iff_prefix, List.isPrefixOf_iff_prefix, List.prefix_take_iff]
  exact ⟨fun h' => h'.1, fun h' => ⟨h', h⟩⟩

theorem rawCharAt_eq (a : ByteArray) (i : Nat) : restO a (rawCharAt a i) = rawChar? (suffix a i) := by
  unfold rawCharAt
  by_cases hi : i < a.size
  · simp only [hi, ↓reduceDIte]
    rw [suffix_lt hi]
    simp only [rawChar?]
    by_cases hb : a[i] < 0x80
    · simp only [hb, ↓reduceIte, restO, Option.map_some]
    · simp only [hb, ↓reduceIte]
      rw [← suffix_lt hi, extract_eq_toByteArray]
      cases ((suffix a i).take 4).toByteArray.utf8DecodeChar? 0 with
      | none => rfl
      | some c =>
        simp only
        rw [List.data_toByteArray, List.toList_toArray, isPrefixOf_take (by
          rw [String.length_utf8EncodeChar]; exact Char.utf8Size_le_four c)]
        by_cases hp : (String.utf8EncodeChar c).isPrefixOf (suffix a i)
        · simp only [hp, ↓reduceIte, restO, Option.map_some]
          rw [suffix_add]
        · simp only [hp, Bool.false_eq_true, ↓reduceIte, restO, Option.map_none]
  · simp only [hi, ↓reduceDIte]
    rw [suffix_ge (by omega)]; rfl

/-- The position form of a result. -/
def restE (a : ByteArray) {α : Type} : Except String (α × Nat) → Except String (α × List UInt8)
  | .ok (x, j) => .ok (x, suffix a j)
  | .error e => .error e

theorem charsAt_eq (a : ByteArray) : ∀ f acc i, restE a (charsAt a f acc i) = chars f acc (suffix a i)
  | 0, acc, i => by simp [charsAt, chars, restE]
  | f + 1, acc, i => by
    rw [charsAt]
    by_cases hi : i < a.size
    · simp only [hi, ↓reduceDIte]
      rw [suffix_lt hi]
      simp only [chars]
      by_cases hq : a[i] == 0x22
      · simp only [hq, ↓reduceIte, restE]
      · simp only [hq, Bool.false_eq_true, ↓reduceIte]
        by_cases hs : a[i] == 0x5C
        · simp only [hs, ↓reduceIte]
          by_cases hi1 : i + 1 < a.size
          · simp only [hi1, ↓reduceDIte]
            rw [suffix_lt hi1]
            simp only
            by_cases hu : a[i + 1] == 0x75
            · simp only [hu, ↓reduceIte]
              by_cases hi5 : i + 5 < a.size
              · simp only [hi5, ↓reduceDIte]
                rw [suffix_lt (show i + 1 + 1 < a.size by omega), suffix_lt (show i + 1 + 1 + 1 < a.size by omega),
                  suffix_lt (show i + 1 + 1 + 1 + 1 < a.size by omega), suffix_lt (show i + 1 + 1 + 1 + 1 + 1 < a.size by omega)]
                simp only [show i + 1 + 1 = i + 2 by omega, show i + 2 + 1 = i + 3 by omega,
                  show i + 3 + 1 = i + 4 by omega, show i + 4 + 1 = i + 5 by omega, show i + 5 + 1 = i + 6 by omega]
                cases hexChar? a[i + 2] a[i + 3] a[i + 4] a[i + 5] with
                | some c => exact charsAt_eq a f _ _
                | none => rfl
              · simp only [hi5, ↓reduceDIte]
                have hl : (suffix a (i + 1 + 1)).length < 4 := by simp [suffix]; omega
                generalize suffix a (i + 1 + 1) = t at hl ⊢
                rcases t with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, t⟩⟩⟩⟩ <;> first | rfl | (simp at hl; omega)
            · simp only [hu, Bool.false_eq_true, ↓reduceIte]
              cases unescape? a[i + 1] with
              | some c => rw [charsAt_eq a f, show i + 2 = i + 1 + 1 by omega]
              | none => rfl
          · simp only [hi1, ↓reduceDIte]
            rw [suffix_ge (by omega)]
            rfl
        · simp only [hs, Bool.false_eq_true, ↓reduceIte]
          rw [← suffix_lt hi, ← rawCharAt_eq]
          cases rawCharAt a i with
          | none => rfl
          | some p =>
            obtain ⟨c, j⟩ := p
            simp only [restO, Option.map_some]
            split
            · rw [charsAt_eq a f]
            · rfl
    · simp only [hi, ↓reduceDIte]
      rw [suffix_ge (by omega)]
      rfl


/-! ### Literals -/

theorem dropPrefix_at (a : ByteArray) (p : List UInt8) (j k : Nat) (hk : p.length = k) :
    dropPrefix? p (suffix a j) =
      if (a.extract j (j + k) == p.toByteArray) = true then some (suffix a (j + k)) else none := by
  by_cases h : (a.extract j (j + k) == p.toByteArray) = true
  · simp only [h, ↓reduceIte]
    rw [extract_beq h, dropPrefix_complete]
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    cases hd : dropPrefix? p (suffix a j) with
    | none => rfl
    | some r => exact absurd (extract_beq_of hk (dropPrefix_sound hd)) h

/-! ### Values -/

theorem valueAt_all (a : ByteArray) : ∀ f : Nat,
    (∀ i, restE a (valueAt a f i) = value f (suffix a i)) ∧
    (∀ i acc, restE a (elementsAt a f i acc) = elements f (suffix a i) acc) ∧
    (∀ i acc, restE a (membersAt a f i acc) = members f (suffix a i) acc)
  | 0 => ⟨fun i => by simp [valueAt, value, restE], fun i acc => by simp [elementsAt, elements, restE],
      fun i acc => by simp [membersAt, members, restE]⟩
  | f + 1 => by
    obtain ⟨hv, he, hm⟩ := valueAt_all a f
    refine ⟨fun i => ?_, fun i acc => ?_, fun i acc => ?_⟩
    · rw [valueAt]
      by_cases hi : i < a.size
      · simp only [hi, ↓reduceDIte]
        rw [suffix_lt hi]
        simp only [value]
        by_cases h1 : a[i] == 0x22
        · simp only [h1, ↓reduceIte]
          rw [← charsAt_eq]
          cases charsAt a f "" (i + 1) with
          | ok p => rfl
          | error e => rfl
        simp only [h1, Bool.false_eq_true, ↓reduceIte]
        by_cases h2 : a[i] == 0x5B
        · simp only [h2, ↓reduceIte]
          rw [← skipWsAt_eq]
          by_cases hj : skipWsAt a (i + 1) < a.size
          · simp only [hj, ↓reduceDIte]
            rw [suffix_lt hj]
            by_cases h3 : a[skipWsAt a (i + 1)] == 0x5D
            · simp only [h3, ↓reduceIte, restE]
            · simp only [h3, Bool.false_eq_true, ↓reduceIte]
              rw [← he (i + 1) []]
              cases elementsAt a f (i + 1) [] with
              | ok p => rfl
              | error e => rfl
          · simp only [hj, ↓reduceDIte]
            rw [suffix_ge (by omega)]
            rfl
        simp only [h2, Bool.false_eq_true, ↓reduceIte]
        by_cases h4 : a[i] == 0x7B
        · simp only [h4, ↓reduceIte]
          rw [← skipWsAt_eq]
          by_cases hj : skipWsAt a (i + 1) < a.size
          · simp only [hj, ↓reduceDIte]
            rw [suffix_lt hj]
            by_cases h3 : a[skipWsAt a (i + 1)] == 0x7D
            · simp only [h3, ↓reduceIte, restE]
            · simp only [h3, Bool.false_eq_true, ↓reduceIte]
              rw [← hm (i + 1) []]
              cases membersAt a f (i + 1) [] with
              | ok p => rfl
              | error e => rfl
          · simp only [hj, ↓reduceDIte]
            rw [suffix_ge (by omega)]
            rfl
        simp only [h4, Bool.false_eq_true, ↓reduceIte]
        by_cases h5 : a[i] == 0x6E
        · simp only [h5, ↓reduceIte]
          rw [dropPrefix_at a nullTail (i + 1) 3 rfl, show i + 4 = i + 1 + 3 by omega]
          by_cases hl : (a.extract (i + 1) (i + 1 + 3) == nullTail.toByteArray) = true
          · simp only [nullB, hl, ↓reduceIte, restE]
          · simp only [nullB, hl, Bool.false_eq_true, ↓reduceIte, restE]
        simp only [h5, Bool.false_eq_true, ↓reduceIte]
        by_cases h6 : a[i] == 0x74
        · simp only [h6, ↓reduceIte]
          rw [dropPrefix_at a trueTail (i + 1) 3 rfl, show i + 4 = i + 1 + 3 by omega]
          by_cases hl : (a.extract (i + 1) (i + 1 + 3) == trueTail.toByteArray) = true
          · simp only [trueB, hl, ↓reduceIte, restE]
          · simp only [trueB, hl, Bool.false_eq_true, ↓reduceIte, restE]
        simp only [h6, Bool.false_eq_true, ↓reduceIte]
        by_cases h7 : a[i] == 0x66
        · simp only [h7, ↓reduceIte]
          rw [dropPrefix_at a falseTail (i + 1) 4 rfl, show i + 5 = i + 1 + 4 by omega]
          by_cases hl : (a.extract (i + 1) (i + 1 + 4) == falseTail.toByteArray) = true
          · simp only [falseB, hl, ↓reduceIte, restE]
          · simp only [falseB, hl, Bool.false_eq_true, ↓reduceIte, restE]
        simp only [h7, Bool.false_eq_true, ↓reduceIte]
        rw [← suffix_lt hi, ← intAt_eq]
        cases intAt a i with
        | some p => rfl
        | none => rfl
      · simp only [hi, ↓reduceDIte]
        rw [suffix_ge (by omega)]
        rfl
    · rw [elementsAt, elements, ← skipWsAt_eq, ← hv]
      cases valueAt a f (skipWsAt a i) with
      | error e => rfl
      | ok p =>
        obtain ⟨v, j⟩ := p
        simp only [restE]
        rw [← skipWsAt_eq]
        by_cases hk : skipWsAt a j < a.size
        · simp only [hk, ↓reduceDIte]
          rw [suffix_lt hk]
          by_cases hc : a[skipWsAt a j] == 0x2C
          · simp only [hc, ↓reduceIte]
            exact he _ _
          · simp only [hc, Bool.false_eq_true, ↓reduceIte]
            by_cases hd : a[skipWsAt a j] == 0x5D
            · simp only [hd, ↓reduceIte]
            · simp only [hd, Bool.false_eq_true, ↓reduceIte]
        · simp only [hk, ↓reduceDIte]
          rw [suffix_ge (by omega)]
    · rw [membersAt, members, ← skipWsAt_eq]
      dsimp only
      by_cases hi : skipWsAt a i < a.size
      · simp only [hi, ↓reduceDIte]
        rw [suffix_lt hi]
        by_cases hq : a[skipWsAt a i] == 0x22
        · simp only [hq, ↓reduceIte]
          rw [← charsAt_eq]
          cases charsAt a f "" (skipWsAt a i + 1) with
          | error e => rfl
          | ok p =>
            obtain ⟨k, j⟩ := p
            simp only [restE]
            rw [← skipWsAt_eq]
            by_cases hj : skipWsAt a j < a.size
            · simp only [hj, ↓reduceDIte]
              rw [suffix_lt hj]
              by_cases hc : a[skipWsAt a j] == 0x3A
              · simp only [hc, ↓reduceIte]
                rw [← skipWsAt_eq, ← hv]
                cases valueAt a f (skipWsAt a (skipWsAt a j + 1)) with
                | error e => rfl
                | ok p =>
                  obtain ⟨v, l⟩ := p
                  simp only [restE]
                  rw [← skipWsAt_eq]
                  by_cases hl : skipWsAt a l < a.size
                  · simp only [hl, ↓reduceDIte]
                    rw [suffix_lt hl]
                    by_cases hc' : a[skipWsAt a l] == 0x2C
                    · simp only [hc', ↓reduceIte]
                      exact hm _ _
                    · simp only [hc', Bool.false_eq_true, ↓reduceIte]
                      by_cases hd : a[skipWsAt a l] == 0x7D
                      · simp only [hd, ↓reduceIte]
                      · simp only [hd, Bool.false_eq_true, ↓reduceIte]
                  · simp only [hl, ↓reduceDIte]
                    rw [suffix_ge (by omega)]
              · simp only [hc, Bool.false_eq_true, ↓reduceIte]
            · simp only [hj, ↓reduceDIte]
              rw [suffix_ge (by omega)]
        · simp only [hq, Bool.false_eq_true, ↓reduceIte, restE]
      · simp only [hi, ↓reduceDIte]
        rw [suffix_ge (by omega)]
        rfl

/-- The index parser returns what the list parser returns. -/
theorem parse_eq (a : ByteArray) : parse a = parseReference a := by
  unfold parse parseReference parseList
  have hlen : a.data.toList.length = a.size := by simp
  have h0 : skipWs a.data.toList = suffix a (skipWsAt a 0) := by rw [skipWsAt_eq, suffix, List.drop_zero]
  rw [hlen, h0, ← (valueAt_all a _).1]
  cases valueAt a (a.size + 1) (skipWsAt a 0) with
  | error e => rfl
  | ok p =>
    obtain ⟨v, j⟩ := p
    simp only [restE]
    rw [← skipWsAt_eq]
    by_cases hk : a.size ≤ skipWsAt a j
    · rw [suffix_ge hk]
      simp [hk]
    · rw [suffix_lt (by omega)]
      simp [hk]

end Airbender.Json.Parser
