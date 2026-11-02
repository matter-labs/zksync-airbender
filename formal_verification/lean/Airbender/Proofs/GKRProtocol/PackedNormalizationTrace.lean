import Airbender.Proofs.GKRProtocol.PackedNumericPolynomial
import Mathlib.Data.Nat.Digits.Defs

namespace Airbender.Compiler.NumericPolynomialChecks.PackedNormalization
set_option warningAsError true


def insertAt (p : Nat) (term : Row) (previous : Packed) (index : Nat) : Packed :=
  let power := radix ^ index
  let low :=  previous.value % power
  let tail := previous.value / power
  let count := previous.length - index
  let head := decodeTerm (tail % radix)
  let next :=
    if index == previous.length then ⟨1, termCode term⟩
    else if term.2 == head.2 then
      let sum := (term.1 + head.1) % p
      if sum == 0 then ⟨count - 1, tail / radix⟩
      else prepend (sum, term.2) ⟨count - 1, tail / radix⟩
    else prepend term ⟨count, tail⟩
  ⟨index + next.length, low + power * next.value⟩

def insertAtCheck (p : Nat) (term : Row) (previous result : Packed) (index : Nat) : Bool :=
  if term.1 == 0 then previous == result
  else decide (index ≤ previous.length) &&
    (index == 0 || decide ((decodeTerm (previous.value / radix ^ (index - 1) % radix)).2 < term.2)) &&
    (index == previous.length || decide (term.2 ≤ (decodeTerm (previous.value / radix ^ index % radix)).2)) &&
    (insertAt p term previous index == result)

def hintedCheck (p : Nat) : Nat → Nat → List (Nat × Packed) → Bool
  | 0, _, [(0, result)] => result == ⟨0, 0⟩
  | count + 1, value, (index, result) :: (nextIndex, previous) :: rest =>
      insertAtCheck p (decodeTerm (value % radix)) previous result index &&
        hintedCheck p count (value / radix) ((nextIndex, previous) :: rest)
  | _, _, _ => false

abbrev Ordered (rows : List Row) : Prop := rows.Pairwise (fun left right => left.2 < right.2)

theorem insert_all (p : Nat) (term : Row) (rows : List Row) (property : Nat → Prop)
    (termProperty : property term.2) (rowsProperty : ∀ row ∈ rows, property row.2) :
    ∀ row ∈ KeyedNormalization.insert p term rows, property row.2 := by
  induction rows with
  | nil => simp only [KeyedNormalization.insert]; split <;> simp_all
  | cons head tail ih =>
      have headProperty := rowsProperty head (by simp)
      have tailProperty : ∀ row ∈ tail, property row.2 := fun row member => rowsProperty row (by simp [member])
      simp only [KeyedNormalization.insert]
      split
      · exact rowsProperty
      · cases compare term.2 head.2 with
        | eq =>
            dsimp only
            split
            · exact tailProperty
            · intro row member
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · exact termProperty
              · exact tailProperty row member
        | lt =>
            intro row member
            simp only [List.mem_cons] at member
            rcases member with rfl | rfl | member
            · exact termProperty
            · exact headProperty
            · exact tailProperty row member
        | gt =>
            intro row member
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · exact headProperty
            · exact ih tailProperty row member

theorem insert_ordered (p : Nat) (term : Row) (rows : List Row) (ordered : Ordered rows) :
    Ordered (KeyedNormalization.insert p term rows) := by
  induction rows with
  | nil => simp only [KeyedNormalization.insert]; split <;> simp
  | cons head tail ih =>
      simp only [List.pairwise_cons] at ordered
      simp only [KeyedNormalization.insert]
      split
      · exact List.pairwise_cons.mpr ordered
      · cases order : compare term.2 head.2 with
        | eq =>
            have keys := Nat.compare_eq_eq.mp order
            dsimp only
            split
            · exact ordered.2
            · apply List.pairwise_cons.mpr
              exact ⟨by simpa only [keys] using ordered.1, ordered.2⟩
        | lt =>
            have less := Nat.compare_eq_lt.mp order
            apply List.pairwise_cons.mpr
            exact ⟨by
              intro row member
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · exact less
              · exact lt_trans less (ordered.1 row member), List.pairwise_cons.mpr ordered⟩
        | gt =>
            have greater := Nat.compare_eq_gt.mp order
            apply List.pairwise_cons.mpr
            exact ⟨insert_all p term tail (head.2 < ·) greater ordered.1, ih ordered.2⟩

theorem normalizeRows_ordered (p : Nat) (rows : List Row) : Ordered (normalizeRows p rows) := by
  induction rows with
  | nil => simp [normalizeRows]
  | cons head tail ih => exact insert_ordered p head (normalizeRows p tail) ih

theorem insert_append (p : Nat) (term : Row) (front tail : List Row) (nonzero : term.1 ≠ 0)
    (before : ∀ row ∈ front, row.2 < term.2) :
    KeyedNormalization.insert p term (front ++ tail) = front ++ KeyedNormalization.insert p term tail := by
  induction front with
  | nil => rfl
  | cons head rest ih =>
      have order := Nat.compare_eq_gt.mpr (before head (by simp))
      simp only [List.cons_append, KeyedNormalization.insert, beq_iff_eq, ite_eq_right nonzero, order]
      rw [ih (fun row member => before row (by simp [member]))]

theorem pack_value (rows : List Row) : (pack rows).value = Nat.ofDigits radix (rows.map termCode) := by
  induction rows with
  | nil => rfl
  | cons head tail ih => simp only [pack_cons, prepend, List.map_cons, Nat.ofDigits_cons, ih]

theorem codes_bounded (rows : List Row) (bound : ∀ row ∈ rows, bounded row) :
    ∀ code ∈ rows.map termCode, code < radix := by
  intro code member
  rcases List.mem_map.mp member with ⟨row, oldMember, rfl⟩
  exact code_bound row (bound row oldMember)

theorem pack_take (rows : List Row) (index : Nat) (bound : ∀ row ∈ rows, bounded row) :
    (pack rows).value % radix ^ index = (pack (rows.take index)).value := by
  simp only [pack_value]
  rw [Nat.ofDigits_mod_pow_eq_ofDigits_take index (by decide) _ (codes_bounded rows bound), List.map_take]

theorem pack_drop (rows : List Row) (index : Nat) (bound : ∀ row ∈ rows, bounded row) :
    (pack rows).value / radix ^ index = (pack (rows.drop index)).value := by
  simp only [pack_value]
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop index (by decide) _ (codes_bounded rows bound), List.map_drop]

theorem pack_get (rows : List Row) (index : Nat) (within : index < rows.length)
    (bound : ∀ row ∈ rows, bounded row) :
    decodeTerm ((pack rows).value / radix ^ index % radix) = rows[index] := by
  rw [pack_drop rows index bound, List.drop_eq_getElem_cons within]
  rw [head_pack _ _ (bound _ (List.getElem_mem within)), decode_code _ (bound _ (List.getElem_mem within))]

theorem pack_append (front tail : List Row) :
    pack (front ++ tail) = ⟨front.length + tail.length, (pack front).value + radix ^ front.length * (pack tail).value⟩ := by
  apply Packed.ext
  · simp only [pack_length, List.length_append]
  · simp only [pack_value, List.map_append, Nat.ofDigits_append, List.length_map]

theorem ordered_prefix (rows : List Row) (ordered : Ordered rows) (index key : Nat)
    (within : index ≤ rows.length)
    (last : ∀ positive : 0 < index, (rows[index - 1]'(by omega)).2 < key) :
    ∀ row ∈ rows.take index, row.2 < key := by
  intro row member
  rcases List.mem_iff_getElem.mp member with ⟨position, positionBound, value⟩
  have positionLength : position < min index rows.length := by simpa only [List.length_take] using positionBound
  have positionWithin : position < index := lt_of_lt_of_le positionLength (min_le_left index rows.length)
  have positionRows : position < rows.length := lt_of_lt_of_le positionWithin within
  have rowValue : rows[position] = row := by simpa only [List.getElem_take] using value
  have lastBound := last (by omega)
  by_cases atLast : position = index - 1
  · simpa only [← rowValue, atLast] using lastBound
  · have earlier : position < index - 1 := by omega
    have order := ordered.rel_get_of_lt (a := ⟨position, positionRows⟩) (b := ⟨index - 1, by omega⟩) earlier
    simp only [List.get_eq_getElem] at order
    exact rowValue ▸ lt_trans order lastBound



theorem insertAt_append (p : Nat) (term : Row) (front tail : List Row)
    (nonzero : term.1 ≠ 0) (bound : ∀ row ∈ front ++ tail, bounded row)
    (before : ∀ row ∈ front, row.2 < term.2)
    (after : ∀ head rest, tail = head :: rest → term.2 ≤ head.2) :
    insertAt p term (pack (front ++ tail)) front.length =
      pack (KeyedNormalization.insert p term (front ++ tail)) := by
  have low : (pack (front ++ tail)).value % radix ^ front.length = (pack front).value := by
    simpa using pack_take (front ++ tail) front.length bound
  have high : (pack (front ++ tail)).value / radix ^ front.length = (pack tail).value := by
    simpa using pack_drop (front ++ tail) front.length bound
  rw [insert_append p term front tail nonzero before]
  unfold insertAt
  dsimp only
  rw [low, high, pack_length, List.length_append, Nat.add_sub_cancel_left]
  conv_rhs => rw [pack_append]
  cases tail with
  | nil =>
      simp [KeyedNormalization.insert, nonzero, pack, prepend]
  | cons head rest =>
      have headBound := bound head (by simp)
      have headSame : decodeTerm ((pack (head :: rest)).value % radix) = head := by
        rw [head_pack head rest headBound, decode_code head headBound]
      have different : front.length ≠ front.length + (head :: rest).length := by simp
      simp only [beq_iff_eq, ite_eq_right different, headSame, tail_pack head rest headBound]
      rcases lt_or_eq_of_le (after head rest rfl) with less | same
      · have order := Nat.compare_eq_lt.mpr less
        have keys := Nat.ne_of_lt less
        simp [KeyedNormalization.insert, nonzero, order, keys, pack_cons, prepend, pack_length]
      · have order := Nat.compare_eq_eq.mpr same
        by_cases sumZero : (term.1 + head.1) % p = 0
        · simp [KeyedNormalization.insert, nonzero, same, sumZero]
        · simp [KeyedNormalization.insert, nonzero, same, sumZero, pack_cons, prepend, pack_length]



theorem insertAtCheck_sound (p : Nat) (term : Row) (rows : List Row) (result : Packed) (index : Nat)
    (bound : ∀ row ∈ rows, bounded row) (ordered : Ordered rows)
    (checked : insertAtCheck p term (pack rows) result index = true) :
    result = pack (KeyedNormalization.insert p term rows) := by
  by_cases zero : term.1 = 0
  · have same : pack rows = result := by simpa [insertAtCheck, zero] using checked
    cases rows <;> simpa [KeyedNormalization.insert, zero] using same.symm
  · simp only [insertAtCheck, beq_iff_eq, ite_eq_right zero, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, pack_length] at checked
    rcases checked with ⟨⟨⟨within, leftBound⟩, rightBound⟩, output⟩
    have before : ∀ row ∈ rows.take index, row.2 < term.2 := by
      apply ordered_prefix rows ordered index term.2 within
      intro positive
      rcases leftBound with empty | last
      · omega
      · rw [pack_get rows (index - 1) (by omega) bound] at last
        exact last
    have after : ∀ head rest, rows.drop index = head :: rest → term.2 ≤ head.2 := by
      intro head rest tailSame
      have droppedLength := congrArg List.length tailSame
      simp only [List.length_drop, List.length_cons] at droppedLength
      have inside : index < rows.length := by omega
      have headSame : rows[index] = head := by
        rw [List.drop_eq_getElem_cons inside] at tailSame
        exact (List.cons.inj tailSame).1
      rcases rightBound with atEnd | next
      · omega
      · simpa only [pack_get rows index inside bound, headSame] using next
    have frontLength : (rows.take index).length = index := by simp [List.length_take, min_eq_left within]
    have whole : rows.take index ++ rows.drop index = rows := List.take_append_drop index rows
    have actual := insertAt_append p term (rows.take index) (rows.drop index) zero
      (by rw [whole]; exact bound) before after
    rw [whole, frontLength] at actual
    exact output.symm.trans actual

theorem hintedCheck_sound (p : Nat) (primePositive : 0 < p) (primeBound : p ≤ coefficientBase)
    (rows : List Row) (bound : ∀ row ∈ rows, bounded row) (trace : List (Nat × Packed))
    (checked : hintedCheck p rows.length (pack rows).value trace = true) :
    (trace.headD (0, ⟨0, 0⟩)).2 = pack (normalizeRows p rows) := by
  induction rows generalizing trace with
  | nil =>
      cases trace with
      | nil => simp [hintedCheck] at checked
      | cons step rest =>
          rcases step with ⟨index, result⟩
          cases rest with
          | nil =>
              cases index with
              | zero => simpa [hintedCheck, normalizeRows, pack] using checked
              | succ _ => simp [hintedCheck] at checked
          | cons _ _ => simp [hintedCheck] at checked
  | cons head tail ih =>
      have headBound := bound head (by simp)
      have tailBound : ∀ row ∈ tail, bounded row := fun row member => bound row (by simp [member])
      cases trace with
      | nil => simp [hintedCheck] at checked
      | cons step rest =>
          rcases step with ⟨index, result⟩
          cases rest with
          | nil => simp [hintedCheck] at checked
          | cons previousStep rest =>
              rcases previousStep with ⟨nextIndex, previous⟩
              simp only [List.length_cons, hintedCheck, Bool.and_eq_true,
                head_pack head tail headBound, decode_code head headBound,
                tail_pack head tail headBound] at checked
              have previousSame := ih tailBound ((nextIndex, previous) :: rest) checked.2
              simp only [List.headD_cons] at previousSame
              have stepCheck := checked.1
              rw [previousSame] at stepCheck
              have normalization := normalizeRows_bounded p primePositive primeBound tail tailBound
              exact insertAtCheck_sound p head (normalizeRows p tail) result index normalization
                (normalizeRows_ordered p tail) stepCheck


structure PolynomialRow where
  expected : Packed
  input : Packed
  trace : List (Nat × Packed)

def PolynomialRow.check (p : Nat) (row : PolynomialRow) : Bool :=
  hintedCheck p row.input.length row.input.value row.trace &&
    (row.trace.headD (0, ⟨0, 0⟩)).2 == row.expected

structure PolynomialRow.Binding (expected input : Data) (row : PolynomialRow) : Prop where
  expectedEncoding : pack (KeyedNormalization.encodeRows expected) = row.expected
  inputEncoding : pack (KeyedNormalization.encodeRows input) = row.input
  expectedSorted : expected.all (fun term => KeyedNormalization.sortedSmall term.2) = true
  inputSmall : input.all (fun term => KeyedNormalization.small term.2) = true
  expectedBound : ∀ term ∈ KeyedNormalization.encodeRows expected, bounded term
  inputBound : ∀ term ∈ KeyedNormalization.encodeRows input, bounded term

theorem PolynomialRow.check_sound (p : Nat) (positive : 0 < p) (primeBound : p ≤ coefficientBase)
    (expected input : Data) (row : PolynomialRow) (binding : row.Binding expected input)
    (checked : row.check p = true) : NumericPolynomialChecks.normalize p input = expected := by
  simp only [PolynomialRow.check, Bool.and_eq_true, beq_iff_eq] at checked
  have traceChecked := checked.1
  rw [← binding.inputEncoding, pack_length] at traceChecked
  have normalized := hintedCheck_sound p positive primeBound _ binding.inputBound row.trace traceChecked
  have same : pack (normalizeRows p (KeyedNormalization.encodeRows input)) =
      pack (KeyedNormalization.encodeRows expected) :=
    normalized.symm.trans (checked.2.trans binding.expectedEncoding.symm)
  have bounds := normalizeRows_bounded p positive primeBound _ binding.inputBound
  have rowsSame := pack_injective _ _ bounds binding.expectedBound same
  have decodedSame := congrArg KeyedNormalization.decodeRows rowsSame
  rw [normalizeRows_encode] at decodedSame
  change KeyedNormalization.keyedNormalize p input = KeyedNormalization.decodeRows (KeyedNormalization.encodeRows expected) at decodedSame
  rw [KeyedNormalization.keyedNormalize_eq p input binding.inputSmall, FastNormalization.normalize_eq,
    KeyedNormalization.decode_encode expected binding.expectedSorted] at decodedSame
  exact decodedSame

def check (p : Nat) (rows : List PolynomialRow) : Bool :=
  decide (0 < p ∧ p ≤ coefficientBase) && rows.all (PolynomialRow.check p)

theorem check_sound (p : Nat) (rows : List PolynomialRow) (checked : check p rows = true) :
    ∀ row ∈ rows, ∀ expected input, row.Binding expected input →
      NumericPolynomialChecks.normalize p input = expected := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at checked
  intro row member expected input binding
  exact PolynomialRow.check_sound p checked.1.1 checked.1.2 expected input row binding (checked.2 row member)


end Airbender.Compiler.NumericPolynomialChecks.PackedNormalization
