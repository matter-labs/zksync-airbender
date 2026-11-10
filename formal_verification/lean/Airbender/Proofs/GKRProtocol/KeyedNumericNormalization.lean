import Airbender.Proofs.GKRProtocol.FastNumericNormalization

namespace Airbender.Compiler.NumericPolynomialChecks.KeyedNormalization
set_option warningAsError true

def decode (key : Nat) : List Nat :=
  if key = 0 then []
  else if (key - 1) % 512 = 0 then [(key - 1) / 512]
  else [(key - 1) / 512, (key - 1) % 512 - 1]

theorem compare_decode (left right : Nat) :
    monomialCompare (decode left) (decode right) = compare left right := by
  cases left with
  | zero =>
      cases right with
      | zero => rfl
      | succ right =>
          simp only [decode, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
          split <;> simp [monomialCompare, Nat.compare_eq_lt.mpr (Nat.zero_lt_succ right)]
  | succ left =>
      cases right with
      | zero =>
          simp only [decode, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
          split <;> simp [monomialCompare, Nat.compare_eq_gt.mpr (Nat.zero_lt_succ left)]
      | succ right =>
          have divLeft := Nat.mod_lt left (by decide : 0 < 512)
          have divRight := Nat.mod_lt right (by decide : 0 < 512)
          rcases lt_trichotomy (left / 512) (right / 512) with less | same | greater
          · have order : left + 1 < right + 1 := by omega
            simp only [decode, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
            split <;> split <;> simp [monomialCompare, Nat.compare_eq_lt.mpr less, Nat.compare_eq_lt.mpr order]
          · have first : compare (left / 512) (right / 512) = .eq := Nat.compare_eq_eq.mpr same
            simp only [decode, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
            split_ifs with leftZero rightZero
            · have order : left + 1 = right + 1 := by omega
              simp [monomialCompare, first, order]
            · have order : left + 1 < right + 1 := by omega
              simp [monomialCompare, first, Nat.compare_eq_lt.mpr order]
            · have order : right + 1 < left + 1 := by omega
              simp [monomialCompare, first, Nat.compare_eq_gt.mpr order]
            · have tailCompare : compare (left % 512 - 1) (right % 512 - 1) = compare (left + 1) (right + 1) := by
                rcases lt_trichotomy (left + 1) (right + 1) with h | h | h
                · have tailOrder : left % 512 - 1 < right % 512 - 1 := by omega
                  rw [Nat.compare_eq_lt.mpr tailOrder, Nat.compare_eq_lt.mpr h]
                · have tailOrder : left % 512 - 1 = right % 512 - 1 := by omega
                  rw [Nat.compare_eq_eq.mpr tailOrder, Nat.compare_eq_eq.mpr h]
                · have tailOrder : right % 512 - 1 < left % 512 - 1 := by omega
                  rw [Nat.compare_eq_gt.mpr tailOrder, Nat.compare_eq_gt.mpr h]
              simp only [monomialCompare, first, tailCompare]
              cases compare (left + 1) (right + 1) <;> rfl
          · have order : right + 1 < left + 1 := by omega
            simp only [decode, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
            split <;> split <;> simp [monomialCompare, Nat.compare_eq_gt.mpr greater, Nat.compare_eq_gt.mpr order]


def key : List Nat → Nat
  | [] => 0
  | [first] => 1 + first * 512
  | [first, second] => 2 + min first second * 512 + max first second
  | _ => 0

def small : List Nat → Bool
  | [] => true
  | [_] => true
  | [first, second] => decide (first < 511) && decide (second < 511)
  | _ => false

theorem decode_key (monomial : List Nat) (checked : small monomial = true) :
    decode (key monomial) = monomial.insertionSort (fun a b => a ≤ b) := by
  rcases monomial with _ | ⟨first, _ | ⟨second, _ | ⟨third, tail⟩⟩⟩
  · rfl
  · have nonzero : 1 + first * 512 ≠ 0 := by omega
    have whole : (1 + first * 512 - 1) / 512 = first := by omega
    have rest : (1 + first * 512 - 1) % 512 = 0 := by omega
    simp [key, decode]
  · simp only [small, Bool.and_eq_true, decide_eq_true_eq] at checked
    have smallMin := min_le_left first second
    have smallMax : max first second < 511 := max_lt checked.1 checked.2
    have nonzero : 2 + min first second * 512 + max first second ≠ 0 := by omega
    have whole : (2 + min first second * 512 + max first second - 1) / 512 = min first second := by omega
    have rest : (2 + min first second * 512 + max first second - 1) % 512 = max first second + 1 := by omega
    simp only [key, decode, if_neg nonzero, whole, rest, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    by_cases order : first ≤ second
    · simp [List.insertionSort, order]
    · have reverse := le_of_not_ge order
      simp [List.insertionSort, List.orderedInsert, min_eq_right reverse, max_eq_left reverse, order]
  · simp [small] at checked

def decodeRows (rows : List (Nat × Nat)) : Data :=
  rows.map fun term => (term.1, decode term.2)

def insert (p : Nat) (term : Nat × Nat) (rows : List (Nat × Nat)) : List (Nat × Nat) :=
  if term.1 == 0 then rows
  else match rows with
    | [] => [term]
    | head :: tail => match compare term.2 head.2 with
      | .eq =>
          let sum := (term.1 + head.1) % p
          if sum == 0 then tail else (sum, term.2) :: tail
      | .lt => term :: head :: tail
      | .gt => head :: insert p term tail
termination_by structural rows

theorem decode_insert (p : Nat) (term : Nat × Nat) (rows : List (Nat × Nat)) :
    decodeRows (insert p term rows) = FastNormalization.insert p (term.1, decode term.2) (decodeRows rows) := by
  induction rows with
  | nil => simp only [insert, FastNormalization.insert, decodeRows, List.map_nil]; split <;> rfl
  | cons head tail ih =>
      simp only [insert, FastNormalization.insert, decodeRows, List.map_cons,
        FastNormalization.compareMonomial_eq, compare_decode]
      split
      · rfl
      · cases order : compare term.2 head.2 with
        | eq => dsimp only; split <;> rfl
        | lt => rfl
        | gt => simp only [decodeRows] at ih; exact congrArg (fun rest => (head.1, decode head.2) :: rest) ih

def keyedNormalize (p : Nat) (polynomial : Data) : Data :=
  decodeRows (polynomial.foldr (fun term result => insert p (term.1, key term.2) result) [])

theorem keyedNormalize_eq (p : Nat) (polynomial : Data)
    (checked : polynomial.all (fun term => small term.2) = true) :
    keyedNormalize p polynomial = FastNormalization.normalize p polynomial := by
  induction polynomial with
  | nil => rfl
  | cons term tail ih =>
      simp only [List.all_cons, Bool.and_eq_true] at checked
      simp only [keyedNormalize, List.foldr_cons, decode_insert]
      rw [decode_key term.2 checked.1]
      exact congrArg (FastNormalization.insert p (term.1, term.2.insertionSort (fun a b => a ≤ b))) (ih checked.2)

def encodeRows (polynomial : Data) : List (Nat × Nat) :=
  polynomial.map fun term => (term.1, key term.2)

def sortedSmall : List Nat → Bool
  | [] => true
  | [_] => true
  | [first, second] => decide (first ≤ second) && decide (second < 511)
  | _ => false

theorem sortedSmall_small (monomial : List Nat) (checked : sortedSmall monomial = true) :
    small monomial = true := by
  rcases monomial with _ | ⟨first, _ | ⟨second, _ | ⟨third, tail⟩⟩⟩
  · rfl
  · rfl
  · simp only [sortedSmall, Bool.and_eq_true, decide_eq_true_eq] at checked
    simp only [small, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨lt_of_le_of_lt checked.1 checked.2, checked.2⟩
  · simp [sortedSmall] at checked

theorem decode_key_sorted (monomial : List Nat) (checked : sortedSmall monomial = true) :
    decode (key monomial) = monomial := by
  rw [decode_key monomial (sortedSmall_small monomial checked)]
  rcases monomial with _ | ⟨first, _ | ⟨second, _ | ⟨third, tail⟩⟩⟩
  · rfl
  · rfl
  · simp only [sortedSmall, Bool.and_eq_true, decide_eq_true_eq] at checked
    simp [List.insertionSort, checked.1]
  · simp [sortedSmall] at checked

theorem decode_encode (polynomial : Data)
    (checked : polynomial.all (fun term => sortedSmall term.2) = true) :
    decodeRows (encodeRows polynomial) = polynomial := by
  induction polynomial with
  | nil => rfl
  | cons term tail ih =>
      simp only [List.all_cons, Bool.and_eq_true] at checked
      simp only [encodeRows, decodeRows, List.map_cons] at ih ⊢
      rw [decode_key_sorted term.2 checked.1, ih checked.2]

theorem decode_injective : Function.Injective decode := by
  intro left right same
  have order := compare_decode left right
  rw [same] at order
  have self := FastNormalization.monomial_compare_eq (decode right) (decode right)
  exact Nat.compare_eq_eq.mp (order.symm.trans (self.mpr rfl))

theorem decodeRows_injective : Function.Injective decodeRows := by
  apply List.map_injective_iff.mpr
  intro left right same
  apply Prod.ext
  · exact congrArg (fun term : Nat × List Nat => term.1) same
  · exact decode_injective (congrArg (fun term : Nat × List Nat => term.2) same)

def normalizedKeys (p : Nat) (polynomial : Data) : List (Nat × Nat) :=
  polynomial.foldr (fun term result => insert p (term.1, key term.2) result) []

end Airbender.Compiler.NumericPolynomialChecks.KeyedNormalization
