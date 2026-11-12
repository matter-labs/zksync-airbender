module
import all Mathlib.Data.List.Sort
public import Proven.GKRProtocol.KeyedNumericNormalization

@[expose] public section
set_option warningAsError true

namespace Airbender.Compiler.NumericPolynomialChecks.PackedNormalization

abbrev coefficientBase : Nat := 4294967296
abbrev radix : Nat := 18446744073709551616
abbrev Row := Nat × Nat

structure Packed where
  length : Nat
  value : Nat
  deriving BEq, ReflBEq, LawfulBEq

theorem Packed.ext {left right : Packed} (lengths : left.length = right.length)
    (values : left.value = right.value) : left = right := by
  cases left
  cases right
  cases lengths
  cases values
  rfl

def termCode (term : Row) : Nat := term.1 + coefficientBase * term.2

def decodeTerm (value : Nat) : Row := (value % coefficientBase, value / coefficientBase)

abbrev bounded (term : Row) : Prop := term.1 < coefficientBase ∧ term.2 < coefficientBase

theorem code_bound (term : Row) (bound : bounded term) : termCode term < radix := by
  dsimp [bounded, termCode, coefficientBase, radix] at *
  omega

theorem decode_code (term : Row) (bound : bounded term) : decodeTerm (termCode term) = term := by
  apply Prod.ext <;> dsimp [decodeTerm, termCode, coefficientBase, bounded] at * <;> omega

def prepend (head : Row) (tail : Packed) : Packed :=
  ⟨tail.length + 1, termCode head + radix * tail.value⟩

def pack (rows : List Row) : Packed := rows.foldr prepend ⟨0, 0⟩

theorem pack_cons (head : Row) (tail : List Row) :
    pack (head :: tail) = prepend head (pack tail) := rfl

theorem pack_length (rows : List Row) : (pack rows).length = rows.length := by
  induction rows with
  | nil => rfl
  | cons head tail ih => simp only [pack_cons, prepend, List.length_cons, ih]

theorem pack_eta (rows : List Row) : (⟨rows.length, (pack rows).value⟩ : Packed) = pack rows :=
  Packed.ext (pack_length rows).symm rfl

theorem head_pack (head : Row) (tail : List Row) (bound : bounded head) :
    (pack (head :: tail)).value % radix = termCode head := by
  have code := code_bound head bound
  change (termCode head + radix * (pack tail).value) % radix = termCode head
  dsimp [radix] at *
  omega

theorem tail_pack (head : Row) (tail : List Row) (bound : bounded head) :
    (pack (head :: tail)).value / radix = (pack tail).value := by
  have code := code_bound head bound
  change (termCode head + radix * (pack tail).value) / radix = (pack tail).value
  dsimp [radix] at *
  omega

theorem pack_injective (left right : List Row)
    (leftBound : ∀ term ∈ left, bounded term) (rightBound : ∀ term ∈ right, bounded term)
    (same : pack left = pack right) : left = right := by
  induction left generalizing right with
  | nil =>
      have sizes := congrArg Packed.length same
      rw [pack_length, pack_length] at sizes
      cases right <;> simp_all
  | cons head tail ih =>
      cases right with
      | nil =>
          have sizes := congrArg Packed.length same
          rw [pack_length, pack_length] at sizes
          simp at sizes
      | cons next rest =>
          have headBound := leftBound head (by simp)
          have nextBound := rightBound next (by simp)
          have values := congrArg Packed.value same
          have heads := congrArg (fun value => value % radix) values
          rw [head_pack head tail headBound, head_pack next rest nextBound] at heads
          have headSame : head = next := by
            simpa only [decode_code head headBound, decode_code next nextBound] using congrArg decodeTerm heads
          have tails := congrArg (fun value => value / radix) values
          rw [tail_pack head tail headBound, tail_pack next rest nextBound] at tails
          have lengths := congrArg Packed.length same
          rw [pack_length, pack_length, List.length_cons, List.length_cons] at lengths
          have tailSame : pack tail = pack rest := by
            apply Packed.ext
            · simpa only [pack_length] using Nat.add_right_cancel lengths
            · exact tails
          exact congrArg₂ List.cons headSame (ih rest
            (fun term member => leftBound term (by simp [member]))
            (fun term member => rightBound term (by simp [member])) tailSame)

theorem insert_bounded (p : Nat) (primePositive : 0 < p) (primeBound : p ≤ coefficientBase)
    (term : Row) (termBound : bounded term) (rows : List Row)
    (rowsBound : ∀ row ∈ rows, bounded row) :
    ∀ row ∈ KeyedNormalization.insert p term rows, bounded row := by
  induction rows with
  | nil =>
      simp only [KeyedNormalization.insert]
      split
      · simp
      · simpa using termBound
  | cons head tail ih =>
      have headBound := rowsBound head (by simp)
      have tailBound : ∀ row ∈ tail, bounded row := fun row member => rowsBound row (by simp [member])
      simp only [KeyedNormalization.insert]
      split
      · exact rowsBound
      · cases order : compare term.2 head.2 with
        | eq =>
            dsimp only
            split
            · exact tailBound
            · intro row member
              simp only [List.mem_cons] at member
              rcases member with rfl | member
              · exact ⟨lt_of_lt_of_le (Nat.mod_lt _ primePositive) primeBound, termBound.2⟩
              · exact tailBound row member
        | lt =>
            intro row member
            simp only [List.mem_cons] at member
            rcases member with rfl | rfl | member
            · exact termBound
            · exact headBound
            · exact tailBound row member
        | gt =>
            intro row member
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · exact headBound
            · exact ih tailBound row member

def normalizeRows (p : Nat) (rows : List Row) : List Row :=
  rows.foldr (KeyedNormalization.insert p) []

theorem normalizeRows_encode (p : Nat) (polynomial : Data) :
    normalizeRows p (KeyedNormalization.encodeRows polynomial) = KeyedNormalization.normalizedKeys p polynomial := by
  simp only [normalizeRows, KeyedNormalization.encodeRows, KeyedNormalization.normalizedKeys, List.foldr_map]

theorem normalizeRows_bounded (p : Nat) (positive : 0 < p) (primeBound : p ≤ coefficientBase)
    (rows : List Row) (bound : ∀ row ∈ rows, bounded row) :
    ∀ row ∈ normalizeRows p rows, bounded row := by
  induction rows with
  | nil => simp [normalizeRows]
  | cons head tail ih =>
      have headBound := bound head (by simp)
      have tailBound : ∀ row ∈ tail, bounded row := fun row member => bound row (by simp [member])
      exact insert_bounded p positive primeBound head headBound (normalizeRows p tail) (ih tailBound)

def boundsCheck (rows : List Row) : Bool := rows.all (fun row => decide (bounded row))

theorem boundsCheck_sound (rows : List Row) (checked : boundsCheck rows = true) :
    ∀ row ∈ rows, bounded row := by
  simpa only [boundsCheck, List.all_eq_true, decide_eq_true_eq] using checked

end Airbender.Compiler.NumericPolynomialChecks.PackedNormalization
