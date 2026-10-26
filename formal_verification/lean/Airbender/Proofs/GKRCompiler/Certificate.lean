import Airbender.Proofs.GKRCompiler.Polynomial

/- A checked polynomial-ideal certificate supplies both backward preservation
and constructive witness extension. Certificate generation is untrusted. -/
namespace Airbender.Compiler
set_option warningAsError true
set_option Elab.async false

/-- Assemble already kernel-checked finite cases without reevaluating every
case in one large reduction. The proposition records the exact list checked. -/
inductive BoolChecks (predicate : α → Bool) : List α → Prop where
  | nil : BoolChecks predicate []
  | cons {head tail} : predicate head = true → BoolChecks predicate tail → BoolChecks predicate (head :: tail)

theorem BoolChecks.all_true {predicate : α → Bool} {items : List α}
    (checks : BoolChecks predicate items) : items.all predicate = true := by
  induction checks with
  | nil => rfl
  | cons head tail ih => simp only [List.all_cons, head, ih, Bool.and_self]

theorem and_checked {left right : Bool} (a : left = true) (b : right = true) :
    (left && right) = true := by rw [a, b]; rfl

def Satisfies [CommRing F] (relations : List (Polynomial n F)) (values : Fin n → F) : Prop :=
  ∀ relation ∈ relations, evaluate values relation = 0

abbrev Combination (relations : List (Polynomial n F)) :=
  List (Polynomial n F × Fin relations.length)

def combination [CommRing F] (relations : List (Polynomial n F))
    (terms : Combination relations) : Polynomial n F :=
  terms.foldr (fun term result => add (multiply term.1 (relations.get term.2)) result) []

theorem combination_zero [CommRing F] {relations : List (Polynomial n F)}
    {values : Fin n → F} (holds : Satisfies relations values) (terms : Combination relations) :
    evaluate values (combination relations terms) = 0 := by
  induction terms with
  | nil => rfl
  | cons term rest ih =>
    simp only [combination, List.foldr_cons, evaluate_add, evaluate_multiply,
      holds _ (List.get_mem _ _), mul_zero, zero_add]
    exact ih

structure Translation (sourceVariables lowerVariables : Nat) (F : Type) where
  source : List (Polynomial sourceVariables F)
  lowered : List (Polynomial lowerVariables F)
  projection : Fin sourceVariables → Fin lowerVariables
  extension : Fin lowerVariables → Polynomial sourceVariables F

structure Certificate (translation : Translation n m F) where
  backward : Fin translation.source.length → Combination translation.lowered
  forward : Fin translation.lowered.length → Combination translation.source

def Certificate.Valid [CommRing F] [DecidableEq F] {translation : Translation n m F}
    (certificate : Certificate translation) : Prop :=
  (∀ wire, equal (translation.extension (translation.projection wire)) (atom wire) = true) ∧
  (∀ index : Fin translation.source.length,
    equal (rename translation.projection (translation.source.get index))
      (combination translation.lowered (certificate.backward index)) = true) ∧
  (∀ index : Fin translation.lowered.length,
    equal (substitute translation.extension (translation.lowered.get index))
      (combination translation.source (certificate.forward index)) = true)

instance [CommRing F] [DecidableEq F] {translation : Translation n m F}
    (certificate : Certificate translation) : Decidable certificate.Valid :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def check [CommRing F] [DecidableEq F] (translation : Translation n m F)
    (certificate : Certificate translation) : Bool :=
  (List.finRange n).all (fun wire =>
    equal (translation.extension (translation.projection wire)) (atom wire)) &&
  (List.finRange translation.source.length).all (fun index =>
    equal (rename translation.projection (translation.source.get index))
      (combination translation.lowered (certificate.backward index))) &&
  (List.finRange translation.lowered.length).all (fun index =>
    equal (substitute translation.extension (translation.lowered.get index))
      (combination translation.source (certificate.forward index)))

theorem check_valid [CommRing F] [DecidableEq F]
    {translation : Translation n m F} {certificate : Certificate translation}
    (checked : check translation certificate = true) : certificate.Valid := by
  simp only [check, Bool.and_eq_true, List.all_eq_true] at checked
  exact ⟨fun wire => checked.1.1 wire (List.mem_finRange _),
    fun index => checked.1.2 index (List.mem_finRange _),
    fun index => checked.2 index (List.mem_finRange _)⟩

theorem backward_preservation [CommRing F] [DecidableEq F]
    {translation : Translation n m F} {certificate : Certificate translation}
    (checked : check translation certificate = true) {values : Fin m → F}
    (holds : Satisfies translation.lowered values) :
    Satisfies translation.source (values ∘ translation.projection) := by
  have valid := check_valid checked
  intro relation member
  obtain ⟨index, rfl⟩ := List.mem_iff_get.mp member
  have same := equal_sound (valid.2.1 index) values
  rw [evaluate_rename] at same
  exact same.trans (combination_zero holds _)

theorem witness_extension [CommRing F] [DecidableEq F]
    {translation : Translation n m F} {certificate : Certificate translation}
    (checked : check translation certificate = true) {values : Fin n → F}
    (holds : Satisfies translation.source values) :
    ∃ extended : Fin m → F,
      (∀ wire, extended (translation.projection wire) = values wire) ∧
      Satisfies translation.lowered extended := by
  have valid := check_valid checked
  refine ⟨fun wire => evaluate values (translation.extension wire), ?_, ?_⟩
  · intro wire
    exact (equal_sound (valid.1 wire) values).trans (evaluate_atom values wire)
  · intro relation member
    obtain ⟨index, rfl⟩ := List.mem_iff_get.mp member
    have same := equal_sound (valid.2.2 index) values
    rw [evaluate_substitute] at same
    exact same.trans (combination_zero holds _)

theorem semantic_preservation [CommRing F] [DecidableEq F]
    {translation : Translation n m F} {certificate : Certificate translation}
    (checked : check translation certificate = true) (values : Fin n → F) :
    Satisfies translation.source values ↔
      ∃ extended : Fin m → F,
        (∀ wire, extended (translation.projection wire) = values wire) ∧
        Satisfies translation.lowered extended := by
  constructor
  · exact witness_extension checked
  · rintro ⟨extended, projection, holds⟩
    have same : extended ∘ translation.projection = values := funext projection
    simpa only [same] using backward_preservation checked holds

end Airbender.Compiler
