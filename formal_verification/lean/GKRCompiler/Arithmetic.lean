import GKRCompiler.Certificate

namespace Airbender.Compiler
set_option warningAsError true
set_option Elab.async false

/-- Typed arithmetic syntax retains the source expression tree. Bounds on
native variable/address indices are checked when constructing each leaf. -/
inductive Expression (arity : Nat) (F : Type) where
  | constant : F → Expression arity F
  | atom : Fin arity → Expression arity F
  | add : Expression arity F → Expression arity F → Expression arity F
  | mul : Expression arity F → Expression arity F → Expression arity F
  deriving Repr, DecidableEq

def Expression.value [CommRing F] (values : Fin n → F) : Expression n F → F
  | .constant value => value
  | .atom wire => values wire
  | .add left right => left.value values + right.value values
  | .mul left right => left.value values * right.value values

def Expression.polynomial [CommRing F] : Expression n F → Polynomial n F
  | .constant value => Compiler.constant value
  | .atom wire => Compiler.atom wire
  | .add left right => Compiler.add left.polynomial right.polynomial
  | .mul left right => multiply left.polynomial right.polynomial

theorem Expression.polynomial_value [CommRing F] (values : Fin n → F) (expression : Expression n F) :
    evaluate values expression.polynomial = expression.value values := by
  induction expression with
  | constant value => exact evaluate_constant _ _
  | atom wire => exact evaluate_atom _ _
  | add left right ihLeft ihRight =>
    simp only [polynomial, evaluate_add, value, ihLeft, ihRight]
  | mul left right ihLeft ihRight =>
    simp only [polynomial, evaluate_multiply, value, ihLeft, ihRight]

/-- Native arithmetic relation forms. Both sparse input and structured
expression fields are retained and their equality is checked independently. -/
inductive ArithmeticGate (arity : Nat) (F : Type) where
  | assertZero (input expression : Expression arity F)
  | define (output : Fin arity) (input expression : Expression arity F)
  | copy (output input : Fin arity)
  deriving Repr, DecidableEq

def ArithmeticGate.inputResidual [CommRing F] : ArithmeticGate n F → Polynomial n F
  | .assertZero input _ => input.polynomial
  | .define output input _ => add (atom output) (negate input.polynomial)
  | .copy output input => add (atom output) (negate (atom input))

def ArithmeticGate.expressionResidual [CommRing F] (values : Fin n → F) : ArithmeticGate n F → F
  | .assertZero _ expression => expression.value values
  | .define output _ expression => values output - expression.value values
  | .copy output input => values output - values input

def ArithmeticGate.check [CommRing F] [DecidableEq F] : ArithmeticGate n F → Bool
  | .assertZero input expression | .define _ input expression =>
      equal input.polynomial expression.polynomial
  | .copy _ _ => true

theorem ArithmeticGate.checked_value [CommRing F] [DecidableEq F] {gate : ArithmeticGate n F}
    (checked : gate.check = true) (values : Fin n → F) :
    evaluate values gate.inputResidual = gate.expressionResidual values := by
  cases gate with
  | assertZero input expression =>
    exact (equal_sound checked values).trans (expression.polynomial_value values)
  | define output input expression =>
    have same := (equal_sound checked values).trans (expression.polynomial_value values)
    simp only [inputResidual, evaluate_add, evaluate_atom, evaluate_negate, expressionResidual, same, sub_eq_add_neg]
  | copy output input =>
    simp [inputResidual, expressionResidual, sub_eq_add_neg]

structure ArithmeticArtifact (sourceVariables lowerVariables : Nat) (F : Type) where
  source : List (Expression sourceVariables F)
  gates : List (ArithmeticGate lowerVariables F)
  placement : Fin sourceVariables → Fin lowerVariables

def ArithmeticArtifact.SourceHolds [CommRing F] (artifact : ArithmeticArtifact n m F)
    (values : Fin n → F) : Prop := ∀ expression ∈ artifact.source, expression.value values = 0

def ArithmeticArtifact.LoweredHolds [CommRing F] (artifact : ArithmeticArtifact n m F)
    (values : Fin m → F) : Prop := ∀ gate ∈ artifact.gates, gate.expressionResidual values = 0

/-- Selection describes the arithmetic slice certified in the forward
direction. The backward theorem accepts the whole artifact's arithmetic
relations and establishes every original source obligation. -/
def ArithmeticArtifact.translation [CommRing F] (artifact : ArithmeticArtifact n m F)
    (selected : List (Fin artifact.gates.length)) (extension : Fin m → Polynomial n F) : Translation n m F :=
  ⟨artifact.source.map Expression.polynomial,
    selected.map (fun index => (artifact.gates.get index).inputResidual), artifact.placement, extension⟩

theorem ArithmeticArtifact.source_iff [CommRing F] (artifact : ArithmeticArtifact n m F)
    (values : Fin n → F) :
    Satisfies (artifact.source.map Expression.polynomial) values ↔ artifact.SourceHolds values := by
  simp only [Satisfies, SourceHolds, List.mem_map, forall_exists_index, and_imp]
  constructor
  · intro holds expression member
    exact (expression.polynomial_value values).symm.trans (holds _ expression member rfl)
  · intro holds polynomial expression member same
    subst polynomial
    exact (expression.polynomial_value values).trans (holds expression member)

theorem ArithmeticArtifact.backward [CommRing F] [DecidableEq F]
    (artifact : ArithmeticArtifact n m F) (selected : List (Fin artifact.gates.length))
    (extension : Fin m → Polynomial n F)
    (certificate : Certificate (artifact.translation selected extension))
    (gateChecks : artifact.gates.all ArithmeticGate.check = true)
    (checked : check (artifact.translation selected extension) certificate = true)
    {values : Fin m → F} (holds : artifact.LoweredHolds values) :
    artifact.SourceHolds (values ∘ artifact.placement) := by
  apply (artifact.source_iff _).mp
  apply backward_preservation checked
  intro relation member
  obtain ⟨index, included, rfl⟩ := List.mem_map.mp member
  rw [(artifact.gates.get index).checked_value
    (List.all_eq_true.mp gateChecks _ (List.get_mem _ _))]
  exact holds _ (List.get_mem _ _)

theorem ArithmeticArtifact.forward [CommRing F] [DecidableEq F]
    (artifact : ArithmeticArtifact n m F) (selected : List (Fin artifact.gates.length))
    (extension : Fin m → Polynomial n F)
    (certificate : Certificate (artifact.translation selected extension))
    (gateChecks : artifact.gates.all ArithmeticGate.check = true)
    (checked : check (artifact.translation selected extension) certificate = true)
    {values : Fin n → F} (holds : artifact.SourceHolds values) :
    ∃ extended : Fin m → F,
      (∀ wire, extended (artifact.placement wire) = values wire) ∧
      (∀ index ∈ selected, (artifact.gates.get index).expressionResidual extended = 0) := by
  obtain ⟨extended, projection, equations⟩ := witness_extension checked ((artifact.source_iff _).mpr holds)
  refine ⟨extended, projection, ?_⟩
  intro index member
  have equation := equations _ (List.mem_map.mpr ⟨index, member, rfl⟩)
  rw [(artifact.gates.get index).checked_value
    (List.all_eq_true.mp gateChecks _ (List.get_mem _ _))] at equation
  exact equation

end Airbender.Compiler
