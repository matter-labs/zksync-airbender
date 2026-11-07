import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring

namespace Airbender.Compiler
set_option warningAsError true

/-- Multilinear evaluation is a normalized weighted sum over rows. The
normalization equation is explicit and can be instantiated by the GKR eq table. -/
def weightedEvaluation [CommRing R] (weights values : Fin rows → R) : R :=
  ∑ row, weights row * values row

theorem weightedEvaluation_constant [CommRing R] (weights : Fin rows → R)
    (normalized : ∑ row, weights row = 1) (constant : R) :
    weightedEvaluation weights (fun _ => constant) = constant := by
  unfold weightedEvaluation
  rw [← Finset.sum_mul, normalized, one_mul]

theorem weightedEvaluation_add [CommRing R] (weights left right : Fin rows → R) :
    weightedEvaluation weights (fun row => left row + right row) =
      weightedEvaluation weights left + weightedEvaluation weights right := by
  simp [weightedEvaluation, mul_add, Finset.sum_add_distrib]

theorem weightedEvaluation_scale [CommRing R] (weights values : Fin rows → R) (scalar : R) :
    weightedEvaluation weights (fun row => scalar * values row) =
      scalar * weightedEvaluation weights values := by
  simp only [weightedEvaluation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro row _
  ring

theorem weightedEvaluation_sum [CommRing R] (weights : Fin rows → R)
    (values : Fin inputs → Fin rows → R) :
    weightedEvaluation weights (fun row => ∑ input, values input row) =
      ∑ input, weightedEvaluation weights (values input) := by
  simp only [weightedEvaluation, Finset.mul_sum]
  exact Finset.sum_comm

structure AffineCache (Address R : Type) (inputs : Nat) where
  constant : R
  slots : Fin inputs → Address
  coefficients : Fin inputs → R

def AffineCache.value [CommRing R] (cache : AffineCache Address R inputs)
    (values : Address → R) : R :=
  cache.constant + ∑ input, cache.coefficients input * values (cache.slots input)

/-- A verifier can bind an affine cache claim from its dependency evaluations
at the same point. No separate free cache value is assumed. This identity is
valid for arbitrary challenges and row values. -/
theorem AffineCache.evaluation_commutes [CommRing R]
    (cache : AffineCache Address R inputs) (weights : Fin rows → R)
    (normalized : ∑ row, weights row = 1) (values : Fin rows → Address → R) :
    weightedEvaluation weights (fun row => cache.value (values row)) =
      cache.value (fun address => weightedEvaluation weights (fun row => values row address)) := by
  unfold value
  rw [weightedEvaluation_add, weightedEvaluation_constant weights normalized, weightedEvaluation_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro input _
  exact weightedEvaluation_scale _ _ _

def linearize [CommRing R] (alpha : R) (values : Fin width → R) : R :=
  ∑ column, alpha ^ column.val * values column

theorem linearize_fields [CommRing F] [CommRing R] (hom : F →+* R) (alpha : R)
    (source lowered : Fin width → F) (same : ∀ column, source column = lowered column) :
    linearize alpha (hom ∘ source) = linearize alpha (hom ∘ lowered) := by
  unfold linearize
  apply Finset.sum_congr rfl
  intro column _
  rw [Function.comp_apply, Function.comp_apply, same column]

/-- Affine expressions are the operations used by the native cache binder.
Challenge values are coefficients, so this excludes multiplying two witness
columns. -/
inductive AffineProgram (Address R : Type) where
  | constant : R → AffineProgram Address R
  | input : Address → AffineProgram Address R
  | add : AffineProgram Address R → AffineProgram Address R → AffineProgram Address R
  | scale : R → AffineProgram Address R → AffineProgram Address R

def AffineProgram.value [CommRing R] (values : Address → R) : AffineProgram Address R → R
  | .constant scalar => scalar
  | .input address => values address
  | .add left right => left.value values + right.value values
  | .scale coefficient inner => coefficient * inner.value values

theorem AffineProgram.evaluation_commutes [CommRing R]
    (program : AffineProgram Address R) (weights : Fin rows → R)
    (normalized : ∑ row, weights row = 1) (values : Fin rows → Address → R) :
    weightedEvaluation weights (fun row => program.value (values row)) =
      program.value (fun address => weightedEvaluation weights (fun row => values row address)) := by
  induction program with
  | constant constant => exact weightedEvaluation_constant weights normalized constant
  | input address => rfl
  | add left right leftProof rightProof =>
    change weightedEvaluation weights (fun row => left.value (values row) + right.value (values row)) = _
    rw [weightedEvaluation_add, leftProof, rightProof]
    rfl
  | scale coefficient input proof =>
    change weightedEvaluation weights (fun row => coefficient * input.value (values row)) = _
    rw [weightedEvaluation_scale, proof]
    rfl

/-- Recursive multilinear extension on the Boolean cube, with the first list
entry as the first coordinate. This supplies normalization without an extra
premise about a separately supplied table of weights. -/
def multilinearEvaluation [CommRing R] : List R → (List Bool → R) → R
  | [], values => values []
  | coordinate :: point, values =>
      (1 - coordinate) * multilinearEvaluation point (fun row => values (false :: row)) +
        coordinate * multilinearEvaluation point (fun row => values (true :: row))

theorem multilinearEvaluation_constant [CommRing R] (point : List R) (constant : R) :
    multilinearEvaluation point (fun _ => constant) = constant := by
  induction point with
  | nil => rfl
  | cons coordinate point proof => simp only [multilinearEvaluation, proof]; ring

theorem multilinearEvaluation_add [CommRing R] (point : List R) (left right : List Bool → R) :
    multilinearEvaluation point (fun row => left row + right row) =
      multilinearEvaluation point left + multilinearEvaluation point right := by
  induction point generalizing left right with
  | nil => rfl
  | cons coordinate point proof => simp only [multilinearEvaluation, proof]; ring

theorem multilinearEvaluation_scale [CommRing R] (point : List R)
    (coefficient : R) (values : List Bool → R) :
    multilinearEvaluation point (fun row => coefficient * values row) =
      coefficient * multilinearEvaluation point values := by
  induction point generalizing values with
  | nil => rfl
  | cons coordinate point proof => simp only [multilinearEvaluation, proof]; ring

theorem AffineProgram.multilinear_commutes [CommRing R]
    (program : AffineProgram Address R) (point : List R) (values : List Bool → Address → R) :
    multilinearEvaluation point (fun row => program.value (values row)) =
      program.value (fun address => multilinearEvaluation point (fun row => values row address)) := by
  induction program with
  | constant constant => exact multilinearEvaluation_constant point constant
  | input address => rfl
  | add left right leftProof rightProof =>
    change multilinearEvaluation point (fun row => left.value (values row) + right.value (values row)) = _
    rw [multilinearEvaluation_add, leftProof, rightProof]
    rfl
  | scale coefficient input proof =>
    change multilinearEvaluation point (fun row => coefficient * input.value (values row)) = _
    rw [multilinearEvaluation_scale, proof]
    rfl

end Airbender.Compiler
