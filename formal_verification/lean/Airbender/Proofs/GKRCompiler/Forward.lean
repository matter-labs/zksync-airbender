import Airbender.Proofs.GKRCompiler.Arithmetic

namespace Airbender.Compiler
set_option warningAsError true

/-- Logical/oracle inputs form an initial coordinate segment; only computed
native coordinates need certificate-provided extension polynomials. -/
def initialExtension [CommRing F] (bound : n ≤ m) (computed : Fin (m - n) → Polynomial n F)
    (index : Fin m) : Polynomial n F :=
  if input : index.val < n then atom ⟨index.val, input⟩
  else computed ⟨index.val - n, by omega⟩

theorem initialExtension_at [CommRing F] (bound : n ≤ m) (computed : Fin (m - n) → Polynomial n F)
    (index : Fin n) : initialExtension bound computed (index.castLE bound) = atom index := by
  simp only [initialExtension, Fin.val_castLE, dif_pos index.isLt]

theorem initialExtension_projection [CommRing F] [DecidableEq F] (bound : n ≤ m)
    (computed : Fin (m - n) → Polynomial n F) (index : Fin n) :
    equal (initialExtension bound computed (index.castLE bound)) (atom index) = true := by
  rw [initialExtension_at]
  simp only [equal, decide_true]

/-- A forward certificate need not assert the converse for explicit primitive
inputs. It must check every lowered relation and preserve every source input. -/
structure ForwardCertificate (translation : Translation n m F) where
  identities : Fin translation.lowered.length → Combination translation.source

def ForwardCertificate.Valid [CommRing F] [DecidableEq F] {translation : Translation n m F}
    (certificate : ForwardCertificate translation) : Prop :=
  (∀ wire, equal (translation.extension (translation.projection wire)) (atom wire) = true) ∧
  (∀ index : Fin translation.lowered.length,
    equal (substitute translation.extension (translation.lowered.get index))
      (combination translation.source (certificate.identities index)) = true)

def Translation.extend [CommRing F] (translation : Translation n m F) (values : Fin n → F) : Fin m → F :=
  fun wire => evaluate values (translation.extension wire)

theorem ForwardCertificate.projection [CommRing F] [DecidableEq F]
    {translation : Translation n m F} {certificate : ForwardCertificate translation}
    (valid : certificate.Valid) (values : Fin n → F) (wire : Fin n) :
    translation.extend values (translation.projection wire) = values wire :=
  (equal_sound (valid.1 wire) values).trans (evaluate_atom values wire)

theorem ForwardCertificate.satisfies [CommRing F] [DecidableEq F]
    {translation : Translation n m F} {certificate : ForwardCertificate translation}
    (valid : certificate.Valid) {values : Fin n → F} (holds : Satisfies translation.source values) :
    Satisfies translation.lowered (translation.extend values) := by
  intro relation member
  obtain ⟨index, rfl⟩ := List.mem_iff_get.mp member
  have same := equal_sound (valid.2 index) values
  rw [evaluate_substitute] at same
  exact same.trans (combination_zero holds _)

structure ArithmeticExtension (n m : Nat) (F : Type) where
  source : List (Polynomial n F)
  gates : List (ArithmeticGate m F)
  projection : Fin n → Fin m
  extension : Fin m → Polynomial n F

def ArithmeticExtension.translation [CommRing F] (artifact : ArithmeticExtension n m F) : Translation n m F :=
  ⟨artifact.source, artifact.gates.map ArithmeticGate.inputResidual, artifact.projection, artifact.extension⟩

/-- This result covers the complete supplied native arithmetic relation, with
no selected-gate slice. Importers reconstruct that list from every actual base
gate, scalar materializer and scalar base cache in the retained compiler output. -/
theorem ArithmeticExtension.forward [CommRing F] [DecidableEq F] (artifact : ArithmeticExtension n m F)
    (certificate : ForwardCertificate artifact.translation) (valid : certificate.Valid)
    (gateChecks : artifact.gates.all ArithmeticGate.check = true)
    {values : Fin n → F} (holds : Satisfies artifact.source values) :
    (∀ wire, artifact.translation.extend values (artifact.projection wire) = values wire) ∧
      (∀ gate ∈ artifact.gates, gate.expressionResidual (artifact.translation.extend values) = 0) := by
  refine ⟨ForwardCertificate.projection valid values, ?_⟩
  have equations := ForwardCertificate.satisfies valid holds
  intro gate member
  have equation := equations _ (List.mem_map.mpr ⟨gate, member, rfl⟩)
  rw [gate.checked_value (List.all_eq_true.mp gateChecks gate member)] at equation
  exact equation

end Airbender.Compiler
