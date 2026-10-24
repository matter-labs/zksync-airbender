import GKRProtocol.CacheSemantics
import GKRProtocol.Source
import GKRCompiler.Wiring

namespace Airbender.Compiler
set_option warningAsError true

structure CacheChallenges (R : Type) where
  lookupAlpha : R
  memoryGamma : R
  memoryPowers : Fin 6 → R

inductive CacheCoefficient where
  | base : Nat → CacheCoefficient
  | natural : Nat → CacheCoefficient
  | lookupPower : Nat → CacheCoefficient
  | memoryPower : Fin 6 → CacheCoefficient
  | memoryGamma
  | negativeOne
  deriving Repr, DecidableEq

def CacheCoefficient.value [CommRing R] (hom : Source.BaseField →+* R)
    (challenges : CacheChallenges R) : CacheCoefficient → R
  | .base raw => hom ((raw : Source.BaseField) * montgomeryInverse)
  | .natural scalar => hom (scalar : Source.BaseField)
  | .lookupPower index => challenges.lookupAlpha ^ index
  | .memoryPower index => challenges.memoryPowers index
  | .memoryGamma => challenges.memoryGamma
  | .negativeOne => -1

/-- The affine expression interpreted from an actual native cache relation.
The dependency list is retained separately from the expression, and is checked
against the independently imported graph's complete cache ports. -/
structure CacheBinding (R : Type) where
  output : GKRAddress
  dependencies : List GKRAddress
  program : AffineProgram GKRAddress R

def AffineProgram.inputs : AffineProgram Address R → List Address
  | .constant _ => []
  | .input address => [address]
  | .add left right => left.inputs ++ right.inputs
  | .scale _ inner => inner.inputs

def AffineProgram.mapCoefficients (map : S → R) : AffineProgram Address S → AffineProgram Address R
  | .constant scalar => .constant (map scalar)
  | .input address => .input address
  | .add left right => .add (left.mapCoefficients map) (right.mapCoefficients map)
  | .scale coefficient inner => .scale (map coefficient) (inner.mapCoefficients map)

theorem AffineProgram.mapCoefficients_inputs (program : AffineProgram Address S) (map : S → R) :
    (program.mapCoefficients map).inputs = program.inputs := by
  induction program with
  | constant scalar => rfl
  | input address => rfl
  | add left right leftProof rightProof => simp only [mapCoefficients, inputs, leftProof, rightProof]
  | scale coefficient inner proof => exact proof

def CacheBinding.mapCoefficients (map : S → R) (binding : CacheBinding S) : CacheBinding R :=
  ⟨binding.output, binding.dependencies, binding.program.mapCoefficients map⟩

def CacheBinding.portsValid (binding : CacheBinding R) : Bool :=
  binding.program.inputs == binding.dependencies

theorem CacheBinding.ports_sound {binding : CacheBinding R} (checked : binding.portsValid = true) :
    binding.program.inputs = binding.dependencies :=
  LawfulBEq.eq_of_beq checked

theorem CacheBinding.mapCoefficients_ports (binding : CacheBinding S) (map : S → R) :
    (binding.mapCoefficients map).portsValid = binding.portsValid := by
  simp only [mapCoefficients, portsValid, AffineProgram.mapCoefficients_inputs]

theorem CacheBinding.mapCoefficients_all {bindings : List (CacheBinding S)}
    (checked : bindings.all CacheBinding.portsValid = true) (map : S → R) :
    (bindings.map (CacheBinding.mapCoefficients map)).all CacheBinding.portsValid = true := by
  simpa only [List.all_map, Function.comp_def, mapCoefficients_ports] using checked

theorem CacheBinding.mapCoefficients_metadata (bindings : List (CacheBinding S)) (map : S → R) :
    (bindings.map (CacheBinding.mapCoefficients map)).map (fun cache => (cache.dependencies, cache.output)) =
      bindings.map (fun cache => (cache.dependencies, cache.output)) := by
  rw [List.map_map]
  rfl

/-- Canonical row materialization determines the cache; it is not an additional
free witness. -/
def CacheBinding.materialize [CommRing R] (binding : CacheBinding R)
    (rows : List Bool → GKRAddress → R) (row : List Bool) : R :=
  binding.program.value (rows row)

def CacheBinding.expectedClaim [CommRing R] (binding : CacheBinding R)
    (point : List R) (rows : List Bool → GKRAddress → R) : R :=
  binding.program.value (fun address => multilinearEvaluation point (fun row => rows row address))

/-- Native verifier cache binding follows from the materialized row values and
dependency claims at the same evaluation point, including at challenge roots.
No denominator or randomness assumption is needed. -/
theorem CacheBinding.claim_bound [CommRing R] (binding : CacheBinding R)
    (point : List R) (rows : List Bool → GKRAddress → R) :
    multilinearEvaluation point (binding.materialize rows) = binding.expectedClaim point rows :=
  binding.program.multilinear_commutes point rows

theorem CacheBinding.checked_claim [CommRing R] (binding : CacheBinding R)
    (point : List R) (rows : List Bool → GKRAddress → R) (cacheRows : List Bool → R)
    (materialized : ∀ row, cacheRows row = binding.materialize rows row) :
    multilinearEvaluation point cacheRows = binding.expectedClaim point rows := by
  have same : cacheRows = binding.materialize rows := funext materialized
  rw [same]
  exact binding.claim_bound point rows

end Airbender.Compiler
