module
public import Human.Import.Schema
public import Human.Helpers.Core.Field
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section

namespace Airbender.Compiler.NativeArithmetic

abbrev F := ZMod babyBearModulus

/-- Decode a serialized BabyBear Montgomery coefficient. -/
def coefficient (value : Coefficient) : F := (value.raw.val : F) * montgomeryInverse

/-- Evaluate the native sparse affine relation at physical addresses. -/
def linear (relation : LinearRelation) (values : GKRAddress → F) : F :=
  relation.linear_terms.foldl (fun result (scalar, address) => result + coefficient scalar * values address)
    (coefficient relation.constant)

/-- Evaluate the native sparse quadratic relation. -/
def quadratic (relation : CompiledMaxQuadraticGKRRelation) (values : GKRAddress → F) : F :=
  relation.quadratic_terms.foldl (fun result (left, terms) =>
    terms.foldl (fun result (scalar, right) => result + coefficient scalar * values left * values right) result)
    (linear ⟨relation.linear_terms, relation.constant⟩ values)

/-- Evaluate one equation in a native batch of sparse quadratic constraints. -/
def batchedQuadratic (relation : MaxQuadraticConstraintsGKRRelation) (index : Nat)
    (values : GKRAddress → F) : F :=
  let scalar := fun (terms : Array (Coefficient × Nat)) =>
    terms.foldl (fun sum term => if term.2 = index then sum + coefficient term.1 else sum) 0
  relation.quadratic_terms.foldl (fun sum term =>
    sum + scalar term.2 * values term.1.1 * values term.1.2)
    (relation.linear_terms.foldl (fun sum term => sum + scalar term.2 * values term.1)
      (scalar relation.constants))

/-- Base-field equations supplied by native gate acceptance. Lookup and extension gates have separate interfaces. -/
def GateHolds (relation : GKRRelation) (values : GKRAddress → F) : Prop :=
  match relation with
  | .LinearBaseFieldRelation input output => values output = linear input values
  | .MaxQuadratic input _ output => values output = quadratic input values
  | .EnforceSingleMaxQuadraticConstraint input _ => quadratic input values = 0
  | .CopyInBaseField input output => values output = values input
  | .MaterializeSingleLookupInput input output _ => values output = linear input.input values
  | .EnforceConstraintsMaxQuadratic input =>
    ∀ index, batchedQuadratic input index values = 0
  | _ => True

/-- Scalar caches carry the exact native affine value. Other cache variants have extension outputs. -/
def CacheHolds (output : GKRAddress) (relation : GKRCacheRelation) (values : GKRAddress → F) : Prop :=
  match relation with
  | .SingleColumnLookup input _ => values output = linear input.input values
  | _ => True

/-- All native base-field gates and scalar caches of the captured compiled layers hold. -/
def Holds (circuit : Circuit) (values : GKRAddress → F) : Prop :=
  ∀ layer ∈ circuit.layers,
    (∀ entry ∈ layer.cached_relations, CacheHolds entry.1 entry.2 values) ∧
    (∀ gate ∈ layer.gates ++ layer.gates_with_external_connections, GateHolds gate.enforced_relation values)

/-- Logical source columns use the artifact's actual physical placements. No arithmetic result is supplied. -/
def PlacementAgreement (circuit : Circuit) (physical : GKRAddress → F) (logical : Nat → F) : Prop :=
  ∀ entry ∈ circuit.placement_data.entries, logical entry.1 = physical entry.2

end Airbender.Compiler.NativeArithmetic
