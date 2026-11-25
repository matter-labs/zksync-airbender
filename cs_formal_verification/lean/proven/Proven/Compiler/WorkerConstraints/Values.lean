module
public import Human.Compiler.WorkerPublicSetup
public import Human.Import.Coefficients
public import Proven.CircuitField
public import Proven.Compiler.NativeBridge
public import Proven.Compiler.Lookups.Membership
public import Proven.Compiler.LookupWitness

@[expose] public section
namespace Airbender.Compiler.WorkerConstraints
open NativeArithmetic
set_option warningAsError true

/-- Native and reviewed expressions use the same decoded Montgomery coefficient. -/
theorem coefficient_value (value : Coefficient) :
    coefficient value = (Artifact.signedCoefficient value : F) :=
  (CircuitField.signedScalar_cast (p := babyBearModulus) value.raw.val).symm

/-- A checked entry lookup gives the logical value at its actual physical placement. -/
theorem placed {circuit : Circuit} {physical : GKRAddress → F} {logical : Nat → F}
    (agreement : PlacementAgreement circuit physical logical) {position sourceIndex : Nat} {address : GKRAddress}
    (found : circuit.placement_data.entries.toList[position]? = some (sourceIndex, address)) :
    physical address = logical sourceIndex := by
  obtain ⟨bound, same⟩ := List.getElem?_eq_some_iff.mp found
  have included := List.getElem_mem bound
  rw [same] at included
  exact (agreement _ (by simpa using included)).symm

/-- A predicate holds on a list when it holds on the head and the tail. -/
theorem all_cons {Value : Type} {predicate : Value → Prop} {first : Value} {rest : List Value}
    (head : predicate first) (tail : ∀ value ∈ rest, predicate value) :
    ∀ value ∈ first :: rest, predicate value := by
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact head
  · exact tail value member

/-- Complete checked list segments preserve their predicate under concatenation. -/
theorem all_append {Value : Type} {predicate : Value → Prop} {first rest : List Value}
    (head : ∀ value ∈ first, predicate value) (tail : ∀ value ∈ rest, predicate value) :
    ∀ value ∈ first ++ rest, predicate value := by
  intro value member
  rcases List.mem_append.mp member with member | member
  · exact head value member
  · exact tail value member

/-- Each tuple emitted by the actual native selectors matches a public worker row. -/
theorem native_member {family : NativeWorkerLookups.Family} {physical : GKRAddress → F}
    {tuples : Fin 3 → List (List F)}
    (arguments : NativeLookups.Arguments (NativeWorkerLookups.circuitFor family)
      (NativeWorkerLookups.selectorsFor family) physical (NativeWorkerSetup.rows family))
    (binding : ∀ group, NativeLookups.requests (NativeWorkerLookups.circuitFor family)
      (NativeWorkerLookups.selectorsFor family) physical group = .ok (tuples group))
    {group : Fin 3} {values : List F} (member : values ∈ tuples group) :
    ∃ index, values = NativeWorkerSetup.rows family group index := by
  have same : arguments.tuples group = tuples group :=
    Except.ok.inj ((arguments.binding group).symm.trans (binding group))
  apply (arguments.matching group).member
  rw [same]
  exact member

/-- Per-tuple membership supplies exact native matching with natural multiplicities. -/
noncomputable def native_arguments {family : NativeWorkerLookups.Family} {physical : GKRAddress → F}
    (tuples : Fin 3 → List (List F))
    (binding : ∀ group, NativeLookups.requests (NativeWorkerLookups.circuitFor family)
      (NativeWorkerLookups.selectorsFor family) physical group = .ok (tuples group))
    (membership : ∀ group values, values ∈ tuples group →
      ∃ index, values = NativeWorkerSetup.rows family group index) :
    NativeLookups.Arguments (NativeWorkerLookups.circuitFor family)
      (NativeWorkerLookups.selectorsFor family) physical (NativeWorkerSetup.rows family) where
  tuples := tuples
  binding := binding
  matching group := LookupArgument.of_membership (NativeWorkerSetup.rows family group)
    (tuples group) (membership group)

end Airbender.Compiler.WorkerConstraints
