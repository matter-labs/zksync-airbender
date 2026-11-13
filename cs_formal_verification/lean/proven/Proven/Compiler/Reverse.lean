module
public import Proven.Compiler.NativeBridge

@[expose] public section
namespace Airbender.Compiler.NativeBridge
open NativeArithmetic
set_option warningAsError true

def Clause.supported : Clause → Bool
  | .gate (.EnforceConstraintsMaxQuadratic _) => false
  | _ => true

private theorem cache_of_zero (output : GKRAddress) (relation : GKRCacheRelation) (physical : GKRAddress → F)
    (zero : (Clause.cache output relation).residual physical = 0) : CacheHolds output relation physical := by
  cases relation <;> first | trivial | exact sub_eq_zero.mp zero

private theorem gate_of_zero (relation : GKRRelation) (physical : GKRAddress → F)
    (supported : (Clause.gate relation).supported = true)
    (zero : (Clause.gate relation).residual physical = 0) : GateHolds relation physical := by
  cases relation <;> first | trivial | exact sub_eq_zero.mp zero

/-- Complete native sparse equations imply the public gate predicate when there is no batched relation. -/
theorem native_of_base {circuit : Circuit} {physical : GKRAddress → F}
    (supported : (clauses circuit).all Clause.supported = true)
    (zero : ∀ clause ∈ baseClauses circuit, clause.residual physical = 0) : Holds circuit physical := by
  have all (clause : Clause) (member : clause ∈ clauses circuit) : clause.residual physical = 0 := by
    by_cases base : clause.isBase = true
    · exact zero clause (List.mem_filter.mpr ⟨member, base⟩)
    · cases clause with
      | cache output relation => cases relation <;> first | rfl | simp [Clause.isBase] at base
      | gate relation => cases relation <;> first | rfl | simp [Clause.isBase] at base
  intro layer present
  constructor
  · intro entry member
    apply cache_of_zero
    apply all
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    refine ⟨layer, by simpa using present, ?_⟩
    exact List.mem_map.mpr ⟨entry, by simpa using member, rfl⟩
  · intro entry member
    have clauseMember : Clause.gate entry.enforced_relation ∈ clauses circuit := by
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      refine ⟨layer, by simpa using present, ?_⟩
      exact List.mem_map.mpr ⟨entry, by simpa using member, rfl⟩
    exact gate_of_zero _ physical (List.all_eq_true.mp supported _ clauseMember) (all _ clauseMember)
theorem cons_zero {head : Clause} {tail : List Clause} {physical : GKRAddress → F}
    (first : head.residual physical = 0) (rest : ∀ clause ∈ tail, clause.residual physical = 0) :
    ∀ clause ∈ head :: tail, clause.residual physical = 0 := by
  intro clause member
  rcases List.mem_cons.mp member with rfl | included
  · exact first
  · exact rest clause included

theorem append_zero {first rest : List Clause} {physical : GKRAddress → F}
    (left : ∀ clause ∈ first, clause.residual physical = 0)
    (right : ∀ clause ∈ rest, clause.residual physical = 0) :
    ∀ clause ∈ first ++ rest, clause.residual physical = 0 := by
  intro clause member
  exact (List.mem_append.mp member).elim (left clause) (right clause)

end Airbender.Compiler.NativeBridge
