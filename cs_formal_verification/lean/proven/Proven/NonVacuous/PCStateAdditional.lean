module
public import Human.Helpers.Context.PCState.Theorems
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section
namespace Airbender.PCState

def nonVacuousContext : Context babyBearModulus 1 where
  program := #v[some 4]
  initialPC := 4
  terminalPC := 4
  initialTimestamp := (4, 0)
  terminalTimestamp := (4, 0)
  starts := [boundary 4 (4, 0)]
  ends := [boundary 4 (4, 0)]

theorem outgoing_bounds_witness : OutgoingBoundsSatisfiableClaim := by
  refine ⟨1, nonVacuousContext, encode 4, by decide +kernel, ?_, ?_, by decide +kernel, by decide +kernel⟩
  · constructor
    · exact List.Perm.refl _
    · intro state member
      simp only [nonVacuousContext, List.mem_singleton] at member
      subst state
      exact ⟨0, rfl⟩
  · exact ⟨boundary 4 (4, 0), List.mem_singleton_self _, rfl⟩
end Airbender.PCState
