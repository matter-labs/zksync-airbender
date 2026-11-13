module
public import Human.Helpers.Context.PCState.Theorems
public import Human.Helpers.Core.BabyBearPrime

@[expose] public section
namespace Airbender.PCState

def nonVacuousContext : Context babyBearModulus 1 where
  program := #v[some 0]
  initialPC := 0
  terminalPC := 0
  initialTimestamp := (0, 0)
  terminalTimestamp := (0, 0)
  starts := [boundary 0 (0, 0)]
  ends := [boundary 0 (0, 0)]

theorem outgoing_bounds_witness : OutgoingBoundsSatisfiableClaim := by
  refine ⟨1, nonVacuousContext, encode 0, by decide +kernel, ?_, ?_, by decide +kernel⟩
  · constructor
    · exact List.Perm.refl _
    · intro state member
      simp only [nonVacuousContext, List.mem_singleton] at member
      subst state
      exact ⟨0, rfl⟩
  · exact ⟨boundary 0 (0, 0), List.mem_singleton_self _, rfl⟩
end Airbender.PCState
