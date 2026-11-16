module
public import Human.Compiler.NativeLookups
public import Lean.Elab.Tactic.Omega

@[expose] public section
namespace Airbender.Compiler.NativeLookups
set_option warningAsError true

/-- The chain index gives distinct keys to distinct physical addresses. -/
theorem chainAddress_injective : Function.Injective chainAddress := by
  intro first second same
  cases first <;> cases second <;> simp only [chainAddress] at same
  all_goals try omega
  all_goals try (congr 1 <;> omega)
  case InnerLayer.InnerLayer leftLayer leftOffset rightLayer rightOffset =>
    have paired := Nat.mul_left_cancel (by decide : 0 < 8) (Nat.add_right_cancel same)
    obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.mp paired
    rfl
  case Cached.Cached leftLayer leftOffset rightLayer rightOffset =>
    have paired := Nat.mul_left_cancel (by decide : 0 < 8) (Nat.add_right_cancel same)
    obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.mp paired
    rfl
  case VirtualSetup.VirtualSetup leftKind rightKind =>
    cases leftKind <;> cases rightKind <;> simp_all

end Airbender.Compiler.NativeLookups
