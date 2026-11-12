module
public import Proven.Compiler.Lookups.Selectors.AddSub

@[expose] public section
namespace Airbender.Compiler.NativeLookups.Proofs.Introduction
set_option maxRecDepth 32768

/-- A nonempty supported capture supplies the separate non-vacuity statement. -/
theorem selectors_satisfiable_of (family : Trace.RVMachineDecoderFamily)
    (nonempty : selectorsFor family ≠ [])
    (covered : queryLocators (circuitFor family) =
      .ok ((selectorsFor family).map (fun selector => (selector.gate, selector.operand))))
    (resolved : (selectorsFor family).all (fun selector =>
      match select (circuitFor family) selector with | .ok _ => true | .error _ => false) = true) :
    CachedLookupSelectorsSatisfiableClaim :=
  ⟨family, nonempty, covered, resolved⟩

/-- The selector conditions hold for a nonempty native query list. -/
theorem satisfiable : CachedLookupSelectorsSatisfiableClaim := by
  have nonempty : selectorsFor (Trace.RVMachineDecoderFamily.pooled Trace.PooledFamily.addSub) ≠ [] := by
    intro empty
    have size : (selectorsFor (.pooled .addSub)).length = 15 := by kernel_rfl
    rw [empty] at size
    contradiction
  exact selectors_satisfiable_of _ nonempty Proofs.AddSub.binding.1 Proofs.AddSub.binding.2

end Airbender.Compiler.NativeLookups.Proofs.Introduction
