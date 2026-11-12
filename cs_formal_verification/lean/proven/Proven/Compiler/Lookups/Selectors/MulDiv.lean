module
public import Human.Compiler.LookupSelectors
public import Proven.KernelRfl

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeLookups.Proofs.MulDiv
set_option maxRecDepth 32768

/-- The native query selectors are complete and every expansion follows actual definitions. -/
theorem binding :
    queryLocators (circuitFor (.pooled .mulDiv)) =
      .ok ((selectorsFor (.pooled .mulDiv)).map (fun selector => (selector.gate, selector.operand))) ∧
    (selectorsFor (.pooled .mulDiv)).all (fun selector =>
      match select (circuitFor (.pooled .mulDiv)) selector with | .ok _ => true | .error _ => false) = true := by
  constructor <;> kernel_rfl

end Airbender.Compiler.NativeLookups.Proofs.MulDiv
