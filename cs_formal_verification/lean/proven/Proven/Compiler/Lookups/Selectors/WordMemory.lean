module
public import Human.Compiler.LookupSelectors
public import Proven.KernelRfl

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeLookups.Proofs.WordMemory
set_option maxRecDepth 32768

/-- The native query selectors are complete and every expansion follows actual definitions. -/
theorem binding :
    queryLocators (circuitFor (.pooled .wordMemory)) =
      .ok ((selectorsFor (.pooled .wordMemory)).map (fun selector => (selector.gate, selector.operand))) ∧
    (selectorsFor (.pooled .wordMemory)).all (fun selector =>
      match select (circuitFor (.pooled .wordMemory)) selector with | .ok _ => true | .error _ => false) = true := by
  constructor <;> kernel_rfl

end Airbender.Compiler.NativeLookups.Proofs.WordMemory
