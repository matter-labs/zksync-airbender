module
public import Human.Compiler.LookupSelectors
public import Proven.KernelRfl

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeLookups.Proofs.ShiftBinop
set_option maxRecDepth 32768

/-- The native query selectors are complete and every expansion follows actual definitions. -/
theorem binding :
    queryLocators (circuitFor (.pooled .shiftBinop)) =
      .ok ((selectorsFor (.pooled .shiftBinop)).map (fun selector => (selector.gate, selector.operand))) ∧
    (selectorsFor (.pooled .shiftBinop)).all (fun selector =>
      match select (circuitFor (.pooled .shiftBinop)) selector with | .ok _ => true | .error _ => false) = true := by
  constructor <;> kernel_rfl

end Airbender.Compiler.NativeLookups.Proofs.ShiftBinop
