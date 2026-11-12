module
public import Human.Compiler.LookupSelectors
public import Proven.KernelRfl

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeLookups.Proofs.JumpBranch
set_option maxRecDepth 32768

/-- The native query selectors are complete and every expansion follows actual definitions. -/
theorem binding :
    queryLocators (circuitFor (.pooled .jumpBranchSlt)) =
      .ok ((selectorsFor (.pooled .jumpBranchSlt)).map (fun selector => (selector.gate, selector.operand))) ∧
    (selectorsFor (.pooled .jumpBranchSlt)).all (fun selector =>
      match select (circuitFor (.pooled .jumpBranchSlt)) selector with | .ok _ => true | .error _ => false) = true := by
  constructor <;> kernel_rfl

end Airbender.Compiler.NativeLookups.Proofs.JumpBranch
