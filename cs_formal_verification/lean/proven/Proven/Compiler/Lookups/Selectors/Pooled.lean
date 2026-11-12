module
public import Proven.Compiler.Lookups.Selectors.AddSub
public import Proven.Compiler.Lookups.Selectors.JumpBranch
public import Proven.Compiler.Lookups.Selectors.MulDiv
public import Proven.Compiler.Lookups.Selectors.ShiftBinop
public import Proven.Compiler.Lookups.Selectors.WordMemory
public import Proven.Compiler.Lookups.Selectors.SubwordMemory

@[expose] public section
namespace Airbender.Compiler.NativeLookups.Proofs.Pooled
set_option maxRecDepth 32768

/-- Every unrolled CPU family has complete resolved native query selectors. -/
theorem binding (family : Trace.PooledFamily) :
    queryLocators (circuitFor (.pooled family)) =
      .ok ((selectorsFor (.pooled family)).map (fun selector => (selector.gate, selector.operand))) ∧
    (selectorsFor (.pooled family)).all (fun selector =>
      match select (circuitFor (.pooled family)) selector with | .ok _ => true | .error _ => false) = true := by
  cases family with
  | addSub => exact Proofs.AddSub.binding
  | wordMemory => exact Proofs.WordMemory.binding
  | jumpBranchSlt => exact Proofs.JumpBranch.binding
  | mulDiv => exact Proofs.MulDiv.binding
  | shiftBinop => exact Proofs.ShiftBinop.binding
  | subwordMemory => exact Proofs.SubwordMemory.binding

end Airbender.Compiler.NativeLookups.Proofs.Pooled
