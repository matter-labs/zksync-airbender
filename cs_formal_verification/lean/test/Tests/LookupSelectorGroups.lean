module
public import Human.Compiler.LookupSelectors
public import Proven.Compiler.ChainAddress
public import Proven.KernelRfl

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeLookups
set_option maxRecDepth 32768

/-- Gate 5 belongs to the range table, so changing its group rejects the selector. -/
example : groupsAgree (circuitFor (.pooled .addSub)) [⟨0, 5, 0, []⟩] = false := by
  kernel_rfl

/-- The unchanged gate and operand still have their native range group. -/
example : groupsAgree (circuitFor (.pooled .addSub)) [⟨1, 5, 0, []⟩] = true := by
  kernel_rfl

end Airbender.Compiler.NativeLookups
