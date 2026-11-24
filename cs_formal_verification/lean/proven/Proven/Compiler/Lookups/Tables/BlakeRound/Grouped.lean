module
public import Human.Compiler.WorkerLookups
public import Proven.KernelRfl

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.BlakeRound
set_option maxRecDepth 32768

/-- The table operands of the cached capture, in gate order. -/
def tableSelectors : List NativeLookups.Selector := [
  ⟨2, 45, 1, []⟩,
  ⟨0, 90, 1, [178]⟩
]

/-- Each table operand belongs to the native output chain of its group. This module keeps the chain evaluation
    apart from the other table-side checks, within the module budget. -/
theorem tablesGrouped : NativeLookups.groupsAgree (circuitFor .blakeRound) tableSelectors = true := by
  kernel_rfl

end Airbender.Compiler.NativeWorkerLookups.Proofs.BlakeRound
