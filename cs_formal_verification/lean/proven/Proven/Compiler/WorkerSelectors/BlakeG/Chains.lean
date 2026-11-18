module
public import Proven.Compiler.WorkerSelectors.Common

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.BlakeG
set_option maxRecDepth 32768

/-- Each operand of a public lookup chain with the group of its output, in output and chain order. -/
def chains : List ((Nat × Nat) × Fin 3) := [((11, 0), 2), ((11, 1), 2), ((13, 0), 2), ((13, 1), 2), ((12, 0), 2), ((12, 1), 2), ((19, 0), 2), ((19, 1), 2), ((18, 0), 2), ((18, 1), 2), ((21, 0), 2), ((21, 1), 2), ((20, 0), 2), ((20, 1), 2), ((15, 0), 2), ((15, 1), 2), ((14, 0), 2), ((14, 1), 2), ((17, 0), 2), ((17, 1), 2), ((16, 0), 2), ((16, 1), 2), ((23, 0), 0), ((23, 1), 0), ((22, 0), 0), ((22, 1), 0), ((25, 0), 0), ((25, 1), 0), ((24, 0), 0), ((24, 1), 0), ((31, 0), 0), ((31, 1), 0), ((30, 0), 0), ((30, 1), 0), ((27, 0), 0), ((27, 1), 0), ((26, 0), 0), ((26, 1), 0), ((29, 0), 0), ((29, 1), 0), ((28, 0), 0), ((28, 1), 0)]

/-- The kernel follows the actual native chains to these operands and groups. -/
theorem chain_groups : NativeLookups.chainGroups (circuitFor .blakeG) = .ok chains := by
  unfold NativeLookups.chainGroups
  rw [compiled_gates_toList]
  kernel_rfl

/-- A selector has the group of the one chain that contains its operand. -/
def grouping (selector : NativeLookups.Selector) : Bool :=
  (chains.filter (fun entry => entry.1 == (selector.gate, selector.operand))).map Prod.snd == [selector.group]

end Airbender.Compiler.NativeWorkerLookups.Proofs.BlakeG
