module
public import Proven.Compiler.WorkerSelectors.Common

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.KeccakColumnParity
set_option maxRecDepth 32768

/-- Each operand of a public lookup chain with the group of its output, in output and chain order. -/
def chains : List ((Nat × Nat) × Fin 3) := [((22, 0), 2), ((22, 1), 2), ((21, 0), 2), ((21, 1), 2), ((24, 0), 2), ((24, 1), 2), ((23, 0), 2), ((23, 1), 2), ((18, 0), 2), ((18, 1), 2), ((17, 0), 2), ((17, 1), 2), ((20, 0), 2), ((20, 1), 2), ((19, 0), 2), ((19, 1), 2), ((30, 0), 2), ((30, 1), 2), ((29, 0), 2), ((29, 1), 2), ((31, 0), 2), ((31, 1), 2), ((74, 0), 2), ((26, 0), 2), ((26, 1), 2), ((25, 0), 2), ((25, 1), 2), ((28, 0), 2), ((28, 1), 2), ((27, 0), 2), ((27, 1), 2), ((34, 0), 0), ((34, 1), 0), ((33, 0), 0), ((33, 1), 0), ((36, 0), 0), ((36, 1), 0), ((35, 0), 0), ((35, 1), 0), ((42, 0), 0), ((42, 1), 0), ((41, 0), 0), ((41, 1), 0), ((43, 0), 0), ((43, 1), 0), ((82, 0), 0), ((38, 0), 0), ((38, 1), 0), ((37, 0), 0), ((37, 1), 0), ((40, 0), 0), ((40, 1), 0), ((39, 0), 0), ((39, 1), 0)]

/-- The kernel follows the actual native chains to these operands and groups. -/
theorem chain_groups : NativeLookups.chainGroups (circuitFor .columnParity) = .ok chains := by
  unfold NativeLookups.chainGroups
  rw [compiled_gates_toList]
  kernel_rfl

/-- A selector has the group of the one chain that contains its operand. -/
def grouping (selector : NativeLookups.Selector) : Bool :=
  (chains.filter (fun entry => entry.1 == (selector.gate, selector.operand))).map Prod.snd == [selector.group]

end Airbender.Compiler.NativeWorkerLookups.Proofs.KeccakColumnParity
