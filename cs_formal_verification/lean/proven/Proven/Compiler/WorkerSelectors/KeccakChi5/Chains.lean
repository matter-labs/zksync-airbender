module
public import Proven.Compiler.WorkerSelectors.Common

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.KeccakChi5
set_option maxRecDepth 32768

/-- Each operand of a public lookup chain with the group of its output, in output and chain order. -/
def chains : List ((Nat × Nat) × Fin 3) := [((15, 0), 2), ((15, 1), 2), ((50, 0), 2), ((17, 0), 0), ((17, 1), 0), ((19, 0), 0), ((19, 1), 0), ((18, 0), 0), ((18, 1), 0), ((25, 0), 0), ((25, 1), 0), ((24, 0), 0), ((24, 1), 0), ((21, 0), 0), ((21, 1), 0), ((20, 0), 0), ((20, 1), 0), ((23, 0), 0), ((23, 1), 0), ((22, 0), 0), ((22, 1), 0)]

/-- The kernel follows the actual native chains to these operands and groups. -/
theorem chain_groups : NativeLookups.chainGroups (circuitFor .chi5) = .ok chains := by
  unfold NativeLookups.chainGroups
  rw [compiled_gates_toList]
  kernel_rfl

/-- A selector has the group of the one chain that contains its operand. -/
def grouping (selector : NativeLookups.Selector) : Bool :=
  (chains.filter (fun entry => entry.1 == (selector.gate, selector.operand))).map Prod.snd == [selector.group]

end Airbender.Compiler.NativeWorkerLookups.Proofs.KeccakChi5
