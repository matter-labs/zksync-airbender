module
public import Proven.Compiler.WorkerSelectors.Common

@[expose] public section
set_option warningAsError true
namespace Airbender.Compiler.NativeWorkerLookups.Proofs.KeccakThetaRho
set_option maxRecDepth 32768

/-- Each operand of a public lookup chain with the group of its output, in output and chain order. -/
def chains : List ((Nat × Nat) × Fin 3) := [((19, 0), 2), ((19, 1), 2), ((93, 0), 2), ((38, 0), 0), ((38, 1), 0), ((37, 0), 0), ((37, 1), 0), ((40, 0), 0), ((40, 1), 0), ((39, 0), 0), ((39, 1), 0), ((34, 0), 0), ((34, 1), 0), ((33, 0), 0), ((33, 1), 0), ((36, 0), 0), ((36, 1), 0), ((35, 0), 0), ((35, 1), 0), ((45, 0), 0), ((45, 1), 0), ((94, 0), 0), ((42, 0), 0), ((42, 1), 0), ((41, 0), 0), ((41, 1), 0), ((44, 0), 0), ((44, 1), 0), ((43, 0), 0), ((43, 1), 0), ((22, 0), 0), ((22, 1), 0), ((21, 0), 0), ((21, 1), 0), ((24, 0), 0), ((24, 1), 0), ((23, 0), 0), ((23, 1), 0), ((30, 0), 0), ((30, 1), 0), ((29, 0), 0), ((29, 1), 0), ((32, 0), 0), ((32, 1), 0), ((31, 0), 0), ((31, 1), 0), ((26, 0), 0), ((26, 1), 0), ((25, 0), 0), ((25, 1), 0), ((28, 0), 0), ((28, 1), 0), ((27, 0), 0), ((27, 1), 0)]

/-- The kernel follows the actual native chains to these operands and groups. -/
theorem chain_groups : NativeLookups.chainGroups (circuitFor .thetaRho) = .ok chains := by
  unfold NativeLookups.chainGroups
  rw [compiled_gates_toList]
  kernel_rfl

/-- A selector has the group of the one chain that contains its operand. -/
def grouping (selector : NativeLookups.Selector) : Bool :=
  (chains.filter (fun entry => entry.1 == (selector.gate, selector.operand))).map Prod.snd == [selector.group]

end Airbender.Compiler.NativeWorkerLookups.Proofs.KeccakThetaRho
