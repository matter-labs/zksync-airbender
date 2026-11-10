import Airbender.Proofs.GKRProtocol.MemoryValueCongruence
import Airbender.Import.GKRProtocol.QueryFrameImport

namespace Airbender.Compiler.WorkerPortsChecks
open Lean Elab Command
set_option warningAsError true

private def emitChecked (command : Syntax) : CommandElabM Unit := do
  withEnableInfoTree false (elabCommand command)
  if (← get).messages.hasErrors then throwAbortCommand

/-- The planner supplies only a finite span. Each proposition is reconstructed
from the imported list and checked by the kernel; the final list is reassembled
with exact coverage. -/
elab "worker_checks_part " name:ident " input_list " items:term " test_fn " predicate:term
    " start " first:num " stop " last:num : command => do
  let mut proofs := #[]
  for index in [first.getNat:last.getNat] do
    let lemmaName := mkIdent (name.getId.appendAfter s!"Item{index}")
    emitChecked (← `(theorem $lemmaName : ($predicate) (($items).get ⟨$(quote index), by decide +kernel⟩) = true := by decide +kernel))
    proofs := proofs.push (← `($lemmaName))
  let blockName := mkIdent (name.getId.appendAfter "Block")
  emitChecked (← `(noncomputable def $blockName := (($items).drop $(quote first.getNat)).take $(quote (last.getNat - first.getNat))))
  let mut checked ← `(BoolChecks.nil)
  for proof in proofs.reverse do checked ← `(BoolChecks.cons $proof $checked)
  emitChecked (← `(theorem $name : ($blockName).all $predicate = true :=
    BoolChecks.all_true (predicate := $predicate) (items := $blockName) $checked))

end Airbender.Compiler.WorkerPortsChecks
