module
meta import Human.Import.SetupEmit

meta section
open Lean Elab Command Airbender.Import.Setup

/-! The compiled grid comparison must reject errors in the formula and in the JSON rows. -/

run_cmd do
  let json := #[(0, Block.dense #[0, 1, 2, 3])]
  let correct := [Block.grid 4 (.digit 1 4)]
  match checkColumn json correct with
  | .ok () => pure ()
  | .error e => throwError "Correct grid rejected: {e}"
  match checkColumn json [Block.grid 4 (.digit 2 4)] with
  | .error _ => pure ()
  | .ok () => throwError "Wrong grid accepted"
  match checkColumn #[(0, Block.dense #[0, 1, 2, 9])] correct with
  | .error _ => pure ()
  | .ok () => throwError "Wrong JSON row accepted"
