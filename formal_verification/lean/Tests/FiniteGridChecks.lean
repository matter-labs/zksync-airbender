import Airbender.Proofs.Tables.FiniteGridChecks

namespace Tests.FiniteGridChecks
open Airbender.Verification.FiniteGridChecks
set_option warningAsError true

def left (a : Fin 2) (b : Fin 3) (c : Fin 4) : Nat := a.val * 12 + b.val * 4 + c.val
def right (a : Fin 2) (b : Fin 3) (c : Fin 4) : Nat := c.val + 4 * b.val + 12 * a.val

theorem checked : check 2 3 4 left right = true := by decide +kernel
theorem original (a : Fin 2) (b : Fin 3) (c : Fin 4) : left a b c = right a b c :=
  check_sound 2 3 4 left right checked a b c

def wrong (a : Fin 2) (b : Fin 3) (c : Fin 4) : Nat :=
  if a.val = 1 ∧ b.val = 2 ∧ c.val = 3 then right a b c + 1 else right a b c

theorem final_cell_rejected : check 2 3 4 left wrong = false := by decide +kernel

end Tests.FiniteGridChecks
