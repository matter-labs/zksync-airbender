import Airbender.Proofs.Blake2Round.Claims

namespace Tests.Blake2RoundCall
open Airbender Arithmetic
set_option warningAsError true
set_option maxRecDepth 4096

theorem full_round_controls (flags : Fin 8) :
    Blake2Round.Control.next^[10] ⟨0, flags.val + 8⟩ = ⟨0, flags.val⟩ := by
  fin_cases flags <;> decide

theorem reduced_round_controls (flags : Fin 8) :
    Blake2Round.Control.next^[7] ⟨0, flags.val + 8⟩ = ⟨0, flags.val + 1024⟩ := by
  fin_cases flags <;> decide

theorem another_round_rejected [Fact p.Prime] (hp : 8192 ≤ p)
    {setup : Table (ZMod p) (fields 4)} {w : Nat → ZMod p} {flags : Fin 8} {round other : Fin 10}
    (control : (w Blake2Round.Variables.controlReadHi).val = flags.val + 8 * 2 ^ round.val)
    (different : other ≠ round) (wrong : w Blake2Round.Variables.roundBits[other] = 1) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2Round.importedConstraints setup) := by
  intro holds
  have mask := Blake2Round.Proofs.exclusive_mask hp holds flags round control other
  rw [if_neg different, wrong] at mask
  exact one_ne_zero mask

theorem changed_request_flags_rejected [Fact p.Prime] (hp : 8192 ≤ p)
    {setup : Table (ZMod p) (fields 4)} {w : Nat → ZMod p} {flags : Fin 8} {round : Fin 10}
    (control : (w Blake2Round.Variables.controlReadHi).val = flags.val + 8 * 2 ^ round.val)
    (wrong : (w 139).val ≠ flags.val % 2 ∨ (w 140).val ≠ flags.val / 2 % 2 ∨
      (w 141).val ≠ flags.val / 4) :
    ¬ FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (Blake2Round.importedConstraints setup) := by
  intro holds
  obtain ⟨reduced, right, compression⟩ := Blake2Round.Proofs.control_flags hp holds flags round control
  rcases wrong with wrong | wrong | wrong
  · exact wrong reduced
  · exact wrong right
  · exact wrong compression

end Tests.Blake2RoundCall
