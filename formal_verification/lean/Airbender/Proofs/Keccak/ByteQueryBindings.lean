import Airbender.Proofs.Keccak.Tags

namespace Airbender.Keccak.Proofs.ByteQueryBindings
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-- Checked scalar inputs of the forty native byte queries. -/
theorem columns {p : Nat} [Fact p.Prime] (setup : Table (ZMod p) (fields 8))
    (w : Nat → ZMod p) (operation : Fin 5) (byte : Fin 8) :
    let q := byteQuery setup ⟨8 * operation.val + byte.val, by omega⟩
    q.entry.toArray[0]!.eval (Verification.environment w) = w (102 + 24 * operation.val + byte.val) ∧
    q.entry.toArray[1]!.eval (Verification.environment w) = w (110 + 24 * operation.val + byte.val) ∧
    q.entry.toArray[2]!.eval (Verification.environment w) = w (118 + 24 * operation.val + byte.val) := by
  fin_cases operation <;> fin_cases byte
  all_goals simp [byteQuery, importedConstraints, FlatOperation.lookups,
    Expression.eval, Verification.environment]

end Airbender.Keccak.Proofs.ByteQueryBindings
