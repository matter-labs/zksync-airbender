import Airbender.Proofs.Keccak.ByteQueryBindings
import Airbender.Proofs.Keccak.FixedLookups

namespace Airbender.Keccak.Proofs.ByteQueryBindings
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-- Native membership expressed through the checked byte input columns. -/
theorem values {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 1048576)
    {control : Fin 4096 → Vector Nat 6} {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (setupTable control))) (operation : Fin 5) (byte : Fin 8) :
    ByteOperationFacts
      (byteTag (setupTable control) w ⟨8 * operation.val + byte.val, by omega⟩).val
      (w (102 + 24 * operation.val + byte.val)).val
      (w (110 + 24 * operation.val + byte.val)).val
      (w (118 + 24 * operation.val + byte.val)).val := by
  have query := byte_lookup_checks hp h ⟨8 * operation.val + byte.val, by omega⟩
  rcases columns (setupTable control) w operation byte with ⟨a, b, c⟩
  change ByteOperationFacts
    ((byteQuery (setupTable control) ⟨8 * operation.val + byte.val, by omega⟩).entry.toArray[7]!.eval
      (Verification.environment w)).val
    ((byteQuery (setupTable control) ⟨8 * operation.val + byte.val, by omega⟩).entry.toArray[0]!.eval
      (Verification.environment w)).val
    ((byteQuery (setupTable control) ⟨8 * operation.val + byte.val, by omega⟩).entry.toArray[1]!.eval
      (Verification.environment w)).val
    ((byteQuery (setupTable control) ⟨8 * operation.val + byte.val, by omega⟩).entry.toArray[2]!.eval
      (Verification.environment w)).val at query
  rw [a, b, c] at query
  simpa only [byteTag, Array.back!, Vector.size_toArray, byte_query_arity] using query

end Airbender.Keccak.Proofs.ByteQueryBindings
