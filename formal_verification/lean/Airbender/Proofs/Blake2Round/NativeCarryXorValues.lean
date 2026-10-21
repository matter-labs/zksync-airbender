import Airbender.Proofs.Blake2Round.NativeXorKeyHelpers

namespace Airbender.Blake2Round.Proofs
open Airbender.Setup Airbender.Setup.Proofs NativeXorKeyHelpers
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

/-- The stored carry is a bounded value, not an assumed valid control. -/
theorem carry_value_get (kind : Fin 2) (n : Nat)
    (hn : n < (xorData (carryKind kind)).length) :
    (xorData (carryKind kind)).columns[2].get? n =
      some (n / (carryBase kind * carryBase kind)) := by
  have shape : (xorData (carryKind kind)).columns[2] = Column.mk #[
      .affine (carryBase kind * carryBase kind) 0 0,
      .affine (carryBase kind * carryBase kind) 1 0,
      .affine (carryBase kind * carryBase kind) 2 0] := by
    fin_cases kind <;> rfl
  rw [shape]
  fin_cases kind
  all_goals simp only [carryBase]
  · change n < 196608 at hn
    by_cases h0 : n < 65536
    · simp [Column.get?, getFromBlocks, Block.length, affine_constant_get, h0]
      omega
    · by_cases h1 : n - 65536 < 65536
      · simp [Column.get?, getFromBlocks, Block.length, affine_constant_get, h0, h1]
        omega
      · simp (disch := omega) [Column.get?, getFromBlocks, Block.length, affine_constant_get, h0, h1]
        omega
  · change n < 49152 at hn
    by_cases h0 : n < 16384
    · simp [Column.get?, getFromBlocks, Block.length, affine_constant_get, h0]
      omega
    · by_cases h1 : n - 16384 < 16384
      · simp [Column.get?, getFromBlocks, Block.length, affine_constant_get, h0, h1]
        omega
      · simp (disch := omega) [Column.get?, getFromBlocks, Block.length, affine_constant_get, h0, h1]
        omega


end Airbender.Blake2Round.Proofs
