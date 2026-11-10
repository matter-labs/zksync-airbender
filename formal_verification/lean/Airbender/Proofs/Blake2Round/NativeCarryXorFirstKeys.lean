import Airbender.Proofs.Blake2Round.NativeXorKeyHelpers

namespace Airbender.Blake2Round.Proofs
open Airbender.Setup Airbender.Setup.Proofs NativeXorKeyHelpers
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

/-- Carry tables repeat every input pair for exactly the three carry values. -/
theorem carry_first_get (kind : Fin 2) (n : Nat)
    (hn : n < (xorData (carryKind kind)).length) :
    (xorData (carryKind kind)).columns[0].get? n =
      some (n / carryBase kind % carryBase kind) := by
  have shape : (xorData (carryKind kind)).columns[0] = Column.mk #[
      .periodic (carryBase kind) 1 (Array.replicate (carryBase kind) 0),
      .periodic (carryBase kind) 1 (Array.replicate (carryBase kind) 0),
      .periodic (carryBase kind) 1 (Array.replicate (carryBase kind) 0)] := by
    fin_cases kind <;> rfl
  rw [shape]
  fin_cases kind
  all_goals simp only [carryBase]
  · change n < 196608 at hn
    by_cases h0 : n < 65536
    · simp [Column.get?, getFromBlocks, Block.length, h0, periodic_constant_get]
      omega
    · by_cases h1 : n - 65536 < 65536
      · simp [Column.get?, getFromBlocks, Block.length, h0, h1, periodic_constant_get]
        omega
      · simp (disch := omega) [Column.get?, getFromBlocks, Block.length, h0, h1,
          periodic_constant_get]
        omega
  · change n < 49152 at hn
    by_cases h0 : n < 16384
    · simp [Column.get?, getFromBlocks, Block.length, h0, periodic_constant_get]
      omega
    · by_cases h1 : n - 16384 < 16384
      · simp [Column.get?, getFromBlocks, Block.length, h0, h1, periodic_constant_get]
        omega
      · simp (disch := omega) [Column.get?, getFromBlocks, Block.length, h0, h1,
          periodic_constant_get]
        omega


end Airbender.Blake2Round.Proofs
