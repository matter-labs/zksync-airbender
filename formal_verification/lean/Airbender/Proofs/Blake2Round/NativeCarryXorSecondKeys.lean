import Airbender.Proofs.Blake2Round.NativeXorKeyHelpers

namespace Airbender.Blake2Round.Proofs
open Airbender.Setup Airbender.Setup.Proofs NativeXorKeyHelpers
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

/-- Every stored second input agrees with its native pair index. -/
theorem carry_second_get (kind : Fin 2) (n : Nat)
    (hn : n < (xorData (carryKind kind)).length) :
    (xorData (carryKind kind)).columns[1].get? n = some (n % carryBase kind) := by
  fin_cases kind
  · have shape : (xorData (3 : Fin 6)).columns[1] = Column.mk #[
        .dense (Array.range 128),
        .periodic 767 0 (Array.ofFn (fun i : Fin 256 => (128 + i.val) % 256)),
        .dense (Array.ofFn (fun i : Fin 128 => 128 + i.val))] := rfl
    change n < 196608 at hn
    change (xorData (3 : Fin 6)).columns[1].get? n = some (n % 256)
    rw [shape]
    by_cases h0 : n < 128
    · simp [Column.get?, getFromBlocks, Block.length, dense_range_get, h0]
      omega
    · by_cases h1 : n - 128 < 196352
      · simp [Column.get?, getFromBlocks, Block.length, periodic_cyclic_get, h0, h1]
        omega
      · simp (disch := omega) [Column.get?, getFromBlocks, Block.length, h0, h1,
          dense_affine_get]
        omega
  · change (Column.mk #[.dense (Array.range 128),
        .periodic 383 0 (Array.range 128)]).get? n = some (n % 128)
    change n < 49152 at hn
    by_cases h0 : n < 128
    · simp [Column.get?, getFromBlocks, Block.length, dense_range_get, h0]
      omega
    · simp (disch := omega) [Column.get?, getFromBlocks, Block.length, h0, periodic_range_get]
      omega


end Airbender.Blake2Round.Proofs
