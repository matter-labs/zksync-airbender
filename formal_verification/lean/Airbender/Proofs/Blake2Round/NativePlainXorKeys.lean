import Airbender.Proofs.Blake2Round.NativeXorKeyHelpers

namespace Airbender.Blake2Round.Proofs
open Airbender.Setup Airbender.Setup.Proofs NativeXorKeyHelpers
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

/-- Native key columns use the exported order, including its cyclic block split. -/
theorem plain_second_get (kind : Fin 3) (n : Nat) (hn : n < (xorData ⟨kind.val, by omega⟩).length) :
    (xorData ⟨kind.val, by omega⟩).columns[1].get? n = some (n % (#v[256, 128, 512][kind])) := by
  fin_cases kind
  · change (Column.mk #[.periodic 256 0 (Array.range 256)]).get? n = some (n % 256)
    change n < 65536 at hn
    simp [Column.get?, getFromBlocks, Block.length, periodic_range_get, hn]
  · change (Column.mk #[.periodic 128 0 (Array.range 128)]).get? n = some (n % 128)
    change n < 16384 at hn
    simp [Column.get?, getFromBlocks, Block.length, periodic_range_get, hn]
  · have shape : (xorData (2 : Fin 6)).columns[1] = Column.mk #[
        .periodic 1 0 (Array.range 128),
        .periodic 511 0 (Array.ofFn (fun i : Fin 512 => (128 + i.val) % 512)),
        .dense (Array.ofFn (fun i : Fin 384 => 128 + i.val))] := rfl
    change n < 262144 at hn
    change (xorData (2 : Fin 6)).columns[1].get? n = some (n % 512)
    rw [shape]
    by_cases h0 : n < 128
    · simp [Column.get?, getFromBlocks, Block.length, periodic_range_get, h0]
      omega
    · by_cases h1 : n - 128 < 261632
      · simp [Column.get?, getFromBlocks, Block.length, periodic_cyclic_get, h0, h1]
        omega
      · simp (disch := omega) [Column.get?, getFromBlocks, Block.length, h0, h1,
          dense_affine_get]
        omega


end Airbender.Blake2Round.Proofs
