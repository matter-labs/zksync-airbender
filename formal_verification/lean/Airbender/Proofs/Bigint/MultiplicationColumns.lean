import Airbender.Proofs.Bigint.MultiplicationColumnsChunk0
import Airbender.Proofs.Bigint.MultiplicationColumnsChunk1
import Airbender.Proofs.Bigint.MultiplicationColumnsChunk2
import Airbender.Proofs.Bigint.MultiplicationColumnsChunk3
import Airbender.Proofs.Bigint.MultiplicationColumnsChunk4
import Airbender.Proofs.Bigint.MultiplicationColumnsChunk5
import Airbender.Proofs.Bigint.MultiplicationColumnsChunk6
import Airbender.Proofs.Bigint.MultiplicationColumnsChunk7

namespace Airbender.Bigint.Multiplication.Proofs
open Arithmetic
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

/-- Normalize each imported multiplication assertion into its byte column.
    The serialized inverse is interpreted in this artifact's BabyBear field. -/
theorem native_columns {w : Nat → ZMod babyBearModulus} {left right : Fin 16 → Nat}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable))
    (sources : ∀ i, w Variables.leftLimbs[i] = (left i : ZMod babyBearModulus) ∧
      w Variables.rightLimbs[i] = (right i : ZMod babyBearModulus))
    (bytes : ∀ i : Fin 16,
      w (99 + i.val) = ((left i % 256 : Nat) : ZMod babyBearModulus) ∧
      w (115 + i.val) = ((right i % 256 : Nat) : ZMod babyBearModulus)) :
    ∀ i : Fin 32, (multiplicationColumn left right i.val : ZMod babyBearModulus) + incoming w i =
      w (131 + i.val) + 65536 * outgoing w i := by
  have chunks (chunk : Fin 8) : ∀ lane : Fin 4,
      let i := columnIndex chunk lane
      (multiplicationColumn left right i.val : ZMod babyBearModulus) + incoming w i =
        w (131 + i.val) + 65536 * outgoing w i := by
    fin_cases chunk
    · exact native_columns_chunk0 h sources bytes
    · exact native_columns_chunk1 h sources bytes
    · exact native_columns_chunk2 h sources bytes
    · exact native_columns_chunk3 h sources bytes
    · exact native_columns_chunk4 h sources bytes
    · exact native_columns_chunk5 h sources bytes
    · exact native_columns_chunk6 h sources bytes
    · exact native_columns_chunk7 h sources bytes
  intro i
  let chunk : Fin 8 := ⟨i.val / 4, by have := i.isLt; omega⟩
  let lane : Fin 4 := ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩
  have same : columnIndex chunk lane = i := by
    apply Fin.ext
    dsimp only [columnIndex, chunk, lane]
    omega
  simpa only [same] using chunks chunk lane

end Airbender.Bigint.Multiplication.Proofs
