import Airbender.Proofs.Keccak.ReferenceController
import Airbender.Review.Circuits.Keccak.Tables.Controller
import Mathlib.Tactic.FinCases

namespace Airbender.Keccak.Controller.Proofs.Certificate
open Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

/-- Two coordinates cover every native key, including fallback controls. -/
def splitKey (high low : Fin 64) : Fin 4096 :=
  ⟨64 * high.val + low.val, by have := high.isLt; have := low.isLt; omega⟩

def partKey (chunk high : Fin 8) (low : Fin 64) : Fin 4096 :=
  splitKey ⟨8 * chunk.val + high.val, by have := chunk.isLt; have := high.isLt; omega⟩ low

def ControllerPiece (lane : Fin 6) (chunk : Fin 8) : Prop :=
  ∀ high : Fin 8, ∀ low : Fin 64,
    (rows (partKey chunk high low))[lane] = (referenceRows (partKey chunk high low))[lane]

macro "keccak_controller_certificate " name:ident lane:num chunk:num : command =>
  `(private theorem $name : ControllerPiece $lane $chunk := by
    dsimp only [ControllerPiece, partKey, rows, Vector.getElem_ofFn, Fin.getElem_fin,
      controllerData, Setup.Column.get?, Array.toList, splitKey, referenceRows]
    decide +kernel)


/-- Assemble checked chunks without restricting any encoded key. -/
theorem field_of_pieces (lane : Fin 6) (pieces : ∀ chunk, ControllerPiece lane chunk)
    (high low : Fin 64) :
    (rows (splitKey high low))[lane] = (referenceRows (splitKey high low))[lane] := by
  let chunk : Fin 8 := ⟨high.val / 8, by have := high.isLt; omega⟩
  let inner : Fin 8 := ⟨high.val % 8, Nat.mod_lt _ (by decide)⟩
  have key : partKey chunk inner low = splitKey high low := by
    apply Fin.ext
    dsimp only [partKey, splitKey, chunk, inner]
    omega
  have result := pieces chunk inner low
  simpa only [key] using result

end Airbender.Keccak.Controller.Proofs.Certificate
