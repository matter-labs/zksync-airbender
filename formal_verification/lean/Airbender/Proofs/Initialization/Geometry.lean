import Airbender.Review.Circuits.Initialization.Boundary
import Airbender.Proofs.ExternalBoundary.Initialization
import Airbender.Proofs.Arithmetic.Word

namespace Airbender.Initialization.Proofs
open Arithmetic
set_option warningAsError true
set_option Elab.async false

theorem address_split (layout : Layout) (geometry : Geometry layout) (window row : Nat) :
    4 * (window * layout.rows + row) =
      addressLo row + 65536 * (row / 16384 + window * layout.stride) := by
  have rowSplit : 4 * row = addressLo row + 65536 * (row / 16384) := by
    dsimp [addressLo]
    omega
  calc
    _ = 65536 * (window * layout.stride) + 4 * row := by rw [geometry.stride]; ring
    _ = _ := by rw [rowSplit]; ring

theorem address_word (layout : Layout) (geometry : Geometry layout)
    (window : Fin layout.slots) (row : Fin layout.rows) :
    Word.ofBitVec (BitVec.ofNat 32 (4 * (window.val * layout.rows + row.val))) =
      ⟨addressLo row.val, row.val / 16384 + window.val * layout.stride⟩ := by
  have bound := ExternalBoundary.Initialization.Proofs.address_bound
    (geometry := geometry.public) (window, row)
  change 4 * (window.val * layout.rows + row.val) < 2 ^ 32 at bound
  have split := address_split layout geometry window.val row.val
  have low : addressLo row.val < 65536 := Nat.mod_lt _ (by decide)
  have high : row.val / 16384 + window.val * layout.stride < 65536 := by
    nlinarith
  apply Word.eq_of_value (Word.ofBitVec_bound _) ⟨low, high⟩
  rw [Word.ofBitVec_value, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  exact split

variable [CommRing E]

theorem token_address (layout : Layout) (geometry : Geometry layout) (windows : Windows layout)
    (embed : ZMod p →+* E) (additive : E) (weights : Fin 6 → E) (raw : Raw p)
    (phase : Phase) (set : Fin layout.columns.size) (row : Fin layout.rows) :
    ((Leaf.mk phase set.val layout.columns[set]).token layout
      (parametersFor embed additive weights windows) raw row.val).address =
        (ExternalBoundary.Initialization.cell
          (geometry := geometry.public) (windows.index set, row)).addressCode := by
  simp only [Leaf.token, addressHi, parametersFor, Windows.at, dif_pos set.isLt,
    ExternalBoundary.Initialization.cell, ExternalBoundary.Initialization.address, Trace.Cell.addressCode, Geometry.public,
    address_word layout geometry (windows.index set) row]

end Airbender.Initialization.Proofs
