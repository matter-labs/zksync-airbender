import Airbender.Proofs.Initialization.Geometry

namespace Airbender.Initialization.Proofs
open Trace
set_option warningAsError true
set_option Elab.async false

variable {p : Nat} [Fact p.Prime] [CommRing E]

theorem initial_token (layout : Layout) (geometry : Geometry layout) (windows : Windows layout)
    (embed : ZMod p →+* E) (additive : E) (weights : Fin 6 → E) (raw : Raw p)
    (set : Fin layout.columns.size) (row : Fin layout.rows) :
    (Leaf.mk .initial set.val layout.columns[set]).token layout
      (parametersFor embed additive weights windows) raw row.val =
        (ExternalBoundary.Initialization.cell
          (geometry := geometry.public) (windows.index set, row)).initialToken 0 := by
  have address := token_address layout geometry windows embed additive weights raw .initial set row
  change Nat.pair 1 (Nat.pair (addressLo row.val)
    (addressHi layout (parametersFor embed additive weights windows) set.val row.val)) = _ at address
  simp only [Leaf.token, Leaf.time, Leaf.value]
  rw [address]
  simp [Cell.initialToken, Arithmetic.Word.ofBitVec]

theorem initial_ram_tokens (layout : Layout) (geometry : Geometry layout) (windows : Windows layout)
    (embed : ZMod p →+* E) (additive : E) (weights : Fin 6 → E) (raw : Raw p) :
    ramTokens layout (parametersFor embed additive weights windows) raw .initial =
      ROMView.nativeBootImage
        (((windows.selection geometry).indices.product (List.finRange layout.rows)).map
          (ExternalBoundary.Initialization.cell (geometry := geometry.public))) := by
  simp only [ramTokens, Layout.leaves, ROMView.nativeBootImage, Windows.selection,
    List.product, List.flatMap_map, List.map_map, Function.comp_def]
  rw [List.map_flatMap]
  simp only [List.map_map, Function.comp_def]
  apply List.flatMap_congr
  intro set _
  apply List.map_congr_left
  intro row _
  exact initial_token layout geometry windows embed additive weights raw set row

theorem computed_seed {Kind : Type} [CircuitLayout Kind] (base : Data p Kind)
    (layout : Layout) (geometry : Geometry layout) (windows : Windows layout)
    (embed : ZMod p →+* E) (additive : E) (weights : Fin 6 → E) (raw : Raw p)
    (terminalRegisters : List (MemoryToken p)) :
    (withBoundary base layout (parametersFor embed additive weights windows) raw
      terminalRegisters).initialMemory = ROMView.nativeBootImage (cells geometry windows) := by
  rw [show (withBoundary base layout (parametersFor embed additive weights windows) raw
      terminalRegisters).initialMemory =
      ROMView.nativeBootImage ExternalBoundary.Initialization.registers ++
        ramTokens layout (parametersFor embed additive weights windows) raw .initial from rfl,
    initial_ram_tokens]
  rfl

/-- Teardown preserves the actual raw timestamp/value limbs at the derived
    address. In particular this statement imposes no local 16-bit ranges. -/
theorem terminal_token (layout : Layout) (geometry : Geometry layout) (windows : Windows layout)
    (embed : ZMod p →+* E) (additive : E) (weights : Fin 6 → E) (raw : Raw p)
    (set : Fin layout.columns.size) (row : Fin layout.rows) :
    ((Leaf.mk .terminal set.val layout.columns[set]).token layout
      (parametersFor embed additive weights windows) raw row.val) =
    ⟨(ExternalBoundary.Initialization.cell
        (geometry := geometry.public) (windows.index set, row)).addressCode,
      (raw row.val layout.columns[set].timeLo, raw row.val layout.columns[set].timeHi),
      Nat.pair (raw row.val layout.columns[set].valueLo).val
        (raw row.val layout.columns[set].valueHi).val⟩ := by
  have address := token_address layout geometry windows embed additive weights raw .terminal set row
  change Nat.pair _ _ = _ at address
  simp only [Leaf.token, Leaf.time, Leaf.value]
  rw [address]

end Airbender.Initialization.Proofs
