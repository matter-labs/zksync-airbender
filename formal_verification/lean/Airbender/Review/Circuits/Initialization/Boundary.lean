import Airbender.Review.Circuits.Initialization.Products
import Airbender.Review.Helpers.Memory.Native

namespace Airbender.Initialization
variable {p : Nat}

/-- Checked arithmetic properties of the imported native geometry. These are
    proved for each artifact, rather than imposed on circuit witnesses. -/
structure Geometry (layout : Layout) : Prop where
  wordBits : layout.wordBits = 2
  positive : 0 < layout.rows
  stride : layout.rows = 16384 * layout.stride
  extent : layout.slots * (4 * layout.rows) ≤ 2 ^ 32

abbrev Geometry.public {layout : Layout} (geometry : Geometry layout) :
    ExternalBoundary.Initialization.Geometry :=
  ⟨layout.rows, layout.slots, geometry.positive, geometry.extent⟩

/-- Public statement window indices. Distinctness is the existing explicit
    statement-validation interface; sparse and reversed windows are allowed. -/
structure Windows (layout : Layout) where
  index : Fin layout.columns.size → Fin layout.slots
  unique : Function.Injective index

def Windows.selection {layout : Layout} (windows : Windows layout) (geometry : Geometry layout) :
    ExternalBoundary.Initialization.Selection geometry.public where
  indices := (List.finRange layout.columns.size).map windows.index
  unique := (List.nodup_finRange _).map windows.unique

def Windows.at {layout : Layout} (windows : Windows layout) (set : Nat) : Nat :=
  if bound : set < layout.columns.size then (windows.index ⟨set, bound⟩).val else 0

def parametersFor [CommRing E] {layout : Layout} (embed : ZMod p →+* E)
    (additive : E) (weights : Fin 6 → E) (windows : Windows layout) : Parameters p E :=
  ⟨embed, additive, weights, windows.at⟩

/-- The actual register/RAM public domain. Full native row lists remain symbolic
    and cannot be allocated by native module initialization. -/
noncomputable def cells {layout : Layout} (geometry : Geometry layout) (windows : Windows layout) :
    List Trace.Cell := ExternalBoundary.Initialization.cells (windows.selection geometry)

/-- Replace caller-chosen RAM boundary lists by tokens computed from the actual
    native layout and witness. Register teardown remains an explicit public
    register boundary, outside these RAM-only GKR slices. -/
noncomputable def withBoundary {Kind : Type} [Trace.CircuitLayout Kind] [Fact p.Prime] [CommRing E]
    (base : Trace.Data p Kind) (layout : Layout) (parameters : Parameters p E) (raw : Raw p)
    (terminalRegisters : List (Trace.MemoryToken p)) : Trace.Data p Kind :=
  { base with
    initialMemory := Trace.ROMView.nativeBootImage ExternalBoundary.Initialization.registers ++
      ramTokens layout parameters raw .initial
    terminalMemory := terminalRegisters ++ ramTokens layout parameters raw .terminal }

end Airbender.Initialization
