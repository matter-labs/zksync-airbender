module
public import Human.Helpers.Delegation.RVMemory

@[expose] public section

/-! A native cut's image read from an `RV.State` (`Cell.readRV`). A RAM cell is
    RAM at any address, INCLUDING READ-WRITE ACCESS TO THE SHADOW RAM BELOW `ROM_END` (`RV.State.delegationRAM`); no
    pointer is required to be at or above `ROM_END`. -/

namespace Airbender.Delegation
open Trace

/-- Actual RV reads encode the native seed values and public cell domain. -/
structure RVBoundaryImage (tokens : List (MemoryToken p)) (before : RV.State) (cells : List Cell) : Prop where
  addresses : (tokens.map MemoryToken.address).Perm (cells.map Cell.addressCode)
  values : ∀ token ∈ tokens, ∃ cell ∈ cells, ∃ value,
    cell.addressCode = token.address ∧ cell.readRV before = some value ∧
      token.word = Arithmetic.Word.ofBitVec value

/-- A native cut's actual RV state image, with the seed timestamps retained.
    The invocation-high bound is the approved assumption on the invocation timestamp's high limb. -/
structure RVBoundaryMemoryInputs (data : MemoryData p) (before : RV.State) (cells : List Cell) : Prop where
  image : RVBoundaryImage data.initial before cells
  distinct : (cells.map Cell.addressCode).Nodup
  clocks : ∀ token ∈ data.initial, (timeOfPair token.time).Bounded
  clockRoom : ∀ row ∈ data.rows,
    (decodeTimestamp row.assignment row.columns.invocation).lo + 2 < timestampBase
  invocationHigh : ∀ row ∈ data.rows,
    (decodeTimestamp row.assignment row.columns.invocation).hi < timestampBase

end Airbender.Delegation
