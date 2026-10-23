import Airbender.Review.Helpers.Delegation.Memory

namespace Airbender.Delegation
open Trace Reference.RiscV.Sail

/-- Actual Sail reads encode the native seed values and public cell domain.
    Raw timestamps stay in the tokens; bounds follow separately from history. -/
structure BoundaryImage (tokens : List (MemoryToken p)) (before : State) (cells : List Cell) : Prop where
  addresses : (tokens.map MemoryToken.address).Perm (cells.map Cell.addressCode)
  values : ∀ token ∈ tokens, ∃ cell ∈ cells, ∃ value,
    cell.addressCode = token.address ∧ cell.read before = .ok value before ∧
      token.word = Arithmetic.Word.ofBitVec value

/-- A native cut's actual state image. Shared history derives this input;
    standalone use exposes seed timestamps and invocation-offset room. -/
structure BoundaryMemoryInputs (data : MemoryData p) (before : State) (cells : List Cell) : Prop where
  /-- Canonical seed values read from the actual supplied or derived state. -/
  image : BoundaryImage data.initial before cells
  /-- One physical cell for each native address. -/
  distinct : (cells.map Cell.addressCode).Nodup
  /-- Nineteen-bit native timestamp limbs, derived at cuts. -/
  clocks : ∀ token ∈ data.initial, (timeOfPair token.time).Bounded
  /-- Invocation timestamps leave room for each imported offset-two write. -/
  clockRoom : ∀ row ∈ data.rows,
    (decodeTimestamp row.assignment row.columns.invocation).lo + 2 < timestampBase

end Airbender.Delegation
