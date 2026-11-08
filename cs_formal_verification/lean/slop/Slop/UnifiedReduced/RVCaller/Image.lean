import Slop.Trace.RVValues
import Slop.Trace.TransferHistory

/-! Seed-image facts for the RV unified caller proofs (RV siblings of `image_clocks`/`image_bounds`). -/

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic
set_option warningAsError true

theorem rv_image_clocks {p : Nat} {before : RV.State} {cells : List Cell}
    {tokens : List (MemoryToken p)} (image : initialImageRV before cells = some tokens) :
    ∀ token ∈ tokens, (timeOfPair token.time).Bounded := by
  intro token member
  obtain ⟨cell, _, value, _, rfl⟩ := RVZero.rv_image_token_sources image token member
  simp [Cell.initialToken, timeOfPair, Timestamp.Bounded, timestampBase]

end Airbender.UnifiedReduced.Caller.Proofs

namespace Airbender.UnifiedReduced.Caller.Proofs
open Trace Trace.Proofs Arithmetic

/-- RV sibling of `Delegation.Caller.Proofs.initial_zero`: the x0 seed of an RV image is zero. -/
theorem rv_initial_zero {data : Transfer.Data p} {before : RV.State} {cells : List Cell}
    (image : initialImageRV before cells = some data.initial) :
    ∀ token ∈ data.initial, token.address = (Cell.register 0).addressCode → token.value = 0 := by
  intro token present same
  obtain ⟨cell, _, value, read, rfl⟩ := RVZero.rv_image_token_sources image token present
  have code : cell.addressCode = (Cell.register 0).addressCode := same
  have equal := cell_address_injective code
  subst cell
  have actual : value = 0 := by
    simp only [Cell.readRV, RV.State.getReg, ite_true, Option.some.injEq] at read
    exact read.symm
  subst value
  rfl

end Airbender.UnifiedReduced.Caller.Proofs
