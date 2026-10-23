import Airbender.Proofs.Blake2Round.NativeFinalQueryShapes
import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Blake2Round.NativeFinalLayout
import Airbender.Proofs.Blake2Round.NativeFinalGates
import Airbender.Proofs.Blake2Round.Lookups
import Airbender.Proofs.Blake2Round.FinalXor

namespace Airbender.Blake2Round.Proofs
open Arithmetic Blake2G.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

theorem final_query {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 512)
    {w : Nat → ZMod p} (limb : Fin 16) (stage : Fin 4) (kind : Fin 3)
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable))
    (tag : finalColumn w limb stage 5 = ((plainTags[kind] : Nat) : ZMod p)) :
    chunkXor (#v[8, 7, 9][kind])
      (finalColumn w limb stage 0) (finalColumn w limb stage 1) (finalColumn w limb stage 2) := by
  have member := Verification.lookup_of_holds h
    ⟨NativeFinalLayout.queryIndex limb stage, by
      rw [lookup_count]; have := limb.isLt; have := stage.isLt
      dsimp [NativeFinalLayout.queryIndex]; omega⟩
  have table := NativeFinalQueryShapes.table_eq (p := p) limb stage
  have result := xor_lookup_raw hp kind member table tag
  fin_cases kind <;> simpa [plainBase, chunkXor, finalColumn, NativeFinalLayout.queryColumn, NativeFinalLayout.query] using result

end Airbender.Blake2Round.Proofs
