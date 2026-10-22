import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Blake2Round.NativeFinalACQueries0
import Airbender.Proofs.Blake2Round.NativeFinalACQueries1
import Airbender.Proofs.Blake2Round.NativeFinalBDQueries0
import Airbender.Proofs.Blake2Round.NativeFinalBDQueries1

namespace Airbender.Blake2Round.Proofs
open Arithmetic Blake2G.Proofs
set_option warningAsError true
set_option Elab.async false

theorem ac_queries {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p) (limb : Fin 8)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    chunkXor 7 (acTemp w limb 0) (acLowC w limb) (acTemp w limb 1) ∧
    chunkXor 9 ((-15728640 : ZMod p) * (acInitial w limb - acTemp w limb 0))
      ((-15728640 : ZMod p) * (acC w limb - acLowC w limb)) (acTemp w limb 2) ∧
    chunkXor 7 (acTemp w limb 1) (acLowA w limb) (acTemp w limb 4) ∧
    chunkXor 9 (acTemp w limb 2)
      ((-15728640 : ZMod p) * (acA w limb - acLowA w limb)) (acTemp w limb 5) := by
  fin_cases limb
  · exact native_ac_queries_0 compatible h
  · exact native_ac_queries_1 compatible h
  · exact native_ac_queries_2 compatible h
  · exact native_ac_queries_3 compatible h
  · exact native_ac_queries_4 compatible h
  · exact native_ac_queries_5 compatible h
  · exact native_ac_queries_6 compatible h
  · exact native_ac_queries_7 compatible h

theorem bd_queries {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p) (limb : Fin 8)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    chunkXor 9 (bdLowB w limb) (bdTemp w limb 0) (bdTemp w limb 1) ∧
    chunkXor 7 (bdHighB w limb)
      ((-3932160 : ZMod p) * (bdInitial w limb - bdTemp w limb 0)) (bdTemp w limb 2) ∧
    chunkXor 8 (bdLowD w limb) (bdTemp w limb 1 - 256 * bdTemp w limb 3) (bdTemp w limb 4) ∧
    chunkXor 8 (bdHighD w limb) (2 * bdTemp w limb 2 + bdTemp w limb 3) (bdTemp w limb 5) := by
  fin_cases limb
  · exact native_bd_queries_0 compatible h
  · exact native_bd_queries_1 compatible h
  · exact native_bd_queries_2 compatible h
  · exact native_bd_queries_3 compatible h
  · exact native_bd_queries_4 compatible h
  · exact native_bd_queries_5 compatible h
  · exact native_bd_queries_6 compatible h
  · exact native_bd_queries_7 compatible h

end Airbender.Blake2Round.Proofs
