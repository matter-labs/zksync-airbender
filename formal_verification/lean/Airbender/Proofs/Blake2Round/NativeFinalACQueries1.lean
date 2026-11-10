import Airbender.Proofs.Blake2Round.NativeFinalACSoundness
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Blake2Round.NativeFinalQueryBase

namespace Airbender.Blake2Round.Proofs
open Arithmetic Blake2G.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-- Native query projections for the first half of finalization. -/
theorem native_ac_queries_4 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    chunkXor 7 (acTemp w (4 : Fin 8) 0) (acLowC w (4 : Fin 8)) (acTemp w (4 : Fin 8) 1) ∧
    chunkXor 9 ((-15728640 : ZMod p) * (acInitial w (4 : Fin 8) - acTemp w (4 : Fin 8) 0))
      ((-15728640 : ZMod p) * (acC w (4 : Fin 8) - acLowC w (4 : Fin 8))) (acTemp w (4 : Fin 8) 2) ∧
    chunkXor 7 (acTemp w (4 : Fin 8) 1) (acLowA w (4 : Fin 8)) (acTemp w (4 : Fin 8) 4) ∧
    chunkXor 9 (acTemp w (4 : Fin 8) 2)
      ((-15728640 : ZMod p) * (acA w (4 : Fin 8) - acLowA w (4 : Fin 8))) (acTemp w (4 : Fin 8) 5) := by
  exact native_ac_queries_cached compatible (4 : Fin 8) h


/-- Native query projections for the first half of finalization. -/
theorem native_ac_queries_5 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    chunkXor 7 (acTemp w (5 : Fin 8) 0) (acLowC w (5 : Fin 8)) (acTemp w (5 : Fin 8) 1) ∧
    chunkXor 9 ((-15728640 : ZMod p) * (acInitial w (5 : Fin 8) - acTemp w (5 : Fin 8) 0))
      ((-15728640 : ZMod p) * (acC w (5 : Fin 8) - acLowC w (5 : Fin 8))) (acTemp w (5 : Fin 8) 2) ∧
    chunkXor 7 (acTemp w (5 : Fin 8) 1) (acLowA w (5 : Fin 8)) (acTemp w (5 : Fin 8) 4) ∧
    chunkXor 9 (acTemp w (5 : Fin 8) 2)
      ((-15728640 : ZMod p) * (acA w (5 : Fin 8) - acLowA w (5 : Fin 8))) (acTemp w (5 : Fin 8) 5) := by
  exact native_ac_queries_cached compatible (5 : Fin 8) h


/-- Native query projections for the first half of finalization. -/
theorem native_ac_queries_6 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    chunkXor 7 (acTemp w (6 : Fin 8) 0) (acLowC w (6 : Fin 8)) (acTemp w (6 : Fin 8) 1) ∧
    chunkXor 9 ((-15728640 : ZMod p) * (acInitial w (6 : Fin 8) - acTemp w (6 : Fin 8) 0))
      ((-15728640 : ZMod p) * (acC w (6 : Fin 8) - acLowC w (6 : Fin 8))) (acTemp w (6 : Fin 8) 2) ∧
    chunkXor 7 (acTemp w (6 : Fin 8) 1) (acLowA w (6 : Fin 8)) (acTemp w (6 : Fin 8) 4) ∧
    chunkXor 9 (acTemp w (6 : Fin 8) 2)
      ((-15728640 : ZMod p) * (acA w (6 : Fin 8) - acLowA w (6 : Fin 8))) (acTemp w (6 : Fin 8) 5) := by
  exact native_ac_queries_cached compatible (6 : Fin 8) h


/-- Native query projections for the first half of finalization. -/
theorem native_ac_queries_7 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    chunkXor 7 (acTemp w (7 : Fin 8) 0) (acLowC w (7 : Fin 8)) (acTemp w (7 : Fin 8) 1) ∧
    chunkXor 9 ((-15728640 : ZMod p) * (acInitial w (7 : Fin 8) - acTemp w (7 : Fin 8) 0))
      ((-15728640 : ZMod p) * (acC w (7 : Fin 8) - acLowC w (7 : Fin 8))) (acTemp w (7 : Fin 8) 2) ∧
    chunkXor 7 (acTemp w (7 : Fin 8) 1) (acLowA w (7 : Fin 8)) (acTemp w (7 : Fin 8) 4) ∧
    chunkXor 9 (acTemp w (7 : Fin 8) 2)
      ((-15728640 : ZMod p) * (acA w (7 : Fin 8) - acLowA w (7 : Fin 8))) (acTemp w (7 : Fin 8) 5) := by
  exact native_ac_queries_cached compatible (7 : Fin 8) h


end Airbender.Blake2Round.Proofs
