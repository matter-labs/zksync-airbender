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
theorem native_ac_queries_0 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    chunkXor 7 (acTemp w (0 : Fin 8) 0) (acLowC w (0 : Fin 8)) (acTemp w (0 : Fin 8) 1) ∧
    chunkXor 9 ((-15728640 : ZMod p) * (acInitial w (0 : Fin 8) - acTemp w (0 : Fin 8) 0))
      ((-15728640 : ZMod p) * (acC w (0 : Fin 8) - acLowC w (0 : Fin 8))) (acTemp w (0 : Fin 8) 2) ∧
    chunkXor 7 (acTemp w (0 : Fin 8) 1) (acLowA w (0 : Fin 8)) (acTemp w (0 : Fin 8) 4) ∧
    chunkXor 9 (acTemp w (0 : Fin 8) 2)
      ((-15728640 : ZMod p) * (acA w (0 : Fin 8) - acLowA w (0 : Fin 8))) (acTemp w (0 : Fin 8) 5) := by
  exact native_ac_queries_cached compatible (0 : Fin 8) h


/-- Native query projections for the first half of finalization. -/
theorem native_ac_queries_1 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    chunkXor 7 (acTemp w (1 : Fin 8) 0) (acLowC w (1 : Fin 8)) (acTemp w (1 : Fin 8) 1) ∧
    chunkXor 9 ((-15728640 : ZMod p) * (acInitial w (1 : Fin 8) - acTemp w (1 : Fin 8) 0))
      ((-15728640 : ZMod p) * (acC w (1 : Fin 8) - acLowC w (1 : Fin 8))) (acTemp w (1 : Fin 8) 2) ∧
    chunkXor 7 (acTemp w (1 : Fin 8) 1) (acLowA w (1 : Fin 8)) (acTemp w (1 : Fin 8) 4) ∧
    chunkXor 9 (acTemp w (1 : Fin 8) 2)
      ((-15728640 : ZMod p) * (acA w (1 : Fin 8) - acLowA w (1 : Fin 8))) (acTemp w (1 : Fin 8) 5) := by
  exact native_ac_queries_cached compatible (1 : Fin 8) h


/-- Native query projections for the first half of finalization. -/
theorem native_ac_queries_2 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    chunkXor 7 (acTemp w (2 : Fin 8) 0) (acLowC w (2 : Fin 8)) (acTemp w (2 : Fin 8) 1) ∧
    chunkXor 9 ((-15728640 : ZMod p) * (acInitial w (2 : Fin 8) - acTemp w (2 : Fin 8) 0))
      ((-15728640 : ZMod p) * (acC w (2 : Fin 8) - acLowC w (2 : Fin 8))) (acTemp w (2 : Fin 8) 2) ∧
    chunkXor 7 (acTemp w (2 : Fin 8) 1) (acLowA w (2 : Fin 8)) (acTemp w (2 : Fin 8) 4) ∧
    chunkXor 9 (acTemp w (2 : Fin 8) 2)
      ((-15728640 : ZMod p) * (acA w (2 : Fin 8) - acLowA w (2 : Fin 8))) (acTemp w (2 : Fin 8) 5) := by
  exact native_ac_queries_cached compatible (2 : Fin 8) h


/-- Native query projections for the first half of finalization. -/
theorem native_ac_queries_3 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    chunkXor 7 (acTemp w (3 : Fin 8) 0) (acLowC w (3 : Fin 8)) (acTemp w (3 : Fin 8) 1) ∧
    chunkXor 9 ((-15728640 : ZMod p) * (acInitial w (3 : Fin 8) - acTemp w (3 : Fin 8) 0))
      ((-15728640 : ZMod p) * (acC w (3 : Fin 8) - acLowC w (3 : Fin 8))) (acTemp w (3 : Fin 8) 2) ∧
    chunkXor 7 (acTemp w (3 : Fin 8) 1) (acLowA w (3 : Fin 8)) (acTemp w (3 : Fin 8) 4) ∧
    chunkXor 9 (acTemp w (3 : Fin 8) 2)
      ((-15728640 : ZMod p) * (acA w (3 : Fin 8) - acLowA w (3 : Fin 8))) (acTemp w (3 : Fin 8) 5) := by
  exact native_ac_queries_cached compatible (3 : Fin 8) h


end Airbender.Blake2Round.Proofs
