import Airbender.Proofs.Blake2Round.NativeFinalBDSoundness
import Airbender.Review.Helpers.Core.SerializedInverse
import Airbender.Proofs.Blake2Round.NativeFinalQueryBase

namespace Airbender.Blake2Round.Proofs
open Arithmetic Blake2G.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-- The native b/d queries expose the width change as an expression. No
    separately allocated split witness or extra constraint is required. -/
theorem native_bd_queries_4 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    chunkXor 9 (bdLowB w (4 : Fin 8)) (bdTemp w (4 : Fin 8) 0) (bdTemp w (4 : Fin 8) 1) ∧
    chunkXor 7 (bdHighB w (4 : Fin 8))
      ((-3932160 : ZMod p) * (bdInitial w (4 : Fin 8) - bdTemp w (4 : Fin 8) 0)) (bdTemp w (4 : Fin 8) 2) ∧
    chunkXor 8 (bdLowD w (4 : Fin 8)) (bdTemp w (4 : Fin 8) 1 - 256 * bdTemp w (4 : Fin 8) 3) (bdTemp w (4 : Fin 8) 4) ∧
    chunkXor 8 (bdHighD w (4 : Fin 8)) (2 * bdTemp w (4 : Fin 8) 2 + bdTemp w (4 : Fin 8) 3) (bdTemp w (4 : Fin 8) 5) := by
  exact native_bd_queries_cached compatible (4 : Fin 8) h


/-- The native b/d queries expose the width change as an expression. No
    separately allocated split witness or extra constraint is required. -/
theorem native_bd_queries_5 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    chunkXor 9 (bdLowB w (5 : Fin 8)) (bdTemp w (5 : Fin 8) 0) (bdTemp w (5 : Fin 8) 1) ∧
    chunkXor 7 (bdHighB w (5 : Fin 8))
      ((-3932160 : ZMod p) * (bdInitial w (5 : Fin 8) - bdTemp w (5 : Fin 8) 0)) (bdTemp w (5 : Fin 8) 2) ∧
    chunkXor 8 (bdLowD w (5 : Fin 8)) (bdTemp w (5 : Fin 8) 1 - 256 * bdTemp w (5 : Fin 8) 3) (bdTemp w (5 : Fin 8) 4) ∧
    chunkXor 8 (bdHighD w (5 : Fin 8)) (2 * bdTemp w (5 : Fin 8) 2 + bdTemp w (5 : Fin 8) 3) (bdTemp w (5 : Fin 8) 5) := by
  exact native_bd_queries_cached compatible (5 : Fin 8) h


/-- The native b/d queries expose the width change as an expression. No
    separately allocated split witness or extra constraint is required. -/
theorem native_bd_queries_6 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    chunkXor 9 (bdLowB w (6 : Fin 8)) (bdTemp w (6 : Fin 8) 0) (bdTemp w (6 : Fin 8) 1) ∧
    chunkXor 7 (bdHighB w (6 : Fin 8))
      ((-3932160 : ZMod p) * (bdInitial w (6 : Fin 8) - bdTemp w (6 : Fin 8) 0)) (bdTemp w (6 : Fin 8) 2) ∧
    chunkXor 8 (bdLowD w (6 : Fin 8)) (bdTemp w (6 : Fin 8) 1 - 256 * bdTemp w (6 : Fin 8) 3) (bdTemp w (6 : Fin 8) 4) ∧
    chunkXor 8 (bdHighD w (6 : Fin 8)) (2 * bdTemp w (6 : Fin 8) 2 + bdTemp w (6 : Fin 8) 3) (bdTemp w (6 : Fin 8) 5) := by
  exact native_bd_queries_cached compatible (6 : Fin 8) h


/-- The native b/d queries expose the width change as an expression. No
    separately allocated split witness or extra constraint is required. -/
theorem native_bd_queries_7 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    chunkXor 9 (bdLowB w (7 : Fin 8)) (bdTemp w (7 : Fin 8) 0) (bdTemp w (7 : Fin 8) 1) ∧
    chunkXor 7 (bdHighB w (7 : Fin 8))
      ((-3932160 : ZMod p) * (bdInitial w (7 : Fin 8) - bdTemp w (7 : Fin 8) 0)) (bdTemp w (7 : Fin 8) 2) ∧
    chunkXor 8 (bdLowD w (7 : Fin 8)) (bdTemp w (7 : Fin 8) 1 - 256 * bdTemp w (7 : Fin 8) 3) (bdTemp w (7 : Fin 8) 4) ∧
    chunkXor 8 (bdHighD w (7 : Fin 8)) (2 * bdTemp w (7 : Fin 8) 2 + bdTemp w (7 : Fin 8) 3) (bdTemp w (7 : Fin 8) 5) := by
  exact native_bd_queries_cached compatible (7 : Fin 8) h


end Airbender.Blake2Round.Proofs
