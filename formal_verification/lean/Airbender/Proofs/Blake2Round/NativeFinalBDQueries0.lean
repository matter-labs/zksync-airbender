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
theorem native_bd_queries_0 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    chunkXor 9 (bdLowB w (0 : Fin 8)) (bdTemp w (0 : Fin 8) 0) (bdTemp w (0 : Fin 8) 1) ∧
    chunkXor 7 (bdHighB w (0 : Fin 8))
      ((-3932160 : ZMod p) * (bdInitial w (0 : Fin 8) - bdTemp w (0 : Fin 8) 0)) (bdTemp w (0 : Fin 8) 2) ∧
    chunkXor 8 (bdLowD w (0 : Fin 8)) (bdTemp w (0 : Fin 8) 1 - 256 * bdTemp w (0 : Fin 8) 3) (bdTemp w (0 : Fin 8) 4) ∧
    chunkXor 8 (bdHighD w (0 : Fin 8)) (2 * bdTemp w (0 : Fin 8) 2 + bdTemp w (0 : Fin 8) 3) (bdTemp w (0 : Fin 8) 5) := by
  exact native_bd_queries_cached compatible (0 : Fin 8) h


/-- The native b/d queries expose the width change as an expression. No
    separately allocated split witness or extra constraint is required. -/
theorem native_bd_queries_1 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    chunkXor 9 (bdLowB w (1 : Fin 8)) (bdTemp w (1 : Fin 8) 0) (bdTemp w (1 : Fin 8) 1) ∧
    chunkXor 7 (bdHighB w (1 : Fin 8))
      ((-3932160 : ZMod p) * (bdInitial w (1 : Fin 8) - bdTemp w (1 : Fin 8) 0)) (bdTemp w (1 : Fin 8) 2) ∧
    chunkXor 8 (bdLowD w (1 : Fin 8)) (bdTemp w (1 : Fin 8) 1 - 256 * bdTemp w (1 : Fin 8) 3) (bdTemp w (1 : Fin 8) 4) ∧
    chunkXor 8 (bdHighD w (1 : Fin 8)) (2 * bdTemp w (1 : Fin 8) 2 + bdTemp w (1 : Fin 8) 3) (bdTemp w (1 : Fin 8) 5) := by
  exact native_bd_queries_cached compatible (1 : Fin 8) h


/-- The native b/d queries expose the width change as an expression. No
    separately allocated split witness or extra constraint is required. -/
theorem native_bd_queries_2 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    chunkXor 9 (bdLowB w (2 : Fin 8)) (bdTemp w (2 : Fin 8) 0) (bdTemp w (2 : Fin 8) 1) ∧
    chunkXor 7 (bdHighB w (2 : Fin 8))
      ((-3932160 : ZMod p) * (bdInitial w (2 : Fin 8) - bdTemp w (2 : Fin 8) 0)) (bdTemp w (2 : Fin 8) 2) ∧
    chunkXor 8 (bdLowD w (2 : Fin 8)) (bdTemp w (2 : Fin 8) 1 - 256 * bdTemp w (2 : Fin 8) 3) (bdTemp w (2 : Fin 8) 4) ∧
    chunkXor 8 (bdHighD w (2 : Fin 8)) (2 * bdTemp w (2 : Fin 8) 2 + bdTemp w (2 : Fin 8) 3) (bdTemp w (2 : Fin 8) 5) := by
  exact native_bd_queries_cached compatible (2 : Fin 8) h


/-- The native b/d queries expose the width change as an expression. No
    separately allocated split witness or extra constraint is required. -/
theorem native_bd_queries_3 {p : Nat} [Fact p.Prime]
    (compatible : SerializedInverse.Scale64 p)
    {w : Nat → ZMod p}
    (h : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints setupTable)) :
    chunkXor 9 (bdLowB w (3 : Fin 8)) (bdTemp w (3 : Fin 8) 0) (bdTemp w (3 : Fin 8) 1) ∧
    chunkXor 7 (bdHighB w (3 : Fin 8))
      ((-3932160 : ZMod p) * (bdInitial w (3 : Fin 8) - bdTemp w (3 : Fin 8) 0)) (bdTemp w (3 : Fin 8) 2) ∧
    chunkXor 8 (bdLowD w (3 : Fin 8)) (bdTemp w (3 : Fin 8) 1 - 256 * bdTemp w (3 : Fin 8) 3) (bdTemp w (3 : Fin 8) 4) ∧
    chunkXor 8 (bdHighD w (3 : Fin 8)) (2 * bdTemp w (3 : Fin 8) 2 + bdTemp w (3 : Fin 8) 3) (bdTemp w (3 : Fin 8) 5) := by
  exact native_bd_queries_cached compatible (3 : Fin 8) h


end Airbender.Blake2Round.Proofs
