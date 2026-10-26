import Airbender.Proofs.GKRProtocol.InitializationTokens
import Airbender.Review.Circuits.Initialization.Artifact

namespace Airbender.Compiler
open Airbender
set_option warningAsError true
set_option Elab.async false

/-- Actual inline window stride and row range, with the second set in the next
window. These are field-address laws supplied by native virtual setup. -/
theorem inline_public_addresses (parameters : Initialization.Parameters babyBearModulus Source.BaseField)
    (memory : Source.MemoryValues) (row : Fin 8388608) (window : Nat)
    (windows : ∀ set : Fin 2, parameters.windows set.val = window + set.val)
    (low : memory.initializationAddress 0 = (Initialization.addressLo row.val : Source.BaseField))
    (high : memory.initializationAddress 1 = (row.val / 16384 + window * 512 : Nat))
    (set : Fin 2) :
    memory.initializationAddress 0 = (Initialization.addressLo row.val : Source.BaseField) ∧
    memory.initializationAddress 1 + (set.val * Initialization.unified.layout.stride : Nat) =
      (Initialization.addressHi Initialization.unified.layout parameters set.val row.val : Source.BaseField) := by
  refine ⟨low, ?_⟩
  rw [high]
  change ((row.val / 16384 + window * 512 : Nat) : Source.BaseField) + (set.val * 512 : Nat) =
    ((row.val / 16384 + parameters.windows set.val * 512 : Nat) : Source.BaseField)
  rw [windows set, Nat.add_mul]
  push_cast
  ring

theorem inline_public_bounds (parameters : Initialization.Parameters babyBearModulus Source.BaseField)
    (row : Fin 8388608) (window : Nat) (windowBound : window + 1 < 128)
    (windows : ∀ set : Fin 2, parameters.windows set.val = window + set.val) (set : Fin 2) :
    Initialization.addressLo row.val < babyBearModulus ∧
    Initialization.addressHi Initialization.unified.layout parameters set.val row.val < babyBearModulus := by
  have rowBound := row.isLt
  have setBound := set.isLt
  have lowBound : Initialization.addressLo row.val < 65536 := Nat.mod_lt _ (by decide)
  have upper : row.val / 16384 < 512 := by omega
  change _ ∧ row.val / 16384 + parameters.windows set.val * 512 < babyBearModulus
  rw [windows set]
  constructor
  · change _ < 2013265921
    omega
  · change _ < 2013265921
    omega

theorem inline_public_word_bounds (parameters : Initialization.Parameters babyBearModulus Source.BaseField)
    (row : Fin 8388608) (window : Nat) (windowBound : window + 1 < 128)
    (windows : ∀ set : Fin 2, parameters.windows set.val = window + set.val) (set : Fin 2) :
    Initialization.addressLo row.val < 65536 ∧
    Initialization.addressHi Initialization.unified.layout parameters set.val row.val < 65536 := by
  have rowBound := row.isLt
  have setBound := set.isLt
  have upper : row.val / 16384 < 512 := by omega
  change _ ∧ row.val / 16384 + parameters.windows set.val * 512 < 65536
  rw [windows set]
  constructor
  · exact Nat.mod_lt _ (by decide)
  · have selected : window + set.val < 128 := by omega
    have product : (window + set.val) * 512 ≤ 127 * 512 := Nat.mul_le_mul_right 512 (by omega)
    omega

end Airbender.Compiler
