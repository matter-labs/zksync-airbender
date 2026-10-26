import Airbender.Proofs.GKRProtocol.WindowedInitialization
import Airbender.Review.Circuits.Initialization.Artifact

namespace Airbender.Compiler
open Airbender
set_option warningAsError true

/-- The native virtual high column contains row bits only. Each set adds its
own supplied public window; neither adjacency nor ordering is required. -/
theorem windowed_public_addresses
    (parameters : Initialization.Parameters babyBearModulus Source.BaseField)
    (memory : Source.MemoryValues) (row : Fin 8388608) (publicTops : Nat → Nat)
    (windows : ∀ set : Fin 2, parameters.windows set.val = publicTops set.val)
    (low : memory.initializationAddress 0 = (Initialization.addressLo row.val : Source.BaseField))
    (high : memory.initializationAddress 1 = (row.val / 16384 : Nat)) (set : Fin 2) :
    memory.initializationAddress 0 = (Initialization.addressLo row.val : Source.BaseField) ∧
    memory.initializationAddress 1 + (publicTops set.val * Initialization.unified.layout.stride : Nat) =
      (Initialization.addressHi Initialization.unified.layout parameters set.val row.val : Source.BaseField) := by
  refine ⟨low, ?_⟩
  rw [high]
  change ((row.val / 16384 : Nat) : Source.BaseField) + (publicTops set.val * 512 : Nat) =
    ((row.val / 16384 + parameters.windows set.val * 512 : Nat) : Source.BaseField)
  rw [windows set, Nat.cast_add]

theorem windowed_public_word_bounds
    (parameters : Initialization.Parameters babyBearModulus Source.BaseField)
    (row : Fin 8388608) (publicTops : Nat → Nat)
    (windows : ∀ set : Fin 2, parameters.windows set.val = publicTops set.val)
    (windowBound : ∀ set : Fin 2, publicTops set.val < 128) (set : Fin 2) :
    Initialization.addressLo row.val < 65536 ∧
    Initialization.addressHi Initialization.unified.layout parameters set.val row.val < 65536 := by
  have rowBound := row.isLt
  have upper : row.val / 16384 < 512 := by omega
  change _ ∧ row.val / 16384 + parameters.windows set.val * 512 < 65536
  rw [windows set]
  constructor
  · exact Nat.mod_lt _ (by decide)
  · have product : publicTops set.val * 512 ≤ 127 * 512 := Nat.mul_le_mul_right 512 (by have := windowBound set; omega)
    omega

theorem windowed_public_bounds
    (parameters : Initialization.Parameters babyBearModulus Source.BaseField)
    (row : Fin 8388608) (publicTops : Nat → Nat)
    (windows : ∀ set : Fin 2, parameters.windows set.val = publicTops set.val)
    (windowBound : ∀ set : Fin 2, publicTops set.val < 128) (set : Fin 2) :
    Initialization.addressLo row.val < babyBearModulus ∧
    Initialization.addressHi Initialization.unified.layout parameters set.val row.val < babyBearModulus := by
  have bounds := windowed_public_word_bounds parameters row publicTops windows windowBound set
  constructor <;> change _ < 2013265921 <;> omega

/-- Connect the actual per-set native factor to the retained public boundary
leaf under the native row-address and scalar-column interface laws. -/
theorem windowed_public_leaf
    (parameters : Initialization.Parameters babyBearModulus Source.BaseField)
    (memory : Source.MemoryValues) (raw : Initialization.Raw babyBearModulus)
    (row : Fin 8388608) (publicTops : Nat → Nat)
    (windows : ∀ set : Fin 2, parameters.windows set.val = publicTops set.val)
    (windowBound : ∀ set : Fin 2, publicTops set.val < 128)
    (low : memory.initializationAddress 0 = (Initialization.addressLo row.val : Source.BaseField))
    (high : memory.initializationAddress 1 = (row.val / 16384 : Nat))
    (set : Fin 2) (stageKind : Initialization.Phase)
    (timeLo : memory.teardownTimestamp set.val 0 = raw row.val Initialization.unified.layout.columns[set].timeLo)
    (timeHi : memory.teardownTimestamp set.val 1 = raw row.val Initialization.unified.layout.columns[set].timeHi)
    (valueLo : memory.teardownValue set.val 0 = raw row.val Initialization.unified.layout.columns[set].valueLo)
    (valueHi : memory.teardownValue set.val 1 = raw row.val Initialization.unified.layout.columns[set].valueHi) :
    windowedBoundaryToken memory publicTops stageKind set.val 512 =
      (Initialization.Leaf.mk stageKind set.val Initialization.unified.layout.columns[set]).token
        Initialization.unified.layout parameters raw row.val := by
  have addresses := windowed_public_addresses parameters memory row publicTops windows low high set
  have bounds := windowed_public_bounds parameters row publicTops windows windowBound set
  exact windowed_boundary_leaf Initialization.unified.layout parameters memory publicTops raw stageKind set row
    addresses.1 addresses.2 bounds.1 bounds.2 timeLo timeHi valueLo valueHi

end Airbender.Compiler
