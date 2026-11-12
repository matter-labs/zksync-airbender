module
public import Human.Helpers.Memory.InitialImage
public import Human.Helpers.Memory.Native

/-! Definitions only the proofs use, moved from `human/Human/Helpers/Memory/Native.lean` (no claim states them). -/

@[expose] public section
namespace Airbender.Trace
open Arithmetic
namespace ROMView
/-- Native RAM addresses below the 4 MiB ROM limit. Their permutation values
    are zero, independently of the physical bytes used for fetch/ROM lookups.
    Source: `riscv_transpiler/src/replayer/mod.rs`, `mask_read_for_witness`. -/
def shadow (address : Nat) : Prop :=
  (Nat.unpair address).1 = 1 ∧ (Nat.unpair (Nat.unpair address).2).2 < 64
instance (address : Nat) : Decidable (shadow address) := inferInstanceAs
  (Decidable ((Nat.unpair address).1 = 1 ∧ (Nat.unpair (Nat.unpair address).2).2 < 64))
end ROMView
end Airbender.Trace
