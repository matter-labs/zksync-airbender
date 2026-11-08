module
public import Human.Helpers.Decoder.Program
public import Human.Helpers.Context.FamilyLayout

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

/-- Native initialization: zero values for all tracked GPR/RAM slots, including
    ROM slots, with zero prior timestamps. The address domain is public. -/
def nativeBootImage {p : Nat} (cells : List Cell) : List (MemoryToken p) :=
  cells.map fun cell => cell.initialToken 0

end ROMView

end Airbender.Trace
