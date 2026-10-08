import Airbender.Review.Trace.Execution
import Airbender.Review.Trace.Initialization

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

/-- Read physical ROM bytes from the public Sail state. The fallback is
    unreachable for cells in a successfully constructed initial image. -/
def publicWord (before : Reference.RiscV.Sail.State) (address : Nat) : Word :=
  let limbs := Nat.unpair (Nat.unpair address).2
  match (Cell.ram (Word.mk limbs.1 limbs.2).toBitVec).read before with
  | .ok value _ => Word.ofBitVec value
  | .error _ _ => ⟨0, 0⟩

/-- Interpretation of a native terminal token. Only readonly ROM slots use
    public physical bytes; register and non-ROM RAM values stay unchanged. -/
def token (before : Reference.RiscV.Sail.State) (native : MemoryToken p) : MemoryToken p :=
  if shadow native.address then
    { native with value := (Nat.pair (publicWord before native.address).lo
      (publicWord before native.address).hi) }
  else native

end ROMView

/-- Native zero-initialized execution. Program/ROM bytes come from the public
    Sail image, separately from zero-valued native ROM permutation slots.
    Logical matching and decoder membership remain separate theorem premises. -/
structure NativeBootBoundary {p : Nat} [Fact p.Prime] (trace : Data p)
    (before : Reference.RiscV.Sail.State) (cells : List Cell) (program : List ProgramEntry)
    (projection : SailRV32.instruction → Option DecoderData := decoderFields) : Prop
    extends PublicBoundary before cells program projection where
  profile : InitialProfile before cells
  seed : trace.initialMemory = ROMView.nativeBootImage cells
  initial : trace.initial = PCState.boundary 0 (4, 0)
  rom : ∃ image, initialImage before cells = some image ∧ trace.rom = ROM.table cells image

end Airbender.Trace
