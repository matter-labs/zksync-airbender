module
public import Human.Helpers.Memory.InitialImage

@[expose] public section

namespace Airbender.Trace
open Arithmetic

namespace ROMView

/-- Native initialization: zero values for all tracked GPR/RAM slots, including
    ROM slots, with zero prior timestamps. The address domain is public. -/
def nativeBootImage {p : Nat} (cells : List Cell) : List (MemoryToken p) :=
  cells.map fun cell => cell.initialToken 0

end ROMView

end Airbender.Trace
