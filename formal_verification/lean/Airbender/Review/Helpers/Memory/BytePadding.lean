import Airbender.Review.Helpers.Memory.InitialImage

namespace Airbender.Reference.RiscV.Sail

/-- Explicit zero-byte inserts into the original Sail memory. This constructor
    changes only the selected finite interval; it supplies no default read value. -/
def zeroByteMemory (memory : Std.ExtHashMap Nat (BitVec 8)) (start : Nat) : Nat → Std.ExtHashMap Nat (BitVec 8)
  | 0 => memory
  | count + 1 => (zeroByteMemory memory start count).insert (start + count) 0

/-- Pad the public ROM byte tail to four MiB. The successful public prefix
    constructor supplies `words`; excessive counts are rejected there. -/
def paddedROMState (before : State) (words : Nat) : State :=
  { before with mem := zeroByteMemory before.mem (4 * words) (4194304 - 4 * words) }

end Airbender.Reference.RiscV.Sail
