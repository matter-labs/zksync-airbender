import Airbender.Review.Helpers.Tables.WordROMImage
import Airbender.Review.Circuits.ReducedMachine.WordMemoryResult

namespace Airbender.ReducedMachine.NativeROM
open Verification Reference.RiscV.Sail
set_option autoImplicit false

/-- The actual eight-word native public fixture. The unchanged WordROM fallback
    repeats its last word, UNIMP, throughout the remaining four-MiB region. -/
def fixture : WordROM :=
  ⟨(List.range 8).map (fun i => BitVec.ofNat 32 ((NativeFixed.dataImage.get? i).getD 0)), by decide⟩

/-- Little-endian bytes of the actual fixture and its complete UNIMP tail. -/
def byte (key : Nat) : BitVec 8 :=
  (fixture.word (key/4)).extractLsb' (8*(key%4)) 8

/-- Finite original Sail byte inserts. The extent remains symbolic in proofs;
    no missing byte is replaced by a default read value. -/
def byteMemory (memory : Std.ExtHashMap Nat (BitVec 8)) : Nat → Std.ExtHashMap Nat (BitVec 8)
  | 0 => memory
  | count+1 => (byteMemory memory count).insert count (byte count)

/-- Construct the exact native ROM bytes, retaining all registers and every byte
    at or above four MiB. This is a logical reference input constructor, not a
    Rust loader/export or physical preprocessing certificate. -/
def state (before : State) : State :=
  { before with mem := byteMemory before.mem 4194304 }


/-- Complete descriptor computed from the public fixture and its native tail.
    The proof layer connects the original public byte extractor to this value. -/
def complete : WordROM where
  words := (Vector.ofFn fun i : Fin 1048576 => fixture.word i.val).toList
  capacity := by simp

end Airbender.ReducedMachine.NativeROM
