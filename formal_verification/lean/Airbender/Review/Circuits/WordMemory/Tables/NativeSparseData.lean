import Airbender.Import.SetupEmbed
import Airbender.Review.Helpers.Decoder.WordMemorySparse

namespace Airbender.WordMemory.NativeSparse
open Trace Reference.RiscV.Sail

import_native_setup holes from "artifacts/setup/word-memory-holes-native.json"

def words : Vector (BitVec 32) 4 := #v[0x0100a183, 0xc0001073, 0x0030a823, 0x0100a003]

def programROM : Verification.WordROM := ⟨words.toList, by decide⟩

/-- Public input bytes, independent of the witness and decoded table. -/
def before : State :=
  { (default : State) with mem := ((Std.ExtHashMap.emptyWithCapacity : Std.ExtHashMap Nat (BitVec 8))
    |>.insert 0 0x83 |>.insert 1 0xa1 |>.insert 2 0 |>.insert 3 1
    |>.insert 4 0x73 |>.insert 5 0x10 |>.insert 6 0 |>.insert 7 0xc0
    |>.insert 8 0x23 |>.insert 9 0xa8 |>.insert 10 0x30 |>.insert 11 0
    |>.insert 12 0x03 |>.insert 13 0xa0 |>.insert 14 0 |>.insert 15 1) }

def loadEntry : ProgramEntry WordMemoryFamily :=
  ⟨0, 0x0100a183, .LOAD (16, .Regidx 1, .Regidx 3, false, 4),
    ⟨.wordMemory, 1, 0, 3, ⟨16,0⟩, 0, 2⟩⟩
def storeEntry : ProgramEntry WordMemoryFamily :=
  ⟨8, 0x0030a823, .STORE (16, .Regidx 3, .Regidx 1, 4),
    ⟨.wordMemory, 1, 3, 0, ⟨16,0⟩, 1, 2⟩⟩
def x0Entry : ProgramEntry WordMemoryFamily :=
  ⟨12, 0x0100a003, .LOAD (16, .Regidx 1, .Regidx 0, false, 4),
    ⟨.wordMemory, 1, 0, 0, ⟨16,0⟩, 0, 2⟩⟩

/-- Supported PCs retain their original positions around the UNIMP hole. -/
def setup : SparseDecoderSetup WordMemoryFamily :=
  ⟨[some loadEntry, none, some storeEntry, some x0Entry], 1048572⟩

end Airbender.WordMemory.NativeSparse
