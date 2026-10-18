import Airbender.Import.SetupEmbed
import Airbender.Review.Helpers.Decoder.SparseSetup

namespace Airbender.AddSub.NativeSetup
open Trace Reference.RiscV.Sail

import_native_decoder arithmetic from "artifacts/setup/arithmetic-native.json"

def words : Vector (BitVec 32) 7 :=
  #v[0x001080b3, 0xfff08113, 0x40208033, 0x000071b7, 0x00005217, 0xc0001073, 0x001080b3]

/-- Public code bytes, independent of witness values and decoder table rows. -/
def before : State :=
  { (default : State) with mem := ((Std.ExtHashMap.emptyWithCapacity : Std.ExtHashMap Nat (BitVec 8))
    |>.insert 0 0xb3 |>.insert 1 0x80 |>.insert 2 0x10 |>.insert 3 0x00
    |>.insert 4 0x13 |>.insert 5 0x81 |>.insert 6 0xf0 |>.insert 7 0xff
    |>.insert 8 0x33 |>.insert 9 0x80 |>.insert 10 0x20 |>.insert 11 0x40
    |>.insert 12 0xb7 |>.insert 13 0x71 |>.insert 14 0x00 |>.insert 15 0x00
    |>.insert 16 0x17 |>.insert 17 0x52 |>.insert 18 0x00 |>.insert 19 0x00
    |>.insert 20 0x73 |>.insert 21 0x10 |>.insert 22 0x00 |>.insert 23 0xc0
    |>.insert 24 0xb3 |>.insert 25 0x80 |>.insert 26 0x10 |>.insert 27 0x00) }

def addEntry : ProgramEntry :=
  ⟨0, 0x001080b3, .RTYPE (.Regidx 1, .Regidx 1, .Regidx 1, .ADD),
    ⟨.addSub, 1, 1, 1, ⟨0,0⟩, 1, 0⟩⟩
def addiEntry : ProgramEntry :=
  ⟨4, 0xfff08113, .ITYPE (4095, .Regidx 1, .Regidx 2, .ADDI),
    ⟨.addSub, 1, 0, 2, ⟨65535,65535⟩, 2, 0⟩⟩
def subEntry : ProgramEntry :=
  ⟨8, 0x40208033, .RTYPE (.Regidx 2, .Regidx 1, .Regidx 0, .SUB),
    ⟨.addSub, 1, 2, 0, ⟨0,0⟩, 4, 0⟩⟩
def luiEntry : ProgramEntry :=
  ⟨12, 0x000071b7, .UTYPE (7, .Regidx 3, .LUI),
    ⟨.addSub, 0, 0, 3, ⟨28672,0⟩, 8, 7⟩⟩
def auipcEntry : ProgramEntry :=
  ⟨16, 0x00005217, .UTYPE (5, .Regidx 4, .AUIPC),
    ⟨.addSub, 0, 0, 4, ⟨20480,0⟩, 16, 5⟩⟩
def laterEntry : ProgramEntry :=
  { addEntry with pc := 24 }

/-- Native indexing retains the UNIMP hole at PC 20 and the ADD at PC 24.
    Custom modular MOP words are outside this concrete public-input certificate. -/
def setup : SparseDecoderSetup Family :=
  ⟨[some addEntry, some addiEntry, some subEntry, some luiEntry, some auipcEntry,
    none, some laterEntry], 1048569⟩

end Airbender.AddSub.NativeSetup
