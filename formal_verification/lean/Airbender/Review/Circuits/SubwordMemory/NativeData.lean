import Airbender.Import.SetupEmbed
import Airbender.Review.Circuits.SubwordMemory.Decoder

namespace Airbender.SubwordMemory.NativeSetup
open Arithmetic Trace Reference.RiscV.Sail
set_option autoImplicit false

import_native_subword_decoder native from "artifacts/setup/subword-decoder-native.json"

/-- Independent original instruction words; the final LW is an unsupported slot. -/
def words : Vector (BitVec 32) 13 :=
  #v[0x00008183, 0x00009183, 0x0000c183, 0x0000d183, 0x00208023, 0x00209023, 0xfff08003, 0xfff09003, 0xfff0c003, 0xfff0d003, 0xfe208fa3, 0xfe209fa3, 0x0000a183]

def entries : Vector SubwordMemory.ProgramEntry 12 :=
  #v[⟨0,0x00008183,.LOAD (0,.Regidx 1,.Regidx 3,false,1),⟨.lb,1,0,3,⟨0,0⟩,0,0⟩⟩,
    ⟨4,0x00009183,.LOAD (0,.Regidx 1,.Regidx 3,false,2),⟨.lh,1,0,3,⟨0,0⟩,0,1⟩⟩,
    ⟨8,0x0000c183,.LOAD (0,.Regidx 1,.Regidx 3,true,1),⟨.lbu,1,0,3,⟨0,0⟩,0,4⟩⟩,
    ⟨12,0x0000d183,.LOAD (0,.Regidx 1,.Regidx 3,true,2),⟨.lhu,1,0,3,⟨0,0⟩,0,5⟩⟩,
    ⟨16,0x00208023,.STORE (0,.Regidx 2,.Regidx 1,1),⟨.sb,1,2,0,⟨0,0⟩,1,0⟩⟩,
    ⟨20,0x00209023,.STORE (0,.Regidx 2,.Regidx 1,2),⟨.sh,1,2,0,⟨0,0⟩,1,1⟩⟩,
    ⟨24,0xfff08003,.LOAD (4095,.Regidx 1,.Regidx 0,false,1),⟨.lb,1,0,0,⟨65535,65535⟩,0,0⟩⟩,
    ⟨28,0xfff09003,.LOAD (4095,.Regidx 1,.Regidx 0,false,2),⟨.lh,1,0,0,⟨65535,65535⟩,0,1⟩⟩,
    ⟨32,0xfff0c003,.LOAD (4095,.Regidx 1,.Regidx 0,true,1),⟨.lbu,1,0,0,⟨65535,65535⟩,0,4⟩⟩,
    ⟨36,0xfff0d003,.LOAD (4095,.Regidx 1,.Regidx 0,true,2),⟨.lhu,1,0,0,⟨65535,65535⟩,0,5⟩⟩,
    ⟨40,0xfe208fa3,.STORE (4095,.Regidx 2,.Regidx 1,1),⟨.sb,1,2,0,⟨65535,65535⟩,1,0⟩⟩,
    ⟨44,0xfe209fa3,.STORE (4095,.Regidx 2,.Regidx 1,2),⟨.sh,1,2,0,⟨65535,65535⟩,1,1⟩⟩]

def instructions : Vector SailRV32.instruction 13 :=
  #v[entries[0].instruction, entries[1].instruction, entries[2].instruction, entries[3].instruction, entries[4].instruction, entries[5].instruction, entries[6].instruction, entries[7].instruction, entries[8].instruction, entries[9].instruction, entries[10].instruction, entries[11].instruction, .LOAD (0,.Regidx 1,.Regidx 3,false,4)]

/-- Public byte memory is independent of the exported metadata columns. -/
def before : State :=
  { (default : State) with mem := ((Std.ExtHashMap.emptyWithCapacity : Std.ExtHashMap Nat (BitVec 8))
      |>.insert 0 0x83
      |>.insert 1 0x81
      |>.insert 2 0x00
      |>.insert 3 0x00
      |>.insert 4 0x83
      |>.insert 5 0x91
      |>.insert 6 0x00
      |>.insert 7 0x00
      |>.insert 8 0x83
      |>.insert 9 0xc1
      |>.insert 10 0x00
      |>.insert 11 0x00
      |>.insert 12 0x83
      |>.insert 13 0xd1
      |>.insert 14 0x00
      |>.insert 15 0x00
      |>.insert 16 0x23
      |>.insert 17 0x80
      |>.insert 18 0x20
      |>.insert 19 0x00
      |>.insert 20 0x23
      |>.insert 21 0x90
      |>.insert 22 0x20
      |>.insert 23 0x00
      |>.insert 24 0x03
      |>.insert 25 0x80
      |>.insert 26 0xf0
      |>.insert 27 0xff
      |>.insert 28 0x03
      |>.insert 29 0x90
      |>.insert 30 0xf0
      |>.insert 31 0xff
      |>.insert 32 0x03
      |>.insert 33 0xc0
      |>.insert 34 0xf0
      |>.insert 35 0xff
      |>.insert 36 0x03
      |>.insert 37 0xd0
      |>.insert 38 0xf0
      |>.insert 39 0xff
      |>.insert 40 0xa3
      |>.insert 41 0x8f
      |>.insert 42 0x20
      |>.insert 43 0xfe
      |>.insert 44 0xa3
      |>.insert 45 0x9f
      |>.insert 46 0x20
      |>.insert 47 0xfe
      |>.insert 48 0x83
      |>.insert 49 0xa1
      |>.insert 50 0x00
      |>.insert 51 0x00
  ) }

/-- Preserve native slot positions, original x0 instructions and the complete tail. -/
def setup : SparseDecoderSetup Operation :=
  ⟨[some entries[0], some entries[1], some entries[2], some entries[3], some entries[4], some entries[5], some entries[6], some entries[7], some entries[8], some entries[9], some entries[10], some entries[11],none],1048563⟩

end Airbender.SubwordMemory.NativeSetup
