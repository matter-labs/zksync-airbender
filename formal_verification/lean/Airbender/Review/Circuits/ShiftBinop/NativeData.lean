import Airbender.Import.SetupEmbed
import Airbender.Review.Circuits.ShiftBinop.Decoder

namespace Airbender.ShiftBinop.NativeSetup
open Trace Reference.RiscV.Sail

import_native_shift_decoder native from "artifacts/setup/shift-decoder-native.json"

/-- Public original instruction bytes, independent of native exported metadata. -/
def words : Vector (BitVec 32) 25 :=
  #v[0x002091b3, 0x0020d1b3, 0x4020d1b3, 0x0020c1b3, 0x0020e1b3, 0x0020f1b3, 0x01f09193, 0x01f0d193, 0x41f0d193, 0xfff0c193, 0x8000e193, 0x7ff0f193, 0x00209033, 0x0020d033, 0x4020d033, 0x0020c033, 0x0020e033, 0x0020f033, 0x01f09013, 0x01f0d013, 0x41f0d013, 0xfff0c013, 0x8000e013, 0x7ff0f013, 0x001080b3]

def entries : Vector ProgramEntry 24 :=
  #v[⟨0,0x002091b3,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.SLL),⟨.sll,1,2,3,⟨0,0⟩,1,1⟩⟩,
    ⟨4,0x0020d1b3,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.SRL),⟨.srl,1,2,3,⟨0,0⟩,2,5⟩⟩,
    ⟨8,0x4020d1b3,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.SRA),⟨.sra,1,2,3,⟨0,0⟩,4,5⟩⟩,
    ⟨12,0x0020c1b3,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.XOR),⟨.xor,1,2,3,⟨0,0⟩,8,4⟩⟩,
    ⟨16,0x0020e1b3,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.OR),⟨.or,1,2,3,⟨0,0⟩,8,6⟩⟩,
    ⟨20,0x0020f1b3,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 3,.AND),⟨.and,1,2,3,⟨0,0⟩,8,7⟩⟩,
    ⟨24,0x01f09193,.SHIFTIOP (31,.Regidx 1,.Regidx 3,.SLLI),⟨.sll,1,0,3,⟨31,0⟩,33,1⟩⟩,
    ⟨28,0x01f0d193,.SHIFTIOP (31,.Regidx 1,.Regidx 3,.SRLI),⟨.srl,1,0,3,⟨31,0⟩,34,5⟩⟩,
    ⟨32,0x41f0d193,.SHIFTIOP (31,.Regidx 1,.Regidx 3,.SRAI),⟨.sra,1,0,3,⟨1055,0⟩,36,5⟩⟩,
    ⟨36,0xfff0c193,.ITYPE (4095,.Regidx 1,.Regidx 3,.XORI),⟨.xor,1,0,3,⟨65535,65535⟩,40,4⟩⟩,
    ⟨40,0x8000e193,.ITYPE (2048,.Regidx 1,.Regidx 3,.ORI),⟨.or,1,0,3,⟨63488,65535⟩,40,6⟩⟩,
    ⟨44,0x7ff0f193,.ITYPE (2047,.Regidx 1,.Regidx 3,.ANDI),⟨.and,1,0,3,⟨2047,0⟩,40,7⟩⟩,
    ⟨48,0x00209033,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 0,.SLL),⟨.sll,1,2,0,⟨0,0⟩,1,1⟩⟩,
    ⟨52,0x0020d033,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 0,.SRL),⟨.srl,1,2,0,⟨0,0⟩,2,5⟩⟩,
    ⟨56,0x4020d033,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 0,.SRA),⟨.sra,1,2,0,⟨0,0⟩,4,5⟩⟩,
    ⟨60,0x0020c033,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 0,.XOR),⟨.xor,1,2,0,⟨0,0⟩,8,4⟩⟩,
    ⟨64,0x0020e033,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 0,.OR),⟨.or,1,2,0,⟨0,0⟩,8,6⟩⟩,
    ⟨68,0x0020f033,.RTYPE (.Regidx 2,.Regidx 1,.Regidx 0,.AND),⟨.and,1,2,0,⟨0,0⟩,8,7⟩⟩,
    ⟨72,0x01f09013,.SHIFTIOP (31,.Regidx 1,.Regidx 0,.SLLI),⟨.sll,1,0,0,⟨31,0⟩,33,1⟩⟩,
    ⟨76,0x01f0d013,.SHIFTIOP (31,.Regidx 1,.Regidx 0,.SRLI),⟨.srl,1,0,0,⟨31,0⟩,34,5⟩⟩,
    ⟨80,0x41f0d013,.SHIFTIOP (31,.Regidx 1,.Regidx 0,.SRAI),⟨.sra,1,0,0,⟨1055,0⟩,36,5⟩⟩,
    ⟨84,0xfff0c013,.ITYPE (4095,.Regidx 1,.Regidx 0,.XORI),⟨.xor,1,0,0,⟨65535,65535⟩,40,4⟩⟩,
    ⟨88,0x8000e013,.ITYPE (2048,.Regidx 1,.Regidx 0,.ORI),⟨.or,1,0,0,⟨63488,65535⟩,40,6⟩⟩,
    ⟨92,0x7ff0f013,.ITYPE (2047,.Regidx 1,.Regidx 0,.ANDI),⟨.and,1,0,0,⟨2047,0⟩,40,7⟩⟩]

def instructions : Vector SailRV32.instruction 25 :=
  #v[entries[0].instruction, entries[1].instruction, entries[2].instruction, entries[3].instruction, entries[4].instruction, entries[5].instruction, entries[6].instruction, entries[7].instruction, entries[8].instruction, entries[9].instruction, entries[10].instruction, entries[11].instruction, entries[12].instruction, entries[13].instruction, entries[14].instruction, entries[15].instruction, entries[16].instruction, entries[17].instruction, entries[18].instruction, entries[19].instruction, entries[20].instruction, entries[21].instruction, entries[22].instruction, entries[23].instruction, .RTYPE (.Regidx 1,.Regidx 1,.Regidx 1,.ADD)]

/-- Actual public Sail byte memory; misa is an ordinary public configuration. -/
def before : State :=
  { (default : State) with
    regs := Std.ExtDHashMap.emptyWithCapacity |>.insert .misa (0x40000100 : BitVec 32)
    mem := ((Std.ExtHashMap.emptyWithCapacity : Std.ExtHashMap Nat (BitVec 8))
      |>.insert 0 0xb3
      |>.insert 1 0x91
      |>.insert 2 0x20
      |>.insert 3 0x00
      |>.insert 4 0xb3
      |>.insert 5 0xd1
      |>.insert 6 0x20
      |>.insert 7 0x00
      |>.insert 8 0xb3
      |>.insert 9 0xd1
      |>.insert 10 0x20
      |>.insert 11 0x40
      |>.insert 12 0xb3
      |>.insert 13 0xc1
      |>.insert 14 0x20
      |>.insert 15 0x00
      |>.insert 16 0xb3
      |>.insert 17 0xe1
      |>.insert 18 0x20
      |>.insert 19 0x00
      |>.insert 20 0xb3
      |>.insert 21 0xf1
      |>.insert 22 0x20
      |>.insert 23 0x00
      |>.insert 24 0x93
      |>.insert 25 0x91
      |>.insert 26 0xf0
      |>.insert 27 0x01
      |>.insert 28 0x93
      |>.insert 29 0xd1
      |>.insert 30 0xf0
      |>.insert 31 0x01
      |>.insert 32 0x93
      |>.insert 33 0xd1
      |>.insert 34 0xf0
      |>.insert 35 0x41
      |>.insert 36 0x93
      |>.insert 37 0xc1
      |>.insert 38 0xf0
      |>.insert 39 0xff
      |>.insert 40 0x93
      |>.insert 41 0xe1
      |>.insert 42 0x00
      |>.insert 43 0x80
      |>.insert 44 0x93
      |>.insert 45 0xf1
      |>.insert 46 0xf0
      |>.insert 47 0x7f
      |>.insert 48 0x33
      |>.insert 49 0x90
      |>.insert 50 0x20
      |>.insert 51 0x00
      |>.insert 52 0x33
      |>.insert 53 0xd0
      |>.insert 54 0x20
      |>.insert 55 0x00
      |>.insert 56 0x33
      |>.insert 57 0xd0
      |>.insert 58 0x20
      |>.insert 59 0x40
      |>.insert 60 0x33
      |>.insert 61 0xc0
      |>.insert 62 0x20
      |>.insert 63 0x00
      |>.insert 64 0x33
      |>.insert 65 0xe0
      |>.insert 66 0x20
      |>.insert 67 0x00
      |>.insert 68 0x33
      |>.insert 69 0xf0
      |>.insert 70 0x20
      |>.insert 71 0x00
      |>.insert 72 0x13
      |>.insert 73 0x90
      |>.insert 74 0xf0
      |>.insert 75 0x01
      |>.insert 76 0x13
      |>.insert 77 0xd0
      |>.insert 78 0xf0
      |>.insert 79 0x01
      |>.insert 80 0x13
      |>.insert 81 0xd0
      |>.insert 82 0xf0
      |>.insert 83 0x41
      |>.insert 84 0x13
      |>.insert 85 0xc0
      |>.insert 86 0xf0
      |>.insert 87 0xff
      |>.insert 88 0x13
      |>.insert 89 0xe0
      |>.insert 90 0x00
      |>.insert 91 0x80
      |>.insert 92 0x13
      |>.insert 93 0xf0
      |>.insert 94 0xf0
      |>.insert 95 0x7f
      |>.insert 96 0xb3
      |>.insert 97 0x80
      |>.insert 98 0x10
      |>.insert 99 0x00
) }

/-- Indexed ordinary forms keep their original x0 opcodes. ADD is an interior
    unsupported slot; all remaining native capacity is retained as padding. -/
def setup : SparseDecoderSetup Operation :=
  ⟨[some entries[0], some entries[1], some entries[2], some entries[3], some entries[4], some entries[5], some entries[6], some entries[7], some entries[8], some entries[9], some entries[10], some entries[11], some entries[12], some entries[13], some entries[14], some entries[15], some entries[16], some entries[17], some entries[18], some entries[19], some entries[20], some entries[21], some entries[22], some entries[23], none],1048551⟩

end Airbender.ShiftBinop.NativeSetup
