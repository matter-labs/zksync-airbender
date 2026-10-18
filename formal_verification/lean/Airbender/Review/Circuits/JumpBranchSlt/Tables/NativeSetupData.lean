import Airbender.Import.SetupEmbed
import Airbender.Review.Circuits.JumpBranchSlt.Decoder

namespace Airbender.JumpBranchSlt.NativeSetup
open Trace Reference.RiscV.Sail

import_native_control_decoder control from "artifacts/setup/jump-decoder-native.json"

def words : Vector (BitVec 32) 3 := #v[0xffdff0ef, 0xc0001073, 0xfff0b013]

/-- The public image is actual instruction bytes, independent of native values. -/
def before : State :=
  { (default : State) with mem := ((Std.ExtHashMap.emptyWithCapacity : Std.ExtHashMap Nat (BitVec 8))
    |>.insert 0 0xef |>.insert 1 0xf0 |>.insert 2 0xdf |>.insert 3 0xff
    |>.insert 4 0x73 |>.insert 5 0x10 |>.insert 6 0x00 |>.insert 7 0xc0
    |>.insert 8 0x13 |>.insert 9 0xb0 |>.insert 10 0xf0 |>.insert 11 0xff) }

def jalEntry : JumpBranchSlt.ProgramEntry :=
  ⟨0, 0xffdff0ef, .JAL (0x1ffffc, .Regidx 1),
    ⟨(), 0, 0, 1, ⟨65532, 65535⟩, 1, 7⟩⟩

def sltiEntry : JumpBranchSlt.ProgramEntry :=
  ⟨8, 0xfff0b013, .ITYPE (4095, .Regidx 1, .Regidx 0, .SLTIU),
    ⟨(), 1, 0, 0, ⟨65535, 65535⟩, 8, 3⟩⟩

def setup : SparseDecoderSetup Unit :=
  ⟨[some jalEntry, none, some sltiEntry], 1048573⟩

end Airbender.JumpBranchSlt.NativeSetup
