module
public import Slop.Trace.Timestamps
public import Slop.UnifiedReduced.Completeness.RomLoad
public import Human.Circuits.UnifiedReduced.Decoder
public import Slop.ByteTables
public import Slop.OpIndex
public import Slop.Trace.ROMView
public import Slop.UnifiedReduced

@[expose] public section

namespace Tests.UnifiedROM
open Airbender UnifiedReduced Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 16384

/-- LW x3, 0(x0) from the ROM word 0xdeadbeef at PC 0, clock 4. -/
def witness : Completeness.RomLoad :=
  ⟨⟨0, 0, 4, 0, 0, 0, 0, 0, 0, 0⟩, 0, 3, 0, 0, 0, 0, 0xbeef, 0xdead, 0, 0, 0, 0⟩
def assignment : Nat → ZMod babyBearModulus := witness.honest

theorem shadow_read_is_zero : (Word.mk (assignment 42).val (assignment 43).val).toBitVec = 0 := by rfl

end Tests.UnifiedROM
