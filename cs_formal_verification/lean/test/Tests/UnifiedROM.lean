import Slop.Trace.Timestamps
import Slop.UnifiedReduced.Completeness.RomLoad
import Human.Circuits.UnifiedReduced.Decoder
import Slop.ByteTables
import Slop.OpIndex
import Slop.Trace.ROMView
import Slop.UnifiedReduced

namespace Tests.UnifiedROM
open Airbender UnifiedReduced Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 16384

/-- LW x3, 0(x0) from the ROM word 0xdeadbeef at PC 0, clock 4. -/
private def witness : Completeness.RomLoad :=
  ⟨⟨0, 0, 4, 0, 0, 0, 0, 0, 0, 0⟩, 0, 3, 0, 0, 0, 0, 0xbeef, 0xdead, 0, 0, 0, 0⟩
private def assignment : Nat → ZMod babyBearModulus := witness.honest

theorem shadow_read_is_zero : (Word.mk (assignment 42).val (assignment 43).val).toBitVec = 0 := by rfl

end Tests.UnifiedROM
