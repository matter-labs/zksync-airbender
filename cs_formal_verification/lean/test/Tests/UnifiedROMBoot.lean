import Tests.TraceExecution
import Slop.UnifiedReduced.Claims
import Slop.UnifiedReduced.Completeness.RomLoad

namespace Tests.UnifiedROMBoot
open Airbender Arithmetic Trace
set_option warningAsError true
set_option maxRecDepth 16384

/-- LW x1, 0(x0) from the ROM word 0x2083 at PC 0, clock 4. -/
private def witness : UnifiedReduced.Completeness.RomLoad :=
  ⟨⟨0, 0, 4, 0, 0, 0, 0, 0, 0, 0⟩, 0, 1, 0, 0, 0, 0, 0x2083, 0, 0, 0, 0, 0⟩
private theorem load_col : witness.honest 28 = 1 := rfl
private theorem rom_col : witness.honest 54 = 1 := rfl
private theorem lo_col : (witness.honest 38).val = 0 := rfl
private theorem hi_col : (witness.honest 39).val = 0 := rfl

end Tests.UnifiedROMBoot
