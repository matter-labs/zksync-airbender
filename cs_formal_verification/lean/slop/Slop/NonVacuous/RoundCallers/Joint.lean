module
public import Slop.NonVacuous.Blake2RoundSpan.Span

@[expose] public section

/-! The joint cells of a machine path followed by a complete extended-round span (as `HashCallers/Joint.lean` for the
    G span): x0 and the span's cells, the keys of the one sequential run (`SequentialBlocks.joint_matching`). -/

namespace Airbender.NonVacuous.RoundCallers
open Trace

/-- The joint cells: x0 and the span's cells. -/
def keys : List Cell := .register 0 :: Blake2RoundSpan.cells

theorem keys_nodup : keys.Nodup := by decide +kernel

end Airbender.NonVacuous.RoundCallers
