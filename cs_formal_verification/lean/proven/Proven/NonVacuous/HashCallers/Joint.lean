module
public import Proven.NonVacuous.Blake2GSpan.From

@[expose] public section

/-! The joint cells of a machine path followed by a complete G span: x0 and the span's cells, the keys of the one
    sequential run (`SequentialBlocks.joint_matching`). -/

namespace Airbender.NonVacuous.HashCallers
open Trace NonVacuous.Blake2GSpan

/-- The joint cells: x0 and the span's cells. -/
def keys : List Cell := .register 0 :: cells

theorem keys_nodup : keys.Nodup := by decide +kernel

end Airbender.NonVacuous.HashCallers
