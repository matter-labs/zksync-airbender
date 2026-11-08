import Human.Helpers.Context.RowContext
import Slop.Trace.RowHistory
namespace Airbender.Trace.Proofs
open Arithmetic

theorem row_write_values {Kind : Type} [CircuitLayout Kind] (epoch : Nat) (row : Row p Kind) :
    ((rowEvents epoch row).reverse.map fun event => (event.2.1, event.2.2.2)) = rowWriteValues row := by
  simp [rowEvents, nativeRowEvents, rowWriteValues, Row.writes, writeToken,
    List.map_reverse, List.map_map, Function.comp_def]

end Airbender.Trace.Proofs
