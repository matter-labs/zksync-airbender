import Slop.Sym.Meta
import Slop.RV.Code.init

/-! The symbolic runs of `init`'s straight-line blocks (for `RV/Init.lean`), on the words both images share: the
prologue and the first two loads (words 0 … 7), the second (9, 10), the copy's arguments (12 … 16), the empty
`.data`'s (20 … 24), the epilogue (26 … 29). -/

namespace RV
open RV.Sym
set_option maxHeartbeats 400000

sym_run IPro := Code.init.take 8
sym_run IB := (Code.init.drop 9).take 2
sym_run IC := (Code.init.drop 12).take 5
sym_run ID := (Code.init.drop 20).take 5
sym_run IE := (Code.init.drop 26).take 4

end RV
