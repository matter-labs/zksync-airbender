import Slop.Sym.Meta
import Slop.RV.Code.merkle_step

/-! The symbolic runs of `merkle_step`'s start (for `RV/Merkle/Step.lean`; the delegation build's `merkle_step`
starts with the same nine words): the frame (words 0 … 3), the halves swapped (5, 6), the node as the left half (8). -/

namespace RV
open RV.Sym
set_option maxHeartbeats 400000

sym_run MSPro := Code.merkle_step.take 4
sym_run MSSwap := (Code.merkle_step.drop 5).take 2
sym_run MSLeft := (Code.merkle_step.drop 8).take 1

end RV
