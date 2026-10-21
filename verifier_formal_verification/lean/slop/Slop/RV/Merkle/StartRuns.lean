import Slop.Sym.Meta
import Slop.RV.Code.merkle_check

/-! The symbolic runs of `merkle_check`'s start and loop (for `RV/Merkle/Check.lean`, `RV/Merkle/Loop.lean`): the
prologue (words 0 … 14), `li a1, 32` (24), the leaf's loads and `lui s10` (26 … 34), the leaf's stores into
`MERKLE.state` (35 … 42), `MERKLE` into `s1` (44, 45); in the loop, the sibling's stores below `sp` and the call's
arguments (55 … 64), the count down (66). -/

namespace RV
open RV.Sym
set_option maxHeartbeats 400000

sym_run MPro := Code.merkle_check.take 15
sym_run MLim := (Code.merkle_check.drop 24).take 1
sym_run MLoad := (Code.merkle_check.drop 26).take 9
sym_run MStore := (Code.merkle_check.drop 35).take 8
sym_run MS1 := (Code.merkle_check.drop 44).take 2
sym_run MSib := (Code.merkle_check.drop 55).take 10
sym_run MDec := (Code.merkle_check.drop 66).take 1

end RV
