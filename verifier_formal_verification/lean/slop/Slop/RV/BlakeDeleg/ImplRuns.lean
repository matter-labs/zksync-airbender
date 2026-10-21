import Slop.Sym.Meta
import Slop.RV.Code.blake2s_compress_mop

/-! The symbolic runs of `blake2s_compress` by the round-function delegation (for `RV/BlakeDeleg/Impl.lean`): the
prologue, the counter and the last-block words (words 0 … 17); the epilogue after the seven calls (25 … 27). -/

namespace RV
open RV.Sym
set_option maxHeartbeats 400000

sym_run BDPro := Code.blake2s_compress_mop.take 18
sym_run BDEpi := (Code.blake2s_compress_mop.drop 25).take 3

end RV
