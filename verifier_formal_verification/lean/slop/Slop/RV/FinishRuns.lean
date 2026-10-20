import Slop.Sym.Meta
import Slop.RV.Code.finish_success
import Slop.RV.Code.finish_success_extended

/-! The symbolic runs of riscv_common's finish blocks (for `RV/Finish.lean`, `RV/FinishExt.lean`): the straight-line
words of `zksync_os_finish_success` (up to its `jal ra`) and of `zksync_os_finish_success_extended` (up to its
self-jump). -/

namespace RV
set_option maxHeartbeats 400000

sym_run FinSucc := (Code.finish_success).take 29
sym_run FinExt := (Code.finish_success_extended).take 32

end RV
