import Slop.RV.Code.fs_check
import Slop.RV.Code.finish_error
import Slop.Sym.Meta

/-! `fs_check` (same words in both images except the calls): the symbolic runs of its straight-line blocks — A (the
challenge, up to the call of `ext4_poly`), B (the comparison, up to the branch), E (the epilogue, up to `ret`). -/

namespace RV

sym_run FsA := Code.fs_check.take 53
sym_run FsB := (Code.fs_check.drop 54).take 50
sym_run FsE := (Code.fs_check.drop 105).take 6
-- `zksync_os_finish_error`: its prologue, up to the `csrrw x0, cycle, x0` that ends the run
sym_run FinErr := Code.finish_error.take 4

end RV
