import Slop.RV.Code.main
import Slop.Sym.Meta

/-! `main` (same words in both images except the calls): the symbolic runs of its six straight-line blocks, each
ending at a call (`init`, `u32_combine`, `m31_poly_eval`, `ext4_poly`, `blake2s_compress`, `finish_success`). -/

namespace RV

sym_run Main0 := Code.main.take 12
sym_run Main1 := (Code.main.drop 13).take 8
sym_run Main2 := (Code.main.drop 22).take 5
sym_run Main3 := (Code.main.drop 28).take 7
sym_run Main4 := (Code.main.drop 36).take 32
sym_run Main5 := (Code.main.drop 69).take 15

end RV
