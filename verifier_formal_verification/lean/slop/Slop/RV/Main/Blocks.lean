import Slop.RV.Code.main
import Slop.RV.Code.main_mop
import Slop.Sym.Meta

/-! `main` (same words in both images except the calls): the symbolic runs of its six straight-line blocks, each
ending at a call (`init`, `u32_combine`, `m31_poly_eval`, `ext4_poly`, `blake2s_compress`, `fs_check`,
`merkle_check`, `finish_success`). The input reads (words 13 … 17 and 69 … 72) are single steps. -/

namespace RV

sym_run Main0 := Code.main.take 12
sym_run Main1 := (Code.main.drop 18).take 1
sym_run Main2 := (Code.main.drop 20).take 5
sym_run Main3 := (Code.main.drop 26).take 7
sym_run Main4 := (Code.main.drop 34).take 34
-- the delegation build (`main_mop`): the input words at `BLAKE + 0x80`
sym_run Main4D := (Code.main_mop.drop 34).take 34
sym_run MainF := (Code.main.drop 73).take 6
sym_run MainM := (Code.main.drop 80).take 1
sym_run Main5 := (Code.main.drop 82).take 15

end RV
