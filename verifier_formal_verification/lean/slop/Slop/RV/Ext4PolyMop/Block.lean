import Slop.RV.Code.ext4_poly_mop
import Slop.Sym.Meta

/-! `ext4_poly` with the field opcodes: the symbolic runs of its two straight-line blocks, before the call to
`ext4_horner` (words 0 … 28) and after it (words 30 … 46). -/

namespace RV

sym_run PolyMA := Code.ext4_poly_mop.take 29
sym_run PolyMB := (Code.ext4_poly_mop.drop 30).take 17

end RV
