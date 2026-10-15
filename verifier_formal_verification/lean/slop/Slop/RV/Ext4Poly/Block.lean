import Slop.RV.Code.ext4_poly
import Slop.Sym.Meta

/-! `ext4_poly` in plain Rust: the symbolic runs of its two straight-line blocks, before the call to `ext4_horner`
(words 0 … 85: `new` on the four limbs of `y`) and after it (words 87 … 138: `to_u32` on the result). -/

namespace RV

sym_run PolyA := Code.ext4_poly.take 86
sym_run PolyB := (Code.ext4_poly.drop 87).take 52

end RV
