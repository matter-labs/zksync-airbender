import Slop.RV.Code.ext4_mul_add
import Slop.Sym.Meta

/-! `ext4_mul_add` in plain Rust (Ext4 tower Karatsuba, `ops/basic.rs` arithmetic, all inlined): the symbolic run of
its body, once. -/

namespace RV

sym_block MulAdd := Code.ext4_mul_add

end RV
