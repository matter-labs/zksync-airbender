import Slop.RV.Link
import ImageMop
import Slop.RV.Code.COEFFS
import Slop.RV.Code.COEFFS4
import Slop.RV.Code.add_mod
import Slop.RV.Code.blake2s_compress_mop
import Slop.RV.Code.combine
import Slop.RV.Code.double
import Slop.RV.Code.ext4_horner
import Slop.RV.Code.ext4_mul_add_mop
import Slop.RV.Code.ext4_poly_mop
import Slop.RV.Code.finish_error
import Slop.RV.Code.finish_success
import Slop.RV.Code.finish_success_extended
import Slop.RV.Code.fs_check_mop
import Slop.RV.Code.inc
import Slop.RV.Code.init_mop
import Slop.RV.Code.main_mop
import Slop.RV.Code.memcpy
import Slop.RV.Code.merkle_check
import Slop.RV.Code.merkle_step_mop
import Slop.RV.Code.mul_mod
import Slop.RV.Code.poly_eval
import Slop.RV.Code.start

/-! Link check for the Mop image: the code the proofs use, by address, is in the image bytes. -/

namespace RV

/-- The code pieces of the Mop image, by increasing address. -/
def layoutMop : List (Nat × List Word) := [
    (0, Code.start),
    (0x38, Code.main_mop),
    (0x1c0, Code.blake2s_compress_mop),
    (0x234, Code.ext4_horner),
    (0x2dc, Code.ext4_mul_add_mop),
    (0x3a0, Code.ext4_poly_mop),
    (0x460, Code.fs_check_mop),
    (0x624, Code.add_mod),
    (0x658, Code.mul_mod),
    (0x694, Code.poly_eval),
    (0x710, Code.merkle_check),
    (0x8cc, Code.merkle_step_mop),
    (0x9ec, Code.combine),
    (0xa34, Code.double),
    (0xa58, Code.inc),
    (0xae4, Code.finish_error),
    (0xafc, Code.finish_success),
    (0xb74, Code.finish_success_extended),
    (0xc20, Code.init_mop),
    (0xca8, Code.memcpy),
    (0x26d8, Code.COEFFS),
    (0x26d8 + 0x190, Code.COEFFS4)]

set_option maxRecDepth 100000 in
theorem linked_mop : linkedFrom ImageMop.bytes.toList 0 layoutMop = true := by decide +kernel

end RV
