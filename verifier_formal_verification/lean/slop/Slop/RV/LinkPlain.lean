import Slop.RV.Link
import Image
import Slop.RV.Code.COEFFS
import Slop.RV.Code.COEFFS4
import Slop.RV.Code.add_mod
import Slop.RV.Code.blake2s_compress
import Slop.RV.Code.combine
import Slop.RV.Code.double
import Slop.RV.Code.ext4_horner
import Slop.RV.Code.ext4_mul_add
import Slop.RV.Code.ext4_poly
import Slop.RV.Code.finish_error
import Slop.RV.Code.finish_success
import Slop.RV.Code.finish_success_extended
import Slop.RV.Code.fs_check
import Slop.RV.Code.inc
import Slop.RV.Code.init
import Slop.RV.Code.main
import Slop.RV.Code.memcpy
import Slop.RV.Code.merkle_check
import Slop.RV.Code.merkle_step
import Slop.RV.Code.mul_mod
import Slop.RV.Code.poly_eval
import Slop.RV.Code.start

/-! Link check for the plain image: the code the proofs use, by address, is in the image bytes. -/

namespace RV

/-- The code pieces of the plain image, by increasing address. -/
def layoutPlain : List (Nat × List Word) := [
    (0, Code.start),
    (0x38, Code.main),
    (0x1c0, Code.blake2s_compress),
    (0x1800, Code.ext4_horner),
    (0x18a8, Code.ext4_mul_add),
    (0x1e8c, Code.ext4_poly),
    (0x20bc, Code.fs_check),
    (0x2280, Code.add_mod),
    (0x22b4, Code.mul_mod),
    (0x22f0, Code.poly_eval),
    (0x236c, Code.merkle_check),
    (0x2528, Code.merkle_step),
    (0x2648, Code.combine),
    (0x2690, Code.double),
    (0x26b4, Code.inc),
    (0x2740, Code.finish_error),
    (0x2758, Code.finish_success),
    (0x27d0, Code.finish_success_extended),
    (0x287c, Code.init),
    (0x2904, Code.memcpy),
    (0x4334, Code.COEFFS),
    (0x4334 + 0x190, Code.COEFFS4)]

set_option maxRecDepth 100000 in
theorem linked_plain : linkedFrom Image.bytes.toList 0 layoutPlain = true := by decide +kernel

end RV
