import Slop.Arithmetic.ByteAssembly
namespace Airbender.Arithmetic
set_option warningAsError true
set_option maxHeartbeats 1600000
theorem rotate_left_one_of_limbs {a b c d : Nat} (ha : a < 65536) (hb : b < 65536)
    (hc : c < 65536) :
    rotLeft64 (a + 65536 * (b + 65536 * (c + 65536 * d))) (1 : Fin 64) =
      (2*a % 65536 + d / 32768) + 65536 * ((2*b % 65536 + a / 32768) +
        65536 * ((2*c % 65536 + b / 32768) + 65536 * (2*d % 65536 + c / 32768))) := by
  change ((a + 65536 * (b + 65536 * (c + 65536 * d))) % 9223372036854775808) * 2 +
    (a + 65536 * (b + 65536 * (c + 65536 * d))) / 9223372036854775808 = _
  omega
end Airbender.Arithmetic
