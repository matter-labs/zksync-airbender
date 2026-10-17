import Airbender.Review.Helpers.Tables.Lookups
import Clean.Utils.Field

namespace Airbender.Verification

/-- Native 32-bit contribution of one source byte, as in Rust's shift table. -/
def shiftByteContribution (position byte amount operation : Nat) : BitVec 32 :=
  let input := (BitVec.ofNat 32 byte).shiftLeft (8 * position)
  match operation with
  | 1 => input.shiftLeft amount
  | 2 => input.ushiftRight amount
  | 3 => input.sshiftRight amount
  | 5 => if amount = 0 then (BitVec.ofNat 32 byte).shiftLeft (8 * (3 - position)) else 0
  | _ => 0

def binaryByteRow (tag index : Nat) : Vector Nat 10 :=
  let (a, b) := ByteUtils.splitTwoBytes ⟨index % 65536, Nat.mod_lt _ (by decide)⟩
  let output := if tag = 4 then (a ^^^ b).val else
    if tag = 6 then a.val ||| b.val else a.val &&& b.val
  #v[a.val, b.val, output, 0, 0, 0, 0, 0, 0, tag]

/-- All seven setup tables, with their actual tag and zero-padded columns.
    The combined row count and offsets are checked during JSON import. -/
def referenceShiftNatRow (n : Nat) : Vector Nat 10 :=
  if n = 0 then #v[0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  else if n < 257 then
    let byte := n - 1
    #v[byte, if byte < 128 then 0 else 255, 0, 0, 0, 0, 0, 0, 0, 3]
  else if n < 65793 then binaryByteRow 4 (n - 257)
  else if n < 131329 then binaryByteRow 6 (n - 65793)
  else if n < 196865 then binaryByteRow 7 (n - 131329)
  else if n < 262401 then
    let (a, b) := ByteUtils.splitTwoBytes ⟨(n - 196865) % 65536, Nat.mod_lt _ (by decide)⟩
    #v[a.val, b.val, a.val % 32, 0, 0, 0, 0, 0, 0, 8]
  else
    let key := n - 262401
    let position := key / 65536
    let byte := key / 256 % 256
    let amount := key / 8 % 32
    let operation := key % 8
    let output := (shiftByteContribution position byte amount operation).toNat
    #v[position, byte, amount, operation, output % 256, output / 256 % 256,
      output / 65536 % 256, output / 16777216 % 256, 0, 9]


def referenceShiftBinopRow (index : Fin 524545) : Vector Nat 10 :=
  referenceShiftNatRow index.val

end Airbender.Verification
