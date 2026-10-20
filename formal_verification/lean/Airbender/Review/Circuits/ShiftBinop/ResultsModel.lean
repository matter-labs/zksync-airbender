import Airbender.Review.Circuits.ShiftBinop.ShiftModel

namespace Airbender.ShiftBinop
open Arithmetic
set_option autoImplicit false

/-- RV32 shift references; original Sail instruction execution is separate. -/
def ShiftKind.result (kind : ShiftKind) (x : BitVec 32) (amount : Nat) : BitVec 32 :=
  match kind with
  | .sll => x <<< amount
  | .srl => x >>> amount
  | .sra => x.sshiftRight amount

/-- Numerical references for the six ordinary native operations. Immediate
    selection and original SRAI funct7 truncation are derived from decoding. -/
def Operation.result (op : Operation) (left right : Word) : BitVec 32 :=
  let amount := (right.toBitVec.extractLsb' 0 5).toNat
  match op with
  | .sll => ShiftKind.result .sll left.toBitVec amount
  | .srl => ShiftKind.result .srl left.toBitVec amount
  | .sra => ShiftKind.result .sra left.toBitVec amount
  | .xor => left.toBitVec ^^^ right.toBitVec
  | .or => left.toBitVec ||| right.toBitVec
  | .and => left.toBitVec &&& right.toBitVec

end Airbender.ShiftBinop
