import Airbender.Review.Circuits.ShiftBinop.ShiftModel
import Airbender.Proofs.Arithmetic.Word

namespace Airbender.ShiftBinop.Proofs
open Arithmetic
set_option autoImplicit false

def limbPieces (kind : ShiftKind) (lo hi amount : Nat) : Vector (BitVec 32) 3 :=
  match kind with
  | .sll => #v[(BitVec.ofNat 32 lo) <<< amount,
      (BitVec.ofNat 32 (hi * 65536)) <<< amount,0]
  | .srl => #v[(BitVec.ofNat 32 lo) >>> amount,
      (BitVec.ofNat 32 (hi * 65536)) >>> amount,0]
  | .sra => #v[if hi < 32768 then 0 else (BitVec.allOnes 32) <<< (32 - amount),
      (BitVec.ofNat 32 lo) >>> amount,(BitVec.ofNat 32 (hi * 65536)) >>> amount]

def piecesWord (pieces : Vector (BitVec 32) 3) : Word :=
  ⟨(Word.ofBitVec pieces[0]).lo + (Word.ofBitVec pieces[1]).lo + (Word.ofBitVec pieces[2]).lo,
   (Word.ofBitVec pieces[0]).hi + (Word.ofBitVec pieces[1]).hi + (Word.ofBitVec pieces[2]).hi⟩

end Airbender.ShiftBinop.Proofs
