module
public import Human.Helpers.Decoder.Program
public import Proven.Trace.InitialImage
public import Proven.Trace.DecoderBits
public import Proven.KernelRfl

@[expose] public section
namespace Airbender.Trace.Proofs
open Arithmetic

theorem word_of_pc_query {p : Nat} (hp : limbBase < p) {lo hi : ZMod p} {pc : BitVec 32}
    (low : lo = ((Word.ofBitVec pc).lo : ZMod p))
    (high : hi = ((Word.ofBitVec pc).hi : ZMod p)) :
    (⟨lo.val, hi.val⟩ : Word) = Word.ofBitVec pc := by
  have bound := Word.ofBitVec_bound pc
  rw [low, high, ZMod.val_natCast_of_lt (lt_trans bound.1 hp),
    ZMod.val_natCast_of_lt (lt_trans bound.2 hp)]

end Airbender.Trace.Proofs
