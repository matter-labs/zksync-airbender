import Airbender.Review.Circuits.MulDiv.Decoder

namespace Tests.MulDivInitializedFixture
open Airbender Arithmetic Trace MulDiv

def word (op : Operation) (discarded : Bool) : BitVec 32 :=
  BitVec.ofNat 32 (0x02208033 + 4096 * op.funct3 + if discarded then 0 else 384)
def instruction (op : Operation) (discarded : Bool) : SailRV32.instruction :=
  let rd := SailRV32.regidx.Regidx (if discarded then 0 else 3)
  match op with
  | .mul => .MUL (.Regidx 2,.Regidx 1,rd,⟨.Low,.Signed,.Signed⟩)
  | .mulhu => .MUL (.Regidx 2,.Regidx 1,rd,⟨.High,.Unsigned,.Unsigned⟩)
  | .divu => .DIV (.Regidx 2,.Regidx 1,rd,true)
  | .remu => .REM (.Regidx 2,.Regidx 1,rd,true)

def entry (op : Operation) (discarded : Bool) : MulDiv.ProgramEntry :=
  ⟨0,word op discarded,instruction op discarded,
    ⟨op,1,2,if discarded then 0 else 3,⟨0,0⟩,op.nativeMask,op.funct3⟩⟩
def setup (op : Operation) (discarded : Bool) : SparseDecoderSetup Operation :=
  ⟨[some (entry op discarded),none],1048574⟩

theorem entry_query (op : Operation) (discarded : Bool) :
    (entry op discarded).query (p := mersenne31Modulus) =
      #v[0,0,1,2,if discarded then 0 else 3,if discarded then 1 else 0,
        0,0,(op.funct3 : ZMod mersenne31Modulus),(op.nativeMask : ZMod mersenne31Modulus)] := by cases op <;> cases discarded <;> decide +kernel

end Tests.MulDivInitializedFixture
