module
public import Human.Helpers.Memory.InitialImage
public import Human.Helpers.Context.Model

@[expose] public section

namespace Airbender.Trace
open Arithmetic

variable {Kind : Type} [CircuitLayout Kind]

/-- Interpret Clean's injective value code as its canonical RV32 word. -/
def memoryWord (code : Nat) : BitVec 32 :=
  (Word.mk (Nat.unpair code).1 (Nat.unpair code).2).toBitVec

end Airbender.Trace
