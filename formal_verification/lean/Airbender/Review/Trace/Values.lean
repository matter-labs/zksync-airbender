import Airbender.Review.Trace.Model
import Airbender.Review.Word

namespace Airbender.Trace
open Arithmetic

/-- Decode the injective native value code without reducing either limb. -/
def MemoryToken.word (token : MemoryToken p) : Word :=
  ⟨(Nat.unpair token.value).1, (Nat.unpair token.value).2⟩

/-- Conditions on the public initial image and program table. Native read and
    write bounds are conclusions, not fields of this boundary. -/
structure ValueBoundary [Fact p.Prime] (trace : Data p) : Prop where
  initial : ∀ token ∈ trace.initialMemory, token.word.Bounded
  disabledROM : ∀ row, trace.rom.Contains #[] row → row[8] = 0 →
    row[1] = 0 ∧ row[2] = 0
  rom : ∀ row, trace.rom.Contains #[] row →
    row[1].val < limbBase ∧ row[2].val < limbBase

end Airbender.Trace
