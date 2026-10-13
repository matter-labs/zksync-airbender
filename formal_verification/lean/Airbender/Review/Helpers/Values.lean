import Airbender.Review.Helpers.Model
import Airbender.Review.Helpers.Word

namespace Airbender.Trace
open Arithmetic

/-- Decode the injective native value code without reducing either limb. -/
def MemoryToken.word (token : MemoryToken p) : Word :=
  ⟨(Nat.unpair token.value).1, (Nat.unpair token.value).2⟩

/-- Starting value and modeled-ROM conditions used by restricted trace range
    lemmas. Public Sail image/table construction discharges this record in the
    integrated claim. Read, write and terminal bounds then follow from history. -/
structure ValueBoundary [Fact p.Prime] (trace : Data p) : Prop where
  /-- Every public seed value has two bounded 16-bit limbs. -/
  initial : ∀ token ∈ trace.initialMemory, token.word.Bounded
  /-- A disabled word-ROM query returns zero in both value columns. -/
  disabledROM : ∀ row, trace.rom.Contains #[] row → row[8] = 0 →
    row[1] = 0 ∧ row[2] = 0
  /-- Every word-ROM table result has bounded 16-bit value limbs. -/
  rom : ∀ row, trace.rom.Contains #[] row →
    row[1].val < limbBase ∧ row[2].val < limbBase

end Airbender.Trace
