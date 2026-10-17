import Airbender.Review.Helpers.Context.Model
import Airbender.Review.Helpers.Core.Word

namespace Airbender.Trace
open Arithmetic

/-- Decode the injective native value code without reducing either limb. -/
def MemoryToken.word (token : MemoryToken p) : Word :=
  ⟨(Nat.unpair token.value).1, (Nat.unpair token.value).2⟩

end Airbender.Trace
