module
public import Human.Helpers.Context.Model
public import Human.Helpers.Core.Word

@[expose] public section

namespace Airbender.Trace
open Arithmetic

/-- Decode the injective native value code without reducing either limb. -/
def MemoryToken.word (token : MemoryToken p) : Word :=
  ⟨(Nat.unpair token.value).1, (Nat.unpair token.value).2⟩

end Airbender.Trace
