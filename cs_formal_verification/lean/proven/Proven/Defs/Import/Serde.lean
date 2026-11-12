module
public import Human.Import.BabyBear
public import Human.Import.JsonGrammar
public import Human.Import.Serde

/-! Definitions only the proofs use, moved from `human/Human/Import/Serde.lean` (no claim states them). -/

@[expose] public section
namespace Airbender
open Serde (encode)
instance [Serde α] : Serde (List α) := ⟨fun l => .arr (l.map encode)⟩
end Airbender
