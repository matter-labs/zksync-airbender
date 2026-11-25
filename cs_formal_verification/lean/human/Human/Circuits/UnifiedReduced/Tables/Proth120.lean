module
public import Human.Circuits.UnifiedReduced.Tables.SetupRV
public import Human.Helpers.Core.Proth120

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120

/-- The membership model enumerates the shared 1,048,961 fixed rows, then the 131,072 words in
    the wrap’s 512 KiB ROM (`common_constants/src/rom.rs`). The decoder has its own lookup. -/
def tableWith (words : Nat → BitVec 32) : Table (ZMod proth120Modulus) (fields 10) where
  name := "Airbender.UnifiedReduced.Proth120"
  Contains _ query := ∃ i : Fin 1180033, query =
    (Setup.rowWith words ⟨i, lt_of_lt_of_le i.isLt (by decide)⟩).map (fun (n : Nat) => (n : ZMod proth120Modulus))

end Airbender.UnifiedReduced.Proth120
