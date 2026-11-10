module
public import Human.Import.TranscribeCommand
public import Human.Import.Exec.Emit
public import Human.Import.Operations
public import Human.Helpers.Core.Word
public import Human.Circuits.AddSub.Artifact

/-! Definitions only the proofs use, moved from `human/Human/Circuits/AddSub/Artifact.lean` (no claim states them). -/

@[expose] public section
namespace Airbender.AddSub
open Arithmetic
/-- PC limbs in the imported artifact. Initial bounds come from the state interface;
    final bounds are enforced by the imported lookups. -/
structure PCMapping {p : Nat} (initial final : Word) (w : Nat → ZMod p) : Prop where
  initialLo : w 0 = (initial.lo : ZMod p)
  initialHi : w 1 = (initial.hi : ZMod p)
  finalLo : final.lo = (w 19).val
  finalHi : final.hi = (w 20).val
end Airbender.AddSub
