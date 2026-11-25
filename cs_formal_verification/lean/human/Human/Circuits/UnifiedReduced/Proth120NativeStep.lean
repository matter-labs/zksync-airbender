module
public import Human.Compiler.Proth120Native
public import Human.Circuits.UnifiedReduced.Proth120Execution

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open Trace

/-- An active cached wrap row with matched native lookups takes one RV step from its public ROM.
    The memory permutation supplies the row context. -/
def NativeStepSoundnessClaim : Prop :=
  ∀ cells epoch before after physical w
    (tables : PublicLookupRows (tableWith (ROM.wordsRV before)) (Decoded before)),
    RowContext cells epoch w before after → NativeArithmetic physical w →
    NativeLookupsMatched tables.generic physical → StepResult w before after

def NativeStepSoundnessSatisfiableClaim : Prop :=
  ∃ (cells : List Cell) (epoch : Nat) (before after : RV.State) (physical : GKRAddress → F) (w : Nat → F)
    (tables : PublicLookupRows (tableWith (ROM.wordsRV before)) (Decoded before)),
    RowContext cells epoch w before after ∧ NativeArithmetic physical w ∧ NativeLookupsMatched tables.generic physical

end Airbender.UnifiedReduced.Proth120
