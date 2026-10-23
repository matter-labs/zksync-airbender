import Airbender.Review.Trace.UnifiedReduced.Paths.GapFrames

namespace Airbender.UnifiedReduced.Caller
open Trace Arithmetic Reference.RiscV.Sail

/-- A G index0 occurrence seeds arbitrary native block pointers. Imported
    address uniqueness derives their separation. Later occurrences retain
    those pointers through public code frames, beginning after the seed call.
    The seed call itself is a separate constructor, with no reversed interval.
    No pointer word, native read or desired frame equality is supplied. -/
inductive PathGPointerSeed [Fact p.Prime] (data : RequestTrace p)
    (program : List UnifiedReduced.ProgramEntry) : Nat → Prop where
  | atSeed {start : Nat} (reduced : Bool)
      (call : PathCallerPreparation data (start + 4) .blakeG)
      (control : PathControllerDataflow data program start 12
        (Blake2G.controlAt reduced 0).toBitVec) :
      PathGPointerSeed data program start
  | afterSeed {start target : Nat} (reduced : Bool)
      (call : PathCallerPreparation data (start + 4) .blakeG)
      (control : PathControllerDataflow data program start 12
        (Blake2G.controlAt reduced 0).toBitVec)
      (stateFrames : PathRegisterGapFrames data program (start + 4) target 10)
      (messageFrames : PathRegisterGapFrames data program (start + 4) target 11) :
      PathGPointerSeed data program target

end Airbender.UnifiedReduced.Caller
