import Airbender.Review.Trace.Model
import Airbender.Review.UnifiedReduced.Artifact

namespace Airbender.Trace

/-- The unified artifact is one circuit with several operation selectors.
    This registry lets it reuse native state/memory matching and clock proofs;
    it does not identify those selectors with instructions or assume their results. -/
inductive UnifiedFamily where
  | machine
  deriving DecidableEq

instance : CircuitLayout UnifiedFamily where
  columns _ := UnifiedReduced.importedConstraintsTraceColumns
  ports _ := UnifiedReduced.importedConstraintsMemoryPorts
  decoderColumns _ := UnifiedReduced.importedConstraintsDecoderColumns
  Setup p _ := Table (ZMod p) (fields 10)
  constraints _ setup := UnifiedReduced.clockConstraints setup

/-- Unified rows with their actual imported ports, PC/clocks and pooled setup.
    `Accepted` checks the richer equations and logical state/memory permutations.
    Public initialization and instruction semantics are separate from these data. -/
abbrev UnifiedTrace (p : Nat) [Fact p.Prime] := Data p UnifiedFamily

end Airbender.Trace
