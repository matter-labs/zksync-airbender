import Airbender.Proofs.ReducedMachine.NativeScalarPairs

namespace Airbender.NativeScalarPairs
/-- All five actual ordinary scalar pairs and adjacent initialization ordering
    share the complete inactive MAIN/caller/decoder component for every scalar
    challenge, retaining poles. Scalar table/sum/reserved normalization, global
    source/worker acceptance and physical refinement remain separate. -/
theorem native_inactive_scalar_pairs : ∃ w, Fixture w :=
  NativeScalarPairsProofs.fixture
end Airbender.NativeScalarPairs
