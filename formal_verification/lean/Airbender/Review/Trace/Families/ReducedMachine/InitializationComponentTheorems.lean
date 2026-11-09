import Airbender.Proofs.ReducedMachine.NativeInitializationComponent

namespace Airbender.NativeInitializationComponent
/-- Derived logical scalar queries, observed native initialization endpoints,
    padding and all indexed repeated-window components on the same complete
    inactive main/caller/decoder/scalar source. Global acceptance, verifier
    counters, nonempty workers and physical refinement remain separate. -/
theorem native_inactive_initialization_component : ∃ w, Fixture w :=
  NativeInitializationComponentProofs.fixture
end Airbender.NativeInitializationComponent
