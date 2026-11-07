import Airbender.Proofs.FullUnsigned.NativeSoundness
import Airbender.Proofs.Keccak.SplitSetupTransport
import Airbender.Review.Compiler.SetupSource

namespace Airbender.Compiler.MachineTargets.Proofs
open Trace
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option Elab.async false

/-- Parsed physical-row membership transfers the original setup premise to
native lookup containment. The supplied certificate keeps its full source
and physical-row obligations. -/
theorem fixed_setup_lookup_of_source_rows
    {source : String} {table target : Table F (fields width)}
    (certificate : FixedSetupRows source target) (fixed : FixedSetup source table)
    {row : Vector F width} (member : table.toRaw.Soundness #[] row) :
    target.toRaw.Contains #[] row := by
  obtain ⟨artifact, parsed, width, rows⟩ := fixed
  exact certificate artifact parsed width row ((rows row).mp member)

/-- The complete full target follows from three physical source certificates.
All native equations, both cache modes and the original initialization adapter
are covered by the transport proof. The three certificates remain open. -/
theorem unrolled_full_soundness_of_source_rows
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (parity : ∀ [Fact babyBearModulus.Prime],
      FixedSetupRows (include_str "../../../artifacts/setup/keccak-column-parity.json")
        Keccak.Split.Native.Proofs.fixedSetup.columnParity)
    (theta : ∀ [Fact babyBearModulus.Prime],
      FixedSetupRows (include_str "../../../artifacts/setup/keccak-theta-rho.json")
        Keccak.Split.Native.Proofs.fixedSetup.thetaRho)
    (chi : ∀ [Fact babyBearModulus.Prime],
      FixedSetupRows (include_str "../../../artifacts/setup/keccak-chi5.json")
        Keccak.Split.Native.Proofs.fixedSetup.chi5) : UnrolledFullUnsigned := by
  apply unrolled_full_soundness_of_setup_interpretation
  intro prime data paritySetup thetaSetup chiSetup equations
  have refinement : Keccak.Split.Native.Proofs.SetupRefinement data.setup
      Keccak.Split.Native.Proofs.fixedSetup := {
    columnParity := fun _ member => fixed_setup_lookup_of_source_rows parity paritySetup member
    thetaRho := fun _ member => fixed_setup_lookup_of_source_rows theta thetaSetup member
    chi5 := fun _ member => fixed_setup_lookup_of_source_rows chi chiSetup member }
  exact ⟨Keccak.Split.Native.Proofs.control_of_fixed_setup_refinement refinement,
    Keccak.Split.Native.Proofs.equations_of_setup_refinement refinement equations⟩

end Airbender.Compiler.MachineTargets.Proofs
