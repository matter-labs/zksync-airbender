import Airbender.Proofs.FullUnsigned.SetupInterpretation
import Airbender.Proofs.Keccak.SplitTaggedSetupTransport

namespace Airbender.Compiler.MachineTargets.Proofs
set_option warningAsError true
set_option Elab.async false

/-- The original setup premise and actual query tag supply guarded transport. -/
theorem fixed_setup_lookup_of_guarded_source_rows
    {source : String} {table target : Table F (fields width)} {queried : Vector F width → Prop}
    (certificate : GuardedSetupRows source target queried) (fixed : FixedSetup source table)
    {row : Vector F width} (member : table.toRaw.Soundness #[] row) (query : queried row) :
    target.toRaw.Contains #[] row := by
  obtain ⟨artifact, parsed, width, rows⟩ := fixed
  exact certificate artifact parsed width row ((rows row).mp member) query

/-- Chi5 needs its real query rows. Its physical zero padding cannot match
any of the constant native query tags. The original target stays unchanged. -/
theorem unrolled_full_soundness_of_guarded_source_rows
    [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (parity : ∀ [Fact babyBearModulus.Prime],
      FixedSetupRows (include_str "../../../artifacts/setup/keccak-column-parity.json")
        Keccak.Split.Native.Proofs.fixedSetup.columnParity)
    (theta : ∀ [Fact babyBearModulus.Prime],
      FixedSetupRows (include_str "../../../artifacts/setup/keccak-theta-rho.json")
        Keccak.Split.Native.Proofs.fixedSetup.thetaRho)
    (chi : ∀ [Fact babyBearModulus.Prime],
      GuardedSetupRows (include_str "../../../artifacts/setup/keccak-chi5.json")
        Keccak.Split.Native.Proofs.fixedSetup.chi5 (fun row => row[10] = 65 ∨ row[10] = 66)) :
    UnrolledFullUnsigned := by
  apply unrolled_full_soundness_of_setup_interpretation
  intro prime data paritySetup thetaSetup chiSetup equations
  have refinement : Keccak.Split.Native.Proofs.TaggedSetupRefinement data.setup
      Keccak.Split.Native.Proofs.fixedSetup := {
    columnParity := fun _ member => fixed_setup_lookup_of_source_rows parity paritySetup member
    thetaRho := fun _ member => fixed_setup_lookup_of_source_rows theta thetaSetup member
    chi5 := fun _ member tag => fixed_setup_lookup_of_guarded_source_rows chi chiSetup member tag }
  exact ⟨Keccak.Split.Native.Proofs.control_of_fixed_tagged_setup_refinement refinement,
    Keccak.Split.Native.Proofs.equations_of_tagged_setup_refinement refinement equations⟩

end Airbender.Compiler.MachineTargets.Proofs
