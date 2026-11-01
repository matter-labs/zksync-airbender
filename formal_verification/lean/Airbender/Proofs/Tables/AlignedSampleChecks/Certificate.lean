import Airbender.Proofs.Tables.AlignedSampleChecks.Bindings

namespace Airbender.Verification.AlignedSampleChecks
open Airbender Airbender.Compiler PackedSetupEquality PackedSetupSamples
set_option warningAsError true
set_option Elab.async false

theorem conditionalChecked : PackedSetupSamples.check conditionalRequests = true := by decide +kernel

theorem conditionalFact : Fact conditional :=
  PackedSetupSamples.check_sound_at conditionalRequests conditionalChecked ⟨0, by decide +kernel⟩

theorem positionChecked : PackedSetupSamples.check positionRequests = true := by decide +kernel

theorem positionFact : Fact position :=
  PackedSetupSamples.check_sound_at positionRequests positionChecked ⟨0, by decide +kernel⟩

end Airbender.Verification.AlignedSampleChecks
