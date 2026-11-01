import Airbender.Proofs.GKRProtocol.PackedSetupLengths

namespace Tests.PackedSetupLengths
open Airbender.Compiler.PackedSetupEquality Airbender.Compiler.PackedSetupLengths
set_option warningAsError true

def requests : List Request := [
  ⟨[.affine 3 99 (-1), .periodic 2 (-3) (.range 4)], 11⟩,
  ⟨[.dense (.packedBytes 6 12345), .dense (.linearRuns 5 0 256 1)], 11⟩,
  ⟨[], 0⟩]

theorem checked : check requests = true := by decide +kernel

theorem original_rows :
    ((((requests.get ⟨0, by decide +kernel⟩).blocks).map BlockCode.decode).map
      Airbender.Setup.Block.length).sum = 11 :=
  check_sound_at requests checked ⟨0, by decide +kernel⟩

theorem changed_count_rejected : check [⟨[.affine 3 99 (-1)], 2⟩] = false := by decide +kernel

end Tests.PackedSetupLengths
