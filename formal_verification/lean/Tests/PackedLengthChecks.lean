import Airbender.Proofs.Tables.PackedLengthChecks

namespace Tests.PackedLengthChecks
open Airbender.Setup Airbender.Setup.Proofs PackedWordBlocks
set_option warningAsError true

def requests : List Airbender.Verification.PackedLengthChecks.Request := [
  ⟨[.affine 5 45 2, .dense 3 197121, .periodic 4 (-1) 3 197121], 20⟩,
  ⟨[], 0⟩]

theorem checked : Airbender.Verification.PackedLengthChecks.check requests = true := by decide +kernel

theorem original (index : Fin requests.length) :
    (((requests.get index).blocks.map (Code.decode 65536)).map Block.length).sum =
      (requests.get index).expected :=
  Airbender.Verification.PackedLengthChecks.check_sound_at requests checked index

theorem wrong_total_rejected :
    Airbender.Verification.PackedLengthChecks.check
      [⟨[.affine 5 45 2, .dense 3 197121, .periodic 4 (-1) 3 197121], 21⟩] = false := by decide +kernel

theorem changed_count_rejected :
    Airbender.Verification.PackedLengthChecks.check
      [⟨[.affine 5 45 2, .dense 3 197121, .periodic 5 (-1) 3 197121], 20⟩] = false := by decide +kernel

end Tests.PackedLengthChecks
