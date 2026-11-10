import Airbender.Proofs.Blake2Round.NativeXorRowReads
import Airbender.Proofs.Blake2Round.NativeCombinedXorKeys
import Airbender.Proofs.Blake2Round.NativeXorPadding
import Airbender.Proofs.Blake2Round.CombinedOutputCertificate

namespace Airbender.Blake2Round.Proofs
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

private theorem combined_output_covered :
    (xor4x3Data.columns[4].blocks.toList.map Block.length).sum = 16384 := by
  dsimp only [xor4x3Data, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  simp (config := { maxSteps := 1000000 }) [Block.length]

/-- Exact native combined four-bit and three-bit row, proved from imported data. -/
theorem combined_region_reference (n : Nat) (hn : n < 16384) :
    xorRegionRow 5 n =
      #v[n / 1024, n / 128 % 8, n / 8 % 16, n % 8,
        (n / 1024 ^^^ n / 8 % 16) + 16 * (n / 128 % 8 ^^^ n % 8), 57] := by
  obtain ⟨first, second, third, fourth⟩ := combined_keys_get n hn
  have output := checkBlocks_sound _ _ 0 n combined_output_checks
    (by simpa only [combined_output_covered] using hn)
  simp only [Nat.zero_add] at output
  change xor4x3Data.columns[4].get? n = some
    ((n / 1024 ^^^ n / 8 % 16) + 16 * (n / 128 % 8 ^^^ n % 8)) at output
  have tag := native_tag_get 5 n hn
  apply row_from_entries
  intro j hj
  interval_cases j
  · exact first
  · exact second
  · exact third
  · exact fourth
  · exact output
  · exact tag

end Airbender.Blake2Round.Proofs
