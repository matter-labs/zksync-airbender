import Airbender.Proofs.Blake2Round.NativeXorRowReads
import Airbender.Proofs.Blake2Round.NativeXorKeys
import Airbender.Proofs.Blake2Round.Carry8OutputCertificate
import Airbender.Proofs.Blake2Round.Carry7OutputCertificate

namespace Airbender.Blake2Round.Proofs
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

private theorem carry_output_covered (kind : Fin 2) :
    (((xorData (carryKind kind)).columns[3]).blocks.toList.map Block.length).sum =
      (xorData (carryKind kind)).length := by
  fin_cases kind
  all_goals dsimp only [carryKind, xorData, xor8CarryData, xor7CarryData,
    Vector.getElem_mk, Fin.getElem_fin, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  all_goals simp (config := { maxSteps := 1000000 }) [Block.length]

private theorem carry_output_get (kind : Fin 2) (n : Nat)
    (hn : n < (xorData (carryKind kind)).length) :
    (xorData (carryKind kind)).columns[3].get? n =
      some (n / carryBase kind % carryBase kind ^^^ n % carryBase kind) := by
  have checked : checkBlocks
      (fun n => n / carryBase kind % carryBase kind ^^^ n % carryBase kind) 0
      (xorData (carryKind kind)).columns[3].blocks.toList = true := by
    fin_cases kind
    · exact carry8_output_checks
    · exact carry7_output_checks
  have get := checkBlocks_sound _ _ 0 n checked
    (by simpa only [carry_output_covered kind] using hn)
  simpa only [Column.get?, Nat.zero_add] using get

/-- Exact imported carry-aware rows, including all three carries and padding. -/
theorem carry_region_reference (kind : Fin 2) (n : Nat)
    (hn : n < (xorData (carryKind kind)).length) :
    xorRegionRow (carryKind kind) n =
      let a := n / carryBase kind % carryBase kind;
      let b := n % carryBase kind;
      #v[a, b, n / (carryBase kind * carryBase kind), a ^^^ b, 0, #v[55, 56][kind]] := by
  have first := carry_first_get kind n hn
  have second := carry_second_get kind n hn
  have carry := carry_value_get kind n hn
  have output := carry_output_get kind n hn
  have padding := carry_padding_get kind n hn
  have tag := native_tag_get (carryKind kind) n hn
  have tag_value : (#v[4, 19, 20, 55, 56, 57][carryKind kind] : Nat) = #v[55, 56][kind] := by
    fin_cases kind <;> rfl
  rw [tag_value] at tag
  apply row_from_entries
  intro j hj
  interval_cases j
  · exact first
  · exact second
  · exact carry
  · exact output
  · exact padding
  · exact tag

end Airbender.Blake2Round.Proofs
