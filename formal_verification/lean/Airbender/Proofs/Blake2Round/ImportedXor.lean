import Airbender.Review.Circuits.Blake2Round.Tables.Setup
import Airbender.Proofs.Blake2Round.NativeXorRows

namespace Airbender.Blake2Round

/- Mathematical characterizations only; Review contents come from imported data. -/
def plainXorRow (base tag n : Nat) : Vector Nat 6 :=
  let a := n / base
  let b := n % base
  #v[a, b, a ^^^ b, 0, 0, tag]

def carryXorRow (base tag n : Nat) : Vector Nat 6 :=
  let a := n / base % base
  let b := n % base
  #v[a, b, n / (base * base), a ^^^ b, 0, tag]

def combinedXorRow (n : Nat) : Vector Nat 6 :=
  #v[n / 1024, n / 128 % 8, n / 8 % 16, n % 8,
    (n / 1024 ^^^ n / 8 % 16) + 16 * (n / 128 % 8 ^^^ n % 8), 57]

def referenceSetupRow (index : Fin 606208) : Vector Nat 6 :=
  let n := index.val
  if n < xor8DataRegion.offset + xor8DataRegion.length then plainXorRow 256 4 n
  else if n < xor7DataRegion.offset + xor7DataRegion.length then
    plainXorRow 128 19 (n - xor7DataRegion.offset)
  else if n < xor9DataRegion.offset + xor9DataRegion.length then
    plainXorRow 512 20 (n - xor9DataRegion.offset)
  else if n < xor8CarryDataRegion.offset + xor8CarryDataRegion.length then
    carryXorRow 256 55 (n - xor8CarryDataRegion.offset)
  else if n < xor7CarryDataRegion.offset + xor7CarryDataRegion.length then
    carryXorRow 128 56 (n - xor7CarryDataRegion.offset)
  else combinedXorRow (n - xor4x3DataRegion.offset)

namespace Proofs
open Airbender.Setup
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

/-- All physical imported rows have the checked native mathematical meaning. -/
theorem setup_row_characterization (index : Fin 606208) :
    setupRow index = referenceSetupRow index := by
  have bound := index.isLt
  unfold setupRow referenceSetupRow
  dsimp only [xor8DataRegion, xor7DataRegion, xor9DataRegion,
    xor8CarryDataRegion, xor7CarryDataRegion, xor4x3DataRegion]
  split_ifs
  all_goals first
    | exact plain_region_reference 0 _ (by change _ < 65536; omega)
    | exact plain_region_reference 1 _ (by change _ < 16384; omega)
    | exact plain_region_reference 2 _ (by change _ < 262144; omega)
    | exact carry_region_reference 0 _ (by change _ < 196608; omega)
    | exact carry_region_reference 1 _ (by change _ < 49152; omega)
    | exact combined_region_reference _ (by omega)

/-- Ordinary native XOR regions agree with the existing G table schema. -/
theorem xor_region_projection (kind : Fin 3) (n : Nat)
    (hn : n < (xorData ⟨kind.val, by omega⟩).length) :
    xorRegionRow ⟨kind.val, by omega⟩ n =
      let row := Blake2G.xorRegionRow (#v[(0 : Fin 5), 3, 4][kind]) n
      #v[row[0], row[1], row[2], 0, 0, row[8]] := by
  have bound : n < (Blake2G.xorData (#v[(0 : Fin 5), 3, 4][kind])).length := by
    fin_cases kind <;> exact hn
  rw [plain_region_reference kind n hn, Blake2G.Proofs.xor_region_reference _ _ bound]
  fin_cases kind <;> rfl

end Proofs
end Airbender.Blake2Round
