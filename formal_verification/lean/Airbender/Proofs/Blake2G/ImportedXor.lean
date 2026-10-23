import Airbender.Proofs.Blake2G.ImportedXorColumns
import Airbender.Review.Circuits.Blake2G.Tables.Setup
import Airbender.Proofs.Blake2G.XorCertificate
import Mathlib.Tactic.FinCases
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.IntervalCases

namespace Airbender.Blake2G

/- Mathematical reference only; actual table definitions import their data. -/
def xorRow (width tag index : Nat) : Vector Nat 9 :=
  let a := index / 2 ^ width
  let b := index % 2 ^ width
  #v[a, b, a ^^^ b, 0, 0, 0, 0, 0, tag]

def referenceSetupRow (control : Fin 512 → Vector Nat 7) (index : Fin 344896) : Vector Nat 9 :=
  let n := index.val
  if n < 65536 then xorRow 8 4 n
  else if n < 65600 then xorRow 3 17 (n - 65536)
  else if n < 65856 then xorRow 4 18 (n - 65600)
  else if n < 82240 then xorRow 7 19 (n - 65856)
  else if h : n < 344384 then xorRow 9 20 (n - 82240)
  else
    let outputs := control ⟨n - 344384, by have bound := index.isLt; dsimp [n] at *; omega⟩
    #v[n - 344384, outputs[0], outputs[1], outputs[2], outputs[3], outputs[4],
      outputs[5], outputs[6], 28]

namespace Proofs
open Airbender.Setup Airbender.Setup.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

open XorColumns

/-- All five actual native regions have the exact bounded XOR row, including
    every physical padding and discriminator column. -/
theorem xor_region_reference (kind : Fin 5) (n : Nat) (hn : n < (xorData kind).length) :
    xorRegionRow kind n = xorRow (#v[8, 3, 4, 7, 9][kind]) (#v[4, 17, 18, 19, 20][kind]) n := by
  apply Vector.ext
  intro j hj
  have first := first_get kind n hn
  have second := second_get kind n hn
  have output := output_get kind n hn
  have tag := tag_get kind n hn
  interval_cases j
  all_goals simp only [xorRegionRow, Vector.getElem_map, xorRow, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  · simp only [chunkSize, first, Option.getD_some]
  · simp only [chunkSize, second, Option.getD_some]
  · simp only [chunkSize, output, Option.getD_some]
  · have zero : (xorData kind).columns[3].get? n = some 0 := padding_get kind 0 n hn
    simp only [zero, Option.getD_some]
  · have zero : (xorData kind).columns[4].get? n = some 0 := padding_get kind 1 n hn
    simp only [zero, Option.getD_some]
  · have zero : (xorData kind).columns[5].get? n = some 0 := padding_get kind 2 n hn
    simp only [zero, Option.getD_some]
  · have zero : (xorData kind).columns[6].get? n = some 0 := padding_get kind 3 n hn
    simp only [zero, Option.getD_some]
  · have zero : (xorData kind).columns[7].get? n = some 0 := padding_get kind 4 n hn
    simp only [zero, Option.getD_some]
  · simp only [tag, Option.getD_some, chunkTag]

/-- Native imported fixed rows recover the former mathematical characterization;
    the supplied controller remains arbitrary. -/
theorem setup_row_characterization (control : Fin 512 → Vector Nat 7) (index : Fin 344896) :
    setupRow control index = referenceSetupRow control index := by
  have bound := index.isLt
  unfold setupRow referenceSetupRow
  dsimp only [xor8DataRegion, xor3DataRegion, xor4DataRegion, xor7DataRegion,
    xor9DataRegion, controllerDataRegion]
  split_ifs
  all_goals first
    | exact xor_region_reference _ _ (by change _ < 65536; omega)
    | exact xor_region_reference _ _ (by change _ < 64; omega)
    | exact xor_region_reference _ _ (by change _ < 256; omega)
    | exact xor_region_reference _ _ (by change _ < 16384; omega)
    | exact xor_region_reference _ _ (by change _ < 262144; omega)
    | rfl

/-- Raw imported canonical values and their signed circuit-style lift denote
    the same rows in the native field. Generic-field XOR proofs are unchanged. -/
theorem xor_region_native_cast (kind : Fin 5) (index : Fin (xorData kind).length) :
    (xorRegionRow kind index.val).map (fun n : Nat => (n : ZMod babyBearModulus)) =
      ((xorData kind).row index).map (fun n : Int => (n : ZMod babyBearModulus)) := by
  have offset : (xorData kind).offset = 0 := by fin_cases kind <;> rfl
  apply Vector.ext
  intro j hj
  simp [xorRegionRow, TableData.row, offset, signedValue_cast]

end Proofs
end Airbender.Blake2G
