import Airbender.Review.Helpers.Core.FieldCapacity
import Airbender.Proofs.Blake2Round.ImportedXor

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

def nativeTags : Vector Nat 6 := #v[4, 19, 20, 55, 56, 57]
def nativeLengths : Vector Nat 6 := #v[65536, 16384, 262144, 196608, 49152, 16384]

def referenceRegionRow (kind : Fin 6) (n : Nat) : Vector Nat 6 :=
  #v[plainXorRow 256 4 n, plainXorRow 128 19 n, plainXorRow 512 20 n,
    carryXorRow 256 55 n, carryXorRow 128 56 n, combinedXorRow n][kind]

theorem region_tag (kind : Fin 6) (n : Nat) :
    (referenceRegionRow kind n)[5] = nativeTags[kind] := by
  fin_cases kind <;> rfl

private theorem tag_bound {p : Nat} (hp : FieldCapacity.AtLeast p 512) (kind : Fin 6) : nativeTags[kind] < p := by
  fin_cases kind <;> dsimp [nativeTags] <;> omega

/-- Every satisfying native entry belongs to one actual imported region. -/
theorem any_region {p : Nat} [Fact p.Prime]
    {entry : Vector (Expression (ZMod p)) 6} {env : Environment (ZMod p)}
    (member : (Lookup.mk setupTable.toRaw entry).Contains env) :
    ∃ kind : Fin 6, ∃ n, n < nativeLengths[kind] ∧
      entry.map (Expression.eval env) =
        (referenceRegionRow kind n).map (fun value : Nat => (value : ZMod p)) := by
  change ∃ index : Fin 606208, entry.map (Expression.eval env) =
    (setupRow index).map (fun value : Nat => (value : ZMod p)) at member
  obtain ⟨index, row⟩ := member
  rw [setup_row_characterization] at row
  have bound := index.isLt
  unfold referenceSetupRow at row
  dsimp only [xor8DataRegion, xor7DataRegion, xor9DataRegion,
    xor8CarryDataRegion, xor7CarryDataRegion, xor4x3DataRegion] at row
  split_ifs at row
  · exact ⟨0, index.val, by change _ < 65536; omega, row⟩
  · exact ⟨1, index.val - 65536, by change _ < 16384; omega, row⟩
  · exact ⟨2, index.val - 81920, by change _ < 262144; omega, row⟩
  · exact ⟨3, index.val - 344064, by change _ < 196608; omega, row⟩
  · exact ⟨4, index.val - 540672, by change _ < 49152; omega, row⟩
  · exact ⟨5, index.val - 589824, by change _ < 16384; omega, row⟩

/-- A native discriminator selects its own imported region. Bounds and every
    physical column come from membership, without a table-equivalence premise. -/
theorem selected_region {p : Nat} [Fact p.Prime] (hp : FieldCapacity.AtLeast p 512)
    {entry : Vector (Expression (ZMod p)) 6} {env : Environment (ZMod p)}
    (kind : Fin 6) (member : (Lookup.mk setupTable.toRaw entry).Contains env)
    (selected : entry[5].eval env = ((nativeTags[kind] : Nat) : ZMod p)) :
    ∃ n, n < nativeLengths[kind] ∧
      entry.map (Expression.eval env) =
        (referenceRegionRow kind n).map (fun value : Nat => (value : ZMod p)) := by
  obtain ⟨actual, n, bound, row⟩ := any_region member
  have column : entry[5].eval env = ((nativeTags[actual] : Nat) : ZMod p) := by
    have same := congrArg (fun v : Vector (ZMod p) 6 => v[5]) row
    simpa only [Vector.getElem_map, region_tag] using same
  have tagged : nativeTags[actual] = nativeTags[kind] := by
    have same := congrArg ZMod.val (column.symm.trans selected)
    simpa only [ZMod.val_natCast_of_lt (tag_bound hp actual),
      ZMod.val_natCast_of_lt (tag_bound hp kind)] using same
  have same : actual = kind := by
    fin_cases actual <;> fin_cases kind
    all_goals first | rfl | norm_num [nativeTags] at tagged
  subst actual
  exact ⟨n, bound, row⟩

end Airbender.Blake2Round.Proofs
