import Airbender.Proofs.Blake2G.ImportedXor

namespace Airbender.Blake2Round.Proofs
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 4000000

def gWidths : Vector Nat 5 := #v[8, 3, 4, 7, 9]
def gTags : Vector Nat 5 := #v[4, 17, 18, 19, 20]

/-- Construct only existing fixed rows, using the G artifact's own region offsets.
    The controller remains arbitrary and is never selected by these rows. -/
theorem g_xor_row (control : Fin 512 → Vector Nat 7) (kind : Fin 5) (a b : Nat)
    (ha : a < 2 ^ gWidths[kind]) (hb : b < 2 ^ gWidths[kind]) :
    ∃ index : Fin 344896, Blake2G.setupRow control index =
      #v[a, b, a ^^^ b, 0, 0, 0, 0, 0, gTags[kind]] := by
  let base := 2 ^ gWidths[kind]
  have bound : (Blake2G.xorRegion kind).offset + a * base + b < 344896 := by
    fin_cases kind
    all_goals norm_num [base, gWidths, Blake2G.xorRegion,
      Blake2G.xor8DataRegion, Blake2G.xor3DataRegion, Blake2G.xor4DataRegion,
      Blake2G.xor7DataRegion, Blake2G.xor9DataRegion] at ha hb ⊢
    all_goals omega
  let index : Fin 344896 := ⟨(Blake2G.xorRegion kind).offset + a * base + b, bound⟩
  refine ⟨index, ?_⟩
  rw [Blake2G.Proofs.setup_row_characterization]
  fin_cases kind
  all_goals unfold Blake2G.referenceSetupRow
  all_goals norm_num [index, base, gWidths, gTags, Blake2G.xorRegion,
    Blake2G.xor8DataRegion, Blake2G.xor3DataRegion, Blake2G.xor4DataRegion,
    Blake2G.xor7DataRegion, Blake2G.xor9DataRegion] at ha hb
  all_goals dsimp only [index, base, gWidths, gTags, Blake2G.xorRegion,
    Blake2G.xor8DataRegion, Blake2G.xor3DataRegion, Blake2G.xor4DataRegion,
    Blake2G.xor7DataRegion, Blake2G.xor9DataRegion]
  all_goals simp only [Fin.getElem_fin, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, Nat.reducePow,  ]
  all_goals split_ifs <;> try omega
  all_goals apply Vector.ext
  all_goals intro j hj
  all_goals interval_cases j
  all_goals simp only [Blake2G.xorRow,  Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, Nat.reducePow,  ]
  all_goals first | omega | exact congrArg₂ Nat.xor (by omega) (by omega)

theorem g_xor_membership {p : Nat} [Fact p.Prime]
    (control : Fin 512 → Vector Nat 7) (kind : Fin 5) (a b : Nat)
    (ha : a < 2 ^ gWidths[kind]) (hb : b < 2 ^ gWidths[kind])
    {target : Vector (Expression (ZMod p)) 9} {env : Environment (ZMod p)}
    (columns : target.map (Expression.eval env) =
      (#v[a, b, a ^^^ b, 0, 0, 0, 0, 0, gTags[kind]] : Vector Nat 9).map
        (fun value : Nat => (value : ZMod p))) :
    (Lookup.mk (Blake2G.setupTable control).toRaw target).Contains env := by
  obtain ⟨index, row⟩ := g_xor_row control kind a b ha hb
  change ∃ index : Fin 344896, target.map (Expression.eval env) =
    (Blake2G.setupRow control index).map (fun value : Nat => (value : ZMod p))
  exact ⟨index, by rw [row]; exact columns⟩

end Airbender.Blake2Round.Proofs
