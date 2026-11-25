module
public import Proven.Final.Circuits.UnifiedReduced.Proth120Windows
public import Proven.InitsTeardowns.Claims
public import Proven.Trace.RVBootSeed

@[expose] public section
namespace Airbender.UnifiedReduced.Proth120
open Trace InitsTeardowns

/-- The 32 register seeds and every native inline initialization token carry the zero
    architectural word at the corresponding register or aligned RAM address. -/
theorem zero_boot {initial : RV.State} {cells : List Cell} {seeds : List (MemoryToken proth120Modulus)}
    (instances : List (Witness proth120Modulus importedLayout))
    (tops : ∀ top ∈ instances.flatMap (fun w => w.topBits.toList), top < 256)
    (domain : cells = registerCells ++ windowCells importedLayout (instances.flatMap fun w => w.topBits.toList))
    (native : seeds = registerSeeds ++ instances.flatMap Witness.initTokens)
    (image : initialImageRV initial cells = some seeds) : ∀ cell ∈ cells, cell.readRV initial = some 0 := by
  apply Trace.Proofs.rv_image_zero (p := proth120Modulus)
  have windows : instances.flatMap Witness.initTokens =
      ROMView.nativeBootImage (windowCells importedLayout (instances.flatMap fun w => w.topBits.toList)) := by
    simp only [windowCells, ROMView.nativeBootImage,
      List.map_flatMap, List.flatMap_assoc, List.map_map]
    apply InitsTeardowns.Proofs.flatMap_congr_mem
    intro w member
    apply InitsTeardowns.Proofs.flatMap_congr_mem
    intro top present
    apply List.map_congr_left
    intro r position
    obtain ⟨s, h⟩ := List.mem_iff_getElem.mp present
    have bounded := tops top (List.mem_flatMap.mpr ⟨w, member, present⟩)
    have size : s < importedLayout.sets.size := by simpa using h.1
    have eq : w.topBits[s] = top := by simpa using h.2
    have valid : r < 2 ^ importedLayout.traceLog := List.mem_range.mp position
    have token := (window_tokens w ⟨s, size⟩ ⟨r, valid⟩ (eq ▸ bounded)).2.2.1
    change initToken importedLayout top r = (Cell.ram (BitVec.ofNat 32 (windowAddress importedLayout top r))).initialToken 0
    rw [← eq]
    exact token
  rw [image, native, domain, windows]
  simp [registerSeeds, ROMView.nativeBootImage]

end Airbender.UnifiedReduced.Proth120
