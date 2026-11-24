module
public import Proven.Trace.RVBootSeed
public import Proven.Final.Circuits.InitsTeardowns.Theorems
public import Proven.NonVacuous.Basic

@[expose] public section

/-! Boot facts for the non-vacuity witnesses: a state with zero registers and zero RAM reads 0 at every aligned
    cell, so its initial image is the zero boot image; the inits/teardowns windows are aligned. Stated for any
    tracked domain and layout: nothing here evaluates a window (`2 ^ 24` rows). -/

namespace Airbender.NonVacuous
open Trace Arithmetic

/-- A state whose registers and RAM are zero reads 0 at every aligned cell. -/
theorem readRV_zero {s : RV.State} (registers : ∀ i, s.regFile i = 0) (ram : ∀ a, s.mem a = 0) :
    ∀ cell : Cell, cell.Aligned → cell.readRV s = some 0
  | .register i, _ => by simp [Cell.readRV, RV.State.getReg, registers]
  | .ram address, aligned => by
    have bound := address.isLt
    have aligned : address.toNat % 4 = 0 := aligned
    have readable : RV.readable address 4 := by
      simp only [RV.readable, RV.RAM_END]
      omega
    simp only [Cell.readRV, readable, ite_true, RV.read, ram]
    rfl

/-- Reading cells that all read 0 gives the zero boot image. -/
theorem initialImageRV_zero {p : Nat} {s : RV.State} :
    ∀ {cells : List Cell}, (∀ cell ∈ cells, cell.readRV s = some 0) →
      initialImageRV (p := p) s cells = some (ROMView.nativeBootImage cells)
  | [], _ => rfl
  | cell :: cells, reads => by
    have rest := initialImageRV_zero (p := p) (cells := cells) fun c member => reads c (List.mem_cons_of_mem _ member)
    simp only [initialImageRV, ROMView.nativeBootImage] at rest ⊢
    simp [List.mapM_cons, reads cell List.mem_cons_self, rest]

/-- The window cells of checked top bits are aligned RAM words. -/
theorem windowCells_aligned {layout : InitsTeardowns.Layout} (claims : InitsTeardowns.Claims layout)
    {topBits : List Nat} (bounded : ∀ top ∈ topBits, top < InitsTeardowns.maxTopBit) :
    ∀ cell ∈ InitsTeardowns.windowCells layout topBits, cell.Aligned := by
  intro cell member
  simp only [InitsTeardowns.windowCells, InitsTeardowns.rows, List.mem_flatMap, List.mem_map,
    List.mem_range] at member
  obtain ⟨top, htop, row, hrow, rfl⟩ := member
  exact (claims.init top (bounded top htop) row hrow).2.1

/-- Every register cell is a register seed cell. -/
theorem register_mem_registerCells (index : RV.Reg) : Cell.register index ∈ registerCells := by
  simp only [registerCells, List.mem_map, List.mem_range]
  exact ⟨index.toNat, index.isLt, by simp⟩

theorem registerCells_nodup : registerCells.Nodup := by decide

/-- Registers, then window cells of checked top bits: distinct and aligned. -/
theorem boot_cells {layout : InitsTeardowns.Layout} (shape : InitsTeardowns.Proofs.Shape layout)
    {topBits : List Nat} (checked : InitsTeardowns.TopBitsChecked topBits) :
    (registerCells ++ InitsTeardowns.windowCells layout topBits).Nodup ∧
      ∀ cell ∈ registerCells ++ InitsTeardowns.windowCells layout topBits, cell.Aligned := by
  refine ⟨List.nodup_append.2 ⟨registerCells_nodup, InitsTeardowns.Proofs.windowCells_nodup shape checked, ?_⟩, ?_⟩
  · intro a ha b hb same
    subst same
    simp only [registerCells, List.mem_map] at ha
    obtain ⟨_, _, rfl⟩ := ha
    simp [InitsTeardowns.windowCells] at hb
  · intro cell member
    rcases List.mem_append.1 member with present | present
    · simp only [registerCells, List.mem_map] at present
      obtain ⟨_, _, rfl⟩ := present
      trivial
    · exact windowCells_aligned (InitsTeardowns.Proofs.claims shape) checked.2 cell present

end Airbender.NonVacuous
