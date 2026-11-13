module
public import Human.Compiler.NativeTargets
public import Proven.InitsTeardowns.Claims
public import Proven.Trace.Machine.Boot
public import Proven.KernelRfl
@[expose] public section
namespace Airbender.NonVacuous.Machine
open Airbender Trace Trace.Machine Arithmetic
set_option warningAsError true
set_option maxRecDepth 65536

def zero : RV.State where
  pc := 0
  regFile _ := 0
  rom _ := 0
  mem _ := 0

theorem cell_zero (cell : Cell) (aligned : cell.Aligned) : cell.readRV zero = some 0 := by
  cases cell with
  | register index => simp [Cell.readRV, zero, RV.State.getReg]
  | ram address =>
    have readable : RV.readable address 4 := by
      have bounded := address.isLt
      change address.toNat % 4 = 0 at aligned
      change address.toNat + 4 ≤ 4294967296
      omega
    simp [Cell.readRV, readable, zero, RV.read]

theorem image_zero (cells : List Cell) (aligned : ∀ cell ∈ cells, cell.Aligned) :
    initialImageRV (p := babyBearModulus) zero cells = some (ROMView.nativeBootImage cells) := by
  induction cells with
  | nil => rfl
  | cons cell rest ih =>
    have first := cell_zero cell (aligned cell List.mem_cons_self)
    have tail := ih (fun c member => aligned c (List.mem_cons_of_mem _ member))
    simp only [initialImageRV, List.mapM_cons, first, Option.map_some,
      ROMView.nativeBootImage, List.map_cons] at *
    rw [tail]
    rfl

def cells (layout : InitsTeardowns.Layout)
    (inits : List (InitsTeardowns.Witness babyBearModulus layout)) : List Cell :=
  registerCells ++ InitsTeardowns.windowCells layout (inits.flatMap fun w => w.topBits.toList)

theorem cells_aligned (layout : InitsTeardowns.Layout) (properties : InitsTeardowns.Claims layout)
    (inits : List (InitsTeardowns.Witness babyBearModulus layout))
    (checked : InitsTeardowns.TopBitsChecked (inits.flatMap fun w => w.topBits.toList)) :
    ∀ cell ∈ cells layout inits, cell.Aligned := by
  intro cell member
  rcases List.mem_append.mp member with registers | windows
  · obtain ⟨index, _, rfl⟩ := List.mem_map.mp registers
    trivial
  · obtain ⟨top, present, member⟩ := List.mem_flatMap.mp windows
    obtain ⟨row, bounded, rfl⟩ := List.mem_map.mp member
    exact (properties.init top (checked.2 top present) row (List.mem_range.mp bounded)).2.1

theorem cells_distinct (layout : InitsTeardowns.Layout) (properties : InitsTeardowns.Claims layout)
    (inits : List (InitsTeardowns.Witness babyBearModulus layout))
    (checked : InitsTeardowns.TopBitsChecked (inits.flatMap fun w => w.topBits.toList)) :
    (cells layout inits).Nodup := by
  rw [cells, List.nodup_append]
  refine ⟨by decide +kernel, (properties.bootImage inits checked).1, ?_⟩
  intro left registers right windows equal
  obtain ⟨index, _, same⟩ := List.mem_map.mp registers
  obtain ⟨top, _, member⟩ := List.mem_flatMap.mp windows
  obtain ⟨row, _, ram⟩ := List.mem_map.mp member
  rw [← same, ← ram] at equal
  cases equal

def emptyTrace {Kind : Type} [CircuitLayout Kind] (setup : CircuitLayout.Setup (Kind := Kind) babyBearModulus)
    (layout : InitsTeardowns.Layout) (inits : List (InitsTeardowns.Witness babyBearModulus layout)) :
    Data babyBearModulus Kind where
  rows := []
  rom := setup
  initial := PCState.boundary 0 (4, 0)
  terminal := PCState.boundary 0 (4, 0)
  initialMemory := registerSeeds ++ inits.flatMap InitsTeardowns.Witness.initTokens
  terminalMemory := registerSeeds ++ inits.flatMap InitsTeardowns.Witness.initTokens

theorem boot {Kind : Type} [CircuitLayout Kind] (config : RVMachineConfig)
    (setup : CircuitLayout.Setup (Kind := Kind) babyBearModulus)
    (layout : InitsTeardowns.Layout) (properties : InitsTeardowns.Claims layout)
    (inits : List (InitsTeardowns.Witness babyBearModulus layout))
    (checked : InitsTeardowns.TopBitsChecked (inits.flatMap fun w => w.topBits.toList)) :
    BootInputs config (emptyTrace setup layout inits) zero (cells layout inits) [] layout inits := by
  have aligned := cells_aligned layout properties inits checked
  have seed : registerSeeds ++ inits.flatMap InitsTeardowns.Witness.initTokens =
      ROMView.nativeBootImage (cells layout inits) := by
    rw [(properties.bootImage inits checked).2]
    simp only [cells, registerSeeds, ROMView.nativeBootImage, List.map_append]
  refine ⟨cells_distinct layout properties inits checked, aligned, rfl, ?_, ⟨[], rfl⟩,
    checked, rfl, rfl, ?_, rfl, ?_⟩
  · intro index
    exact cell_zero _ trivial
  · change initialImageRV zero (cells layout inits) = some (registerSeeds ++ inits.flatMap InitsTeardowns.Witness.initTokens)
    rw [seed]
    exact image_zero _ aligned
  · refine ⟨⟨0, (4, 0)⟩, rfl, ?_⟩
    exact List.Perm.refl _

end Airbender.NonVacuous.Machine
