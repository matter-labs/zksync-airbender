module
public import Proven.NonVacuous.DynamicCopyLoop.Model
public import Proven.NonVacuous.MachineBoot

@[expose] public section
namespace Airbender.NonVacuous.DynamicCopyLoop
open Trace Arithmetic
set_option warningAsError true

/-- Window zero remains unchanged. Window one records both buffers after the second COPY call. -/
def teardownAssignment (row column : Nat) : ZMod babyBearModulus :=
  if row < 16 && column == 132 then 51
  else if (row == 0 || row == 8) && column == 130 then 7 else 0

/-- The two public inline windows cover the code shadow and both data buffers. -/
def inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout) :=
  [⟨#v[0, 1], teardownAssignment⟩]

/-- Every register and every aligned word of both initialization windows is tracked. -/
noncomputable def cells := Machine.cells InitsTeardowns.unifiedLayout inits

/-- All submitted rows share the complete native initialization and teardown boundary. -/
noncomputable def trace : UnifiedTrace babyBearModulus :=
  { finiteTrace with
    initialMemory := registerSeeds ++ inits.flatMap InitsTeardowns.Witness.initTokens
    terminalMemory := registerCells.map final ++ inits.flatMap InitsTeardowns.Witness.teardownTokens }

/-- The public top bits satisfy the full statement verifier check. -/
theorem checked : InitsTeardowns.TopBitsChecked (inits.flatMap fun witness => witness.topBits.toList) := by
  change InitsTeardowns.TopBitsChecked [0, 1]
  simp [InitsTeardowns.TopBitsChecked, InitsTeardowns.maxTopBit]

/-- Every actual row preserves the sequential native clock path, including repeated loop PCs. -/
theorem states : (trace.initial :: trace.rows.map Row.finish).Perm
    (trace.terminal :: trace.rows.map Row.start) := by
  change ((trace.rows.map Row.start) ++ [trace.terminal]).Perm
    ([trace.terminal] ++ trace.rows.map Row.start)
  exact List.perm_append_comm

/-- The public ROM image produces exactly the twelve supported program entries. -/
theorem program_image : rvMachineProgramImage .unified initial
    ((List.finRange 12).map fun index => BitVec.ofNat 32 (code index).1) = some program := by
  kernel_rfl

/-- Architectural cell reads use zero registers and zero RAM at public boot. -/
theorem initial_read (cell : Cell) : cell.readRV initial = cell.readRV Machine.zero := by
  cases cell <;> rfl

/-- The final register and RAM token at a cell retains that cell's address. -/
theorem final_address (cell : Cell) : (final cell).address = cell.addressCode := by
  cases cell with
  | register index => rfl
  | ram address =>
    simp only [final]
    split <;> rfl

/-- The complete inline boundary meets the production target's public boot premises. -/
theorem boot : Trace.Machine.BootInputs .unified trace initial cells program
    InitsTeardowns.unifiedLayout inits := by
  have properties : InitsTeardowns.Claims InitsTeardowns.unifiedLayout :=
    InitsTeardowns.Proofs.claims ⟨rfl, Or.inl rfl⟩
  have aligned := Machine.cells_aligned InitsTeardowns.unifiedLayout properties inits checked
  have seed : registerSeeds ++ inits.flatMap InitsTeardowns.Witness.initTokens =
      ROMView.nativeBootImage cells := by
    rw [(properties.bootImage inits checked).2]
    simp only [cells, Machine.cells, registerSeeds, ROMView.nativeBootImage, List.map_append]
  refine ⟨Machine.cells_distinct _ properties _ checked, aligned, rfl, ?_,
    ⟨_, program_image⟩, checked, rfl, ⟨registerCells.map final, ?_, rfl⟩, rfl, ?_, rfl, ?_⟩
  · intro index
    simp only [Cell.readRV, RV.State.getReg, initial]
    split <;> rfl
  · rw [List.map_map]
    have same : (fun cell => (final cell).address) = Cell.addressCode := funext final_address
    change (registerCells.map (fun cell => (final cell).address)).Perm _
    rw [same]
  · change initialImageRV initial cells = some (registerSeeds ++ inits.flatMap InitsTeardowns.Witness.initTokens)
    rw [seed]
    simpa only [initialImageRV, initial_read] using Machine.image_zero cells aligned
  · exact ⟨⟨156, (68, 0)⟩, rfl, states⟩

end Airbender.NonVacuous.DynamicCopyLoop
