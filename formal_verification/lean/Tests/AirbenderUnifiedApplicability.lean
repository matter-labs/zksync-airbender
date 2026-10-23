import Tests.AirbenderApplicability
import Tests.AirbenderUnifiedNative

namespace Tests.AirbenderUnifiedApplicability
open Airbender Airbender.Trace Airbender.Arithmetic Airbender.Initialization
open Airbender.Reference Airbender.Reference.Sail Airbender.Reference.RiscV.Sail
open _root_.Sail.ArchSem
set_option warningAsError true
set_option Elab.async false
local instance : MemoryPlatform SailRV32.exception := Tests.upstreamPlatform.airbender

noncomputable def trace := AirbenderUnifiedNative.trace AirbenderApplicability.unifiedDomain

private theorem subset : AirbenderNative.touched ⊆ AirbenderApplicability.unifiedDomain := by
  intro cell member
  simp only [AirbenderNative.touched, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact ExternalBoundary.Initialization.Proofs.all_registers
        (AirbenderInitialization.unifiedWindows.selection Proofs.unified_geometry) _
    | exact AirbenderInitialization.unified_clint_member

theorem native_accepted : Trace.Accepted trace :=
  AirbenderUnifiedNative.accepted _
    (ExternalBoundary.Initialization.Proofs.cells_distinct
      (AirbenderInitialization.unifiedWindows.selection Proofs.unified_geometry)) subset

/- Read the already imported native source literal and reuse its existing
physical-address resolver. This is the same elaboration/source boundary as
`import_clean`; no second parser or extra file dependency is introduced. -/
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let some info := environment.find? `Airbender.UnifiedReduced.importedConstraintsSourceBytes
    | throwError "missing imported unified source bytes"
  let some value := info.value? (allowOpaque := true)
    | throwError "unified source bytes have no definition"
  let .lit (.strVal source) := value
    | throwError "unified source bytes must remain an actual string literal"
  let .ok circuit := Airbender.parseCircuit source
    | throwError "cannot parse imported unified source bytes"
  unless circuit.memory_layout.total_width == 38 do
    throwError "unified physical memory width changed; review the fixture projection"
  let unit : Coefficient := ⟨⟨268435454, by decide⟩⟩
  let zero : Coefficient := ⟨⟨0, by decide⟩⟩
  let mut terms : Array (TSyntax `term) := #[]
  for column in [:circuit.memory_layout.total_width] do
    let relation : LinearRelation := ⟨#[(unit, .BaseLayerMemory column)], zero⟩
    let .ok expression := circuit.lookupExpression relation
      | throwError "physical unified memory column{column} has no unique logical variable"
    let logicalResult : Option Nat := match expression with
      | .Sum parts => match parts.toList with
        | [.Constant _, .Product factors] => match factors.toList with
          | [.Constant _, .Var logicalId] => some logicalId
          | _ => none
        | _ => none
      | _ => none
    let some logicalId := logicalResult
      | throwError "unexpected public resolver shape for physical column{column}"
    terms := terms.push (quote logicalId)
  let name := mkIdent `physicalMemoryProjection
  elabCommand (← `(def $name : Array Nat := #[$[$terms],*]))

/-- Both imported views are compiled from the exact same native JSON bytes. -/
theorem projection_source_identity :
    unified.sourceBytes = UnifiedReduced.importedConstraintsSourceBytes := by rfl

theorem projection_width : physicalMemoryProjection.size = unified.layout.memoryWidth := by rfl

/-- The full clean assignments retain all actual native CPU variables. -/
def clean : Raw babyBearModulus := fun row column =>
  if row = 0 then AirbenderUnifiedNative.luiAssignment column
  else if row = 1 then AirbenderUnifiedNative.addiAssignment column
  else if row = 2 then AirbenderUnifiedNative.swAssignment column
  else if row = 3 then AirbenderUnifiedNative.lwAssignment column else 0

/-- Only indices below the native memory width denote physical memory columns.
The total-function extension outside that bank retains the clean index. -/
def physicalNativeColumn (column : Nat) : Nat :=
  (physicalMemoryProjection[column]?).getD column

/-- Inline initialization reads the physical memory view of those SAME four
assignments, rather than treating physical bank offsets as clean variable IDs. -/
def raw : Raw babyBearModulus := fun row column => clean row (physicalNativeColumn column)

theorem native_rows :
    ([⟨.machine, clean 0⟩, ⟨.machine, clean 1⟩, ⟨.machine, clean 2⟩, ⟨.machine, clean 3⟩] :
      List (Row babyBearModulus UnifiedFamily)) = AirbenderUnifiedNative.rows := by rfl

/-- Every physical memory column, including both inline teardown sets, reads
from the full native assignment through the artifact-resolved projection. -/
theorem physical_native_coupling (row : Nat) (column : Fin unified.layout.memoryWidth) :
    raw row column.val = clean row
      (physicalMemoryProjection[column.val]'(by rw [projection_width]; exact column.isLt)) := by
  fin_cases column <;> rfl

private def embed : ZMod babyBearModulus →+* ZMod babyBearModulus := RingHom.id _
private def weights : Fin 6 → ZMod babyBearModulus := fun _ => 0

/-- Every selected public row is admitted by the actual imported inline graph.
Exact token matching below is independent of the permissible unit challenge. -/
theorem initialization_accepted : Initialization.Accepted unified
    (parametersFor embed 0 weights AirbenderInitialization.unifiedWindows)
    raw (fun _ _ => 1) := by
  intro row gate _
  cases gate <;> simp [Gate.Sat, Leaf.factor, parametersFor, embed, weights]

theorem profile : UnifiedProfile trace unified.layout Proofs.unified_geometry
    AirbenderInitialization.unifiedWindows AirbenderProgram.before AirbenderUnifiedNative.program := by
  exact {
    profile := AirbenderApplicability.unified_profile.profile
    image := AirbenderApplicability.unified_profile.image
    initialPC := rfl
    programImage := AirbenderApplicability.unified_profile.programImage
    setup := rfl
    code := AirbenderApplicability.unified_profile.code
    configuration := AirbenderApplicability.unified_profile.configuration
    ordinary := AirbenderApplicability.unified_profile.ordinary
    landingPadDisabled := AirbenderApplicability.unified_profile.landingPadDisabled
    loads := AirbenderApplicability.unified_profile.loads }

private theorem selected_cell_iff {layout : Layout} (geometry : Geometry layout)
    (windows : Windows layout) (set target : Fin layout.columns.size)
    (row targetRow : Fin layout.rows) :
    ExternalBoundary.Initialization.cell (geometry := geometry.public) (windows.index set, row) =
      ExternalBoundary.Initialization.cell (geometry := geometry.public) (windows.index target, targetRow) ↔
        set = target ∧ row = targetRow := by
  constructor
  · intro same
    have coordinates := ExternalBoundary.Initialization.Proofs.cell_injective same
    exact ⟨windows.unique (congrArg Prod.fst coordinates), congrArg Prod.snd coordinates⟩
  · rintro ⟨rfl, rfl⟩; rfl

private theorem terminal_token (set : Fin unified.layout.columns.size)
    (row : Fin unified.layout.rows) :
    (Leaf.mk .terminal set.val unified.layout.columns[set]).token unified.layout
      (parametersFor embed 0 weights AirbenderInitialization.unifiedWindows) raw row.val =
    AirbenderNative.final (ExternalBoundary.Initialization.cell
      (geometry := Proofs.unified_geometry.public)
      (AirbenderInitialization.unifiedWindows.index set, row)) := by
  rw [Proofs.terminal_token unified.layout Proofs.unified_geometry
    AirbenderInitialization.unifiedWindows embed 0 weights raw set row]
  have encoded : ExternalBoundary.Initialization.cell
      (geometry := Proofs.unified_geometry.public)
      (AirbenderInitialization.unifiedWindows.index ⟨0, by decide⟩, ⟨0, by decide⟩) =
        Cell.ram 33554432 := by
    change Cell.ram (BitVec.ofNat 32 (4 * (1 * 8388608 + 0))) = Cell.ram 33554432
    norm_num
    decide +kernel
  have coordinateMatch := selected_cell_iff Proofs.unified_geometry
    AirbenderInitialization.unifiedWindows set ⟨0, by decide⟩ row ⟨0, by decide⟩
  rw [encoded] at coordinateMatch
  have same : (ExternalBoundary.Initialization.cell
      (geometry := Proofs.unified_geometry.public)
      (AirbenderInitialization.unifiedWindows.index set, row) = Cell.ram 33554432) ↔
        set.val = 0 ∧ row.val = 0 := by
    simpa only [Fin.ext_iff] using coordinateMatch
  have different (index : BitVec 5) : ExternalBoundary.Initialization.cell
      (geometry := Proofs.unified_geometry.public)
      (AirbenderInitialization.unifiedWindows.index set, row) ≠ Cell.register index := by
    simp [ExternalBoundary.Initialization.cell]
  simp only [AirbenderNative.final, different, if_false, same]
  have columns (index : Fin unified.layout.columns.size) :
      unified.layout.columns[index] =
        if index.val = 0 then (⟨32, 33, 30, 31⟩ : Columns) else ⟨36, 37, 34, 35⟩ := by
    fin_cases index <;> rfl
  rw [columns set]
  fin_cases set <;>
    (by_cases chosen : row.val = 0 <;>
      simp [raw, physicalNativeColumn, physicalMemoryProjection, clean,
        AirbenderUnifiedNative.luiAssignment, AirbenderUnifiedNative.addiAssignment,
        AirbenderUnifiedNative.swAssignment, AirbenderUnifiedNative.lwAssignment,
        AirbenderNative.old, Cell.initialToken, chosen, Arithmetic.Word.ofBitVec,
        babyBearModulus])
  all_goals first
    | rfl
    | exact ⟨(show (7 : ZMod babyBearModulus).val = 7 from
        ZMod.val_natCast_of_lt (by norm_num [babyBearModulus])), rfl⟩

private theorem terminal_ram : ramTokens unified.layout
    (parametersFor embed 0 weights AirbenderInitialization.unifiedWindows) raw .terminal =
    ((((AirbenderInitialization.unifiedWindows.selection Proofs.unified_geometry).indices.product
      (List.finRange unified.layout.rows)).map
        (ExternalBoundary.Initialization.cell (geometry := Proofs.unified_geometry.public))).map
          AirbenderNative.final) := by
  simp only [ramTokens, Layout.leaves, Windows.selection,
    List.product, List.flatMap_map, List.map_map, Function.comp_def]
  rw [List.map_flatMap]
  simp only [List.map_map, Function.comp_def]
  apply List.flatMap_congr
  intro set _
  apply List.map_congr_left
  intro row _
  exact terminal_token set row

/-- Full selected windows1/6, including CLINT and SIG, are the exact public
boundary of the actual four native rows. No RAM cell list is enumerated. -/
theorem native_boundary : withBoundary trace unified.layout
    (parametersFor embed 0 weights AirbenderInitialization.unifiedWindows) raw
      AirbenderApplicability.terminalRegisters = trace := by
  simp only [withBoundary, trace, AirbenderUnifiedNative.trace,
    Proofs.initial_ram_tokens unified.layout Proofs.unified_geometry,
    terminal_ram, AirbenderApplicability.terminalRegisters, AirbenderApplicability.unifiedDomain,
    cells, ExternalBoundary.Initialization.cells, ROMView.nativeBootImage, List.map_append]
  rfl

/-- Nonempty application of the original inline initialization endpoint to the
same actual LUI/ADDI/SW/LW program and its CLINT RAM store/load history. -/
theorem native_execution : Realizes (UnifiedReduced.Step AirbenderUnifiedNative.program)
    trace AirbenderProgram.before AirbenderApplicability.unifiedDomain
      (ROMView.token AirbenderProgram.before) := by
  have result := Initialization.unified_boundary_execution (by decide) (by decide) (by decide)
    AirbenderInitialization.unifiedWindows embed 0 weights raw (fun _ _ => 1)
    AirbenderApplicability.terminalRegisters profile initialization_accepted
    (by rw [native_boundary]; exact native_accepted)
    (by rw [native_boundary]; exact AirbenderUnifiedNative.decoded _)
  rw [native_boundary] at result
  exact result.2

/-- The native application and concrete original execution share the same
public program: terminal PC16, loaded x3=7, and RAM33554432=7. -/
theorem concrete_application :
    Realizes (UnifiedReduced.Step AirbenderUnifiedNative.program) trace AirbenderProgram.before
      AirbenderApplicability.unifiedDomain (ROMView.token AirbenderProgram.before) ∧
    Relation.ReflTransGen (UnifiedReduced.Step AirbenderUnifiedNative.program)
      AirbenderProgram.before AirbenderProgram.afterLW ∧
    run (SailRV32.Functions.get_arch_pc ()) AirbenderProgram.afterLW =
      .ok 16 AirbenderProgram.afterLW ∧
    (Cell.register 3).read AirbenderProgram.afterLW = .ok 7 AirbenderProgram.afterLW ∧
    (Cell.ram 33554432).read AirbenderProgram.afterLW = .ok 7 AirbenderProgram.afterLW :=
  ⟨native_execution, AirbenderUnifiedNative.decoded_execution, AirbenderUnifiedNative.terminal⟩

end Tests.AirbenderUnifiedApplicability
