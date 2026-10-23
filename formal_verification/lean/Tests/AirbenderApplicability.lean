import Tests.AirbenderNative

namespace Tests.AirbenderApplicability
open Airbender Airbender.Trace Airbender.Arithmetic Airbender.Initialization
open Airbender.Reference Airbender.Reference.Sail Airbender.Reference.RiscV.Sail
open _root_.Sail.ArchSem
set_option warningAsError true
set_option Elab.async false
local instance : MemoryPlatform SailRV32.exception := Tests.upstreamPlatform.airbender

noncomputable def standaloneDomain := cells Proofs.standalone_geometry AirbenderInitialization.standaloneWindows
noncomputable def unifiedDomain := cells Proofs.unified_geometry AirbenderInitialization.unifiedWindows

private theorem standalone_image_exists :
    ∃ physical : List (MemoryToken babyBearModulus),
      initialImage AirbenderProgram.before standaloneDomain = some physical := by
  obtain ⟨image, source, _⟩ := AirbenderInitialization.standalone_profile.physicalImage
  exact AirbenderProgram.physical_image source
    (ExternalBoundary.Initialization.Proofs.aligned
      (AirbenderInitialization.standaloneWindows.selection Proofs.standalone_geometry))

private theorem unified_image_exists :
    ∃ physical : List (MemoryToken babyBearModulus),
      initialImage AirbenderProgram.before unifiedDomain = some physical := by
  obtain ⟨image, source⟩ := AirbenderInitialization.unified_profile.image
  exact AirbenderProgram.physical_image source
    (ExternalBoundary.Initialization.Proofs.aligned
      (AirbenderInitialization.unifiedWindows.selection Proofs.unified_geometry))

noncomputable def standalonePhysical := Classical.choose standalone_image_exists
noncomputable def unifiedPhysical := Classical.choose unified_image_exists
noncomputable def standaloneTrace := AirbenderNative.trace standaloneDomain standalonePhysical

private theorem pooled_program_image :
    programImageRunWith pooledDecoderFields AirbenderProgram.before [0, 4, 8, 12] =
      some AirbenderNative.pooledProgram := by
  apply AirbenderProgram.mapped_program_image pooledDecoderFields
    (DecoderData.mapFamily pooledArithmeticFamily)
  intro entry member
  simp only [AirbenderProgram.program, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> rfl

def unifiedProgram : List UnifiedReduced.ProgramEntry :=
  AirbenderProgram.program.map fun entry =>
    ⟨entry.pc, entry.bits, entry.instruction, UnifiedReduced.arithmeticFields entry.data⟩

private theorem unified_program_image :
    programImageRunWith UnifiedReduced.decoderFields AirbenderProgram.before [0, 4, 8, 12] =
      some unifiedProgram := by
  apply AirbenderProgram.mapped_program_image UnifiedReduced.decoderFields UnifiedReduced.arithmeticFields
  intro entry member
  simp only [AirbenderProgram.program, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> rfl

private theorem standalone_subset : AirbenderNative.touched ⊆ standaloneDomain := by
  intro cell member
  simp only [AirbenderNative.touched, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact ExternalBoundary.Initialization.Proofs.all_registers
        (AirbenderInitialization.standaloneWindows.selection Proofs.standalone_geometry) _
    | exact AirbenderInitialization.standalone_clint_member

theorem native_accepted : Trace.Accepted standaloneTrace :=
  AirbenderNative.accepted _ _
    (ExternalBoundary.Initialization.Proofs.cells_distinct
      (AirbenderInitialization.standaloneWindows.selection Proofs.standalone_geometry)) standalone_subset

theorem standalone_profile :
    PooledProfile standaloneTrace standalone.layout Proofs.standalone_geometry
      AirbenderInitialization.standaloneWindows AirbenderProgram.before AirbenderNative.pooledProgram := by
  refine {
    ordinary := fun address _ => ordinaryWordAddress_airbender address
    configuration := AirbenderProgram.configuration
    landingPadDisabled := ⟨0, ?_, rfl⟩
    code := ?_
    loads := ?_
    programImage := ⟨[0, 4, 8, 12], pooled_program_image⟩
    profile := AirbenderProgram.initial_profile _ AirbenderInitialization.standalone_profile.profile
    initialBoundary := rfl
    physicalImage := ⟨standalonePhysical, Classical.choose_spec standalone_image_exists, rfl⟩
    subwordSetup := rfl
    verifierBoundary := ⟨⟨16, (20, 0)⟩, ⟨rfl, native_accepted.states⟩⟩ }
  · simp [AirbenderProgram.before, wordWriteState, AirbenderInitialization.before,
      Std.ExtDHashMap.get?_insert]
  · intro entry member
    simp only [AirbenderNative.pooledProgram, AirbenderProgram.program,
      List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> constructor <;> decide
  · intro entry member imm rs1
    simp only [AirbenderNative.pooledProgram, AirbenderProgram.program,
      List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> intro impossible <;> cases impossible

/-- The inline initialization profile is inhabited for the same real four-word
program, using windows1/6 and physical ROM bytes separately from RAM shadow. -/
noncomputable def unifiedBase : UnifiedTrace babyBearModulus :=
  { AirbenderInitialization.unifiedBase with rom := UnifiedReduced.Setup.table AirbenderProgram.before }

theorem unified_profile :
    UnifiedProfile unifiedBase unified.layout Proofs.unified_geometry
      AirbenderInitialization.unifiedWindows AirbenderProgram.before unifiedProgram := by
  refine {
    profile := AirbenderProgram.initial_profile _ AirbenderInitialization.unified_profile.profile
    image := ⟨unifiedPhysical, Classical.choose_spec unified_image_exists⟩
    initialPC := rfl
    programImage := ⟨[0, 4, 8, 12], unified_program_image⟩
    setup := rfl
    code := ?_
    configuration := AirbenderProgram.configuration
    ordinary := fun address _ => ordinaryWordAddress_airbender address
    landingPadDisabled := ?_
    loads := ?_ }
  · intro entry member
    simp only [unifiedProgram, AirbenderProgram.program, List.map_cons, List.map_nil,
      List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> constructor <;> decide
  · rintro ⟨entry, member, imm, rs1, rd, impossible⟩
    simp only [unifiedProgram, AirbenderProgram.program, List.map_cons, List.map_nil,
      List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> cases impossible
  · intro entry member imm rs1
    simp only [unifiedProgram, AirbenderProgram.program, List.map_cons, List.map_nil,
      List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> intro impossible <;> cases impossible

/-- Actual imported standalone teardown columns for the only changed RAM word:
set0's word8388608 (byte33554432), final refresh clock17 and value7. -/
def standaloneRaw : Raw babyBearModulus := fun row column =>
  if row = 8388608 ∧ column = 2 then 17
  else if row = 8388608 ∧ column = 0 then 7 else 0

def terminalRegisters : List (MemoryToken babyBearModulus) :=
  ExternalBoundary.Initialization.registers.map AirbenderNative.final

private def embed : ZMod babyBearModulus →+* ZMod babyBearModulus := RingHom.id _
private def weights : Fin 6 → ZMod babyBearModulus := fun _ => 0

/-- Gate acceptance covers every row of the actual imported GKR graph. The
separate exact token matching, proved below, carries values independently of
this permissible unit challenge; sampled products are never used as a multiset proof. -/
theorem initialization_accepted : Initialization.Accepted standalone
    (parametersFor embed 0 weights AirbenderInitialization.standaloneWindows)
    standaloneRaw (fun _ _ => 1) := by
  intro row gate _
  cases gate <;> simp [Gate.Sat, Leaf.factor, parametersFor, embed, weights]

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

private theorem standalone_terminal_token (set : Fin standalone.layout.columns.size)
    (row : Fin standalone.layout.rows) :
    (Leaf.mk .terminal set.val standalone.layout.columns[set]).token standalone.layout
      (parametersFor embed 0 weights AirbenderInitialization.standaloneWindows) standaloneRaw row.val =
    AirbenderNative.final (ExternalBoundary.Initialization.cell
      (geometry := Proofs.standalone_geometry.public)
      (AirbenderInitialization.standaloneWindows.index set, row)) := by
  rw [Proofs.terminal_token standalone.layout Proofs.standalone_geometry
    AirbenderInitialization.standaloneWindows embed 0 weights standaloneRaw set row]
  have encoded : ExternalBoundary.Initialization.cell
      (geometry := Proofs.standalone_geometry.public)
      (AirbenderInitialization.standaloneWindows.index ⟨0, by decide⟩, ⟨8388608, by decide⟩) =
        Cell.ram 33554432 := by
    change Cell.ram (BitVec.ofNat 32 (4 * (0 * 16777216 + 8388608))) = Cell.ram 33554432
    norm_num
    decide +kernel
  have coordinateMatch := selected_cell_iff Proofs.standalone_geometry
    AirbenderInitialization.standaloneWindows set ⟨0, by decide⟩ row ⟨8388608, by decide⟩
  rw [encoded] at coordinateMatch
  have same : (ExternalBoundary.Initialization.cell
      (geometry := Proofs.standalone_geometry.public)
      (AirbenderInitialization.standaloneWindows.index set, row) = Cell.ram 33554432) ↔
        set.val = 0 ∧ row.val = 8388608 := by
    simpa only [Fin.ext_iff] using coordinateMatch
  have different (index : BitVec 5) : ExternalBoundary.Initialization.cell
      (geometry := Proofs.standalone_geometry.public)
      (AirbenderInitialization.standaloneWindows.index set, row) ≠ Cell.register index := by
    simp [ExternalBoundary.Initialization.cell]
  simp only [AirbenderNative.final, different, if_false, same]
  have position := row.isLt
  change row.val < 16777216 at position
  have setBound := set.isLt
  change set.val < 8 at setBound
  fin_cases set <;>
    (by_cases chosen : row.val = 8388608 <;>
      simp [AirbenderNative.old, standaloneRaw, standalone, Cell.initialToken, chosen,
        Arithmetic.Word.ofBitVec, babyBearModulus])
  all_goals first | rfl | exact ⟨rfl, rfl⟩

private theorem terminal_ram :
    ramTokens standalone.layout
      (parametersFor embed 0 weights AirbenderInitialization.standaloneWindows) standaloneRaw .terminal =
    ((((AirbenderInitialization.standaloneWindows.selection Proofs.standalone_geometry).indices.product
      (List.finRange standalone.layout.rows)).map
        (ExternalBoundary.Initialization.cell (geometry := Proofs.standalone_geometry.public))).map
          AirbenderNative.final) := by
  simp only [ramTokens, Layout.leaves, Windows.selection,
    List.product, List.flatMap_map, List.map_map, Function.comp_def]
  rw [List.map_flatMap]
  simp only [List.map_map, Function.comp_def]
  apply List.flatMap_congr
  intro set _
  apply List.map_congr_left
  intro row _
  exact standalone_terminal_token set row

/-- The actual imported initialization/teardown boundary is exactly the same
full-domain accepted native trace, including its disputed RAM word. -/
theorem native_boundary :
    withBoundary standaloneTrace standalone.layout
      (parametersFor embed 0 weights AirbenderInitialization.standaloneWindows)
      standaloneRaw terminalRegisters = standaloneTrace := by
  simp only [withBoundary, standaloneTrace, AirbenderNative.trace,
    Proofs.initial_ram_tokens standalone.layout Proofs.standalone_geometry,
    terminal_ram, terminalRegisters, standaloneDomain, cells,
    ExternalBoundary.Initialization.cells, ROMView.nativeBootImage, List.map_append]
  rfl

/-- Concrete application of the original ordinary endpoint theorem, using
actual accepted GKR initialization, actual native rows, actual decoding and
exact logical matching. It does not invoke FullCSR.CodeProfile.ram. -/
theorem native_execution :
    Realizes (PooledStep AirbenderNative.pooledProgram) standaloneTrace AirbenderProgram.before
      standaloneDomain (ROMView.token AirbenderProgram.before) := by
  have result := Initialization.standalone_execution AirbenderInitialization.standaloneWindows
    embed 0 weights standaloneRaw (fun _ _ => 1) terminalRegisters standalone_profile
    initialization_accepted
    (by rw [native_boundary]; exact native_accepted)
    (by rw [native_boundary]; exact AirbenderNative.decoded _ _)
  rw [native_boundary] at result
  exact result.2

private theorem terminal_zero (layout : Layout) (windows : Windows layout) :
    ramTokens layout (parametersFor embed 0 weights windows) (fun _ _ => 0) .terminal =
      ramTokens layout (parametersFor embed 0 weights windows) (fun _ _ => 0) .initial := by
  simp only [ramTokens, Layout.leaves, List.flatMap_map]
  apply List.flatMap_congr
  intro set _
  apply List.map_congr_left
  intro row _
  simp [Leaf.token, Leaf.time, Leaf.value]

/-- Actual inline initialization/teardown admits every selected row, including
CLINT/SIG RAM, with the concrete installed program and the zero-step
initial endpoint. The nonempty four-instruction execution is proved above for
the standalone native trace. -/
theorem unified_initial_application :
    Realizes (UnifiedReduced.Step unifiedProgram)
      (withBoundary unifiedBase unified.layout
        (parametersFor embed 0 weights AirbenderInitialization.unifiedWindows)
        (fun _ _ => 0) (ROMView.nativeBootImage ExternalBoundary.Initialization.registers))
      AirbenderProgram.before unifiedDomain (ROMView.token AirbenderProgram.before) := by
  let boundary := withBoundary unifiedBase unified.layout
    (parametersFor embed 0 weights AirbenderInitialization.unifiedWindows)
    (fun _ _ => 0) (ROMView.nativeBootImage ExternalBoundary.Initialization.registers)
  have gates : Initialization.Accepted unified
      (parametersFor embed 0 weights AirbenderInitialization.unifiedWindows)
      (fun _ _ => 0) (fun _ _ => 1) := by
    intro row gate _
    cases gate <;> simp [Gate.Sat, Leaf.factor, parametersFor, embed, weights]
  have accepted : Trace.Accepted boundary := by
    constructor
    · intro row member; cases member
    · intro row member; cases member
    · exact List.Perm.refl _
    · change ((ROMView.nativeBootImage ExternalBoundary.Initialization.registers ++
          ramTokens unified.layout (parametersFor embed 0 weights AirbenderInitialization.unifiedWindows)
            (fun _ _ => 0) .initial) ++ []).Perm
        ((ROMView.nativeBootImage ExternalBoundary.Initialization.registers ++
          ramTokens unified.layout (parametersFor embed 0 weights AirbenderInitialization.unifiedWindows)
            (fun _ _ => 0) .terminal) ++ [])
      simp only [List.append_nil]
      rw [terminal_zero]
  exact (Initialization.unified_boundary_execution (by decide) (by decide) (by decide)
    AirbenderInitialization.unifiedWindows embed 0 weights (fun _ _ => 0) (fun _ _ => 1)
    (ROMView.nativeBootImage ExternalBoundary.Initialization.registers) unified_profile gates accepted
    (by intro row member; cases member)).2

end Tests.AirbenderApplicability
