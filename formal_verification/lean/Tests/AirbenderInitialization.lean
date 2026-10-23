import Tests.Platform
import Airbender.Proofs.BabyBear
import Airbender.Proofs.Sail.ZeroMemory
import Airbender.Proofs.Sail.CheckedMemory
import Airbender.Proofs.Initialization.NativeGeometry
import Airbender.Review.Helpers.Context.InitializationInputs
import Airbender.Review.Helpers.Context.InitializationUnifiedInputs
import Airbender.Proofs.VerifierBoundary

namespace Tests.AirbenderInitialization
open Airbender Airbender.Initialization Airbender.Trace
open Airbender.Reference Airbender.Reference.RiscV.Sail
open _root_.Sail.ArchSem
set_option warningAsError true
set_option Elab.async false

local instance : MemoryPlatform SailRV32.exception := Tests.upstreamPlatform.airbender

private def attributes : SailRV32.PMA :=
  { (default : SailRV32.PMA) with readable := true, writable := true, executable := true }

/-- Public all-zero GPR boot data, with actual Machine/PMP/PMA configuration. -/
noncomputable def before : State :=
  { (default : State) with
    regs := (Std.ExtDHashMap.emptyWithCapacity :
      Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType)
      |>.insert .mstatus 0 |>.insert .cur_privilege .Machine |>.insert .misa 0x40000100
      |>.insert .senvcfg 0 |>.insert .menvcfg 0x10
      |>.insert .pmpcfg_n (Vector.replicate 64 0)
      |>.insert .pmpaddr_n (Vector.replicate 64 0)
      |>.insert .pma_regions [rv32Region attributes]
      |>.insert .mhartid 0 |>.insert .htif_tohost_base none
      |>.insert .mseccfg 0 |>.insert .PC 0
      |>.insert .x1 0
      |>.insert .x2 0
      |>.insert .x3 0
      |>.insert .x4 0
      |>.insert .x5 0
      |>.insert .x6 0
      |>.insert .x7 0
      |>.insert .x8 0
      |>.insert .x9 0
      |>.insert .x10 0
      |>.insert .x11 0
      |>.insert .x12 0
      |>.insert .x13 0
      |>.insert .x14 0
      |>.insert .x15 0
      |>.insert .x16 0
      |>.insert .x17 0
      |>.insert .x18 0
      |>.insert .x19 0
      |>.insert .x20 0
      |>.insert .x21 0
      |>.insert .x22 0
      |>.insert .x23 0
      |>.insert .x24 0
      |>.insert .x25 0
      |>.insert .x26 0
      |>.insert .x27 0
      |>.insert .x28 0
      |>.insert .x29 0
      |>.insert .x30 0
      |>.insert .x31 0
    mem := zeroMemory (2 ^ 30) }

theorem configuration : FlatMemoryConfiguration before := by
  constructor
  · simp [before, Std.ExtDHashMap.get?_insert]
  · simp [before, Std.ExtDHashMap.get?_insert]
  · exact ⟨0x40000100, by simp [before, Std.ExtDHashMap.get?_insert]⟩
  · exact ⟨0, by simp [before, Std.ExtDHashMap.get?_insert]⟩
  · exact ⟨0x10, by simp [before, Std.ExtDHashMap.get?_insert]⟩
  · simp [before, Std.ExtDHashMap.get?_insert]
  · exact ⟨Vector.replicate 64 0, by simp [before, Std.ExtDHashMap.get?_insert]⟩
  · exact ⟨attributes, by simp [before, Std.ExtDHashMap.get?_insert], rfl, rfl, rfl⟩
  · exact ⟨0, by simp [before, Std.ExtDHashMap.get?_insert]⟩
  · simp [before, Std.ExtDHashMap.get?_insert]; rfl

theorem registers_zero (index : BitVec 5) :
    (Cell.register index).read before = .ok 0 before := by
  have small := index.isLt
  have numeric : ∀ number : Nat, number < 32 →
      (Cell.register (BitVec.ofNat 5 number)).read before = .ok 0 before := by
    intro number bound
    interval_cases number
    all_goals first | rfl | (apply read_register; simp [before, Std.ExtDHashMap.get?_insert])
  simpa using numeric index.toNat small

/-- Full native domains remain symbolic; only the small window-index set is
instantiated. No list of millions of cells is evaluated by these proofs. -/
def standaloneWindows : Windows standalone.layout where
  index set := ⟨set.val, by
    have small := set.isLt
    change set.val < 8 at small
    change set.val < 64
    omega⟩
  unique := by
    intro left right same
    exact Fin.ext (congrArg (fun index : Fin standalone.layout.slots => index.val) same)

def unifiedWindows : Windows unified.layout where
  index set := ⟨if set.val = 0 then 1 else 6, by
    change (if set.val = 0 then 1 else 6) < 128
    split <;> decide⟩
  unique := by
    intro left right same
    apply Fin.ext
    have raw := congrArg Fin.val same
    have lb := left.isLt
    have rb := right.isLt
    change left.val < 2 at lb
    change right.val < 2 at rb
    change (if left.val = 0 then 1 else 6) = (if right.val = 0 then 1 else 6) at raw
    by_cases lz : left.val = 0 <;> by_cases rz : right.val = 0 <;>
      simp [lz, rz] at raw <;> omega

private theorem selected_word_bound {layout : Layout} (geometry : Geometry layout)
    (windows : Windows layout)
    (extent : ∀ set, 4 * ((windows.index set).val + 1) * layout.rows ≤ 2 ^ 30)
    {address : BitVec 32} (member : Cell.ram address ∈ cells geometry windows) :
    address.toNat + 4 ≤ 2 ^ 30 := by
  change Cell.ram address ∈ ExternalBoundary.Initialization.registers ++
    (((List.finRange layout.columns.size).map windows.index).product
      (List.finRange layout.rows)).map (ExternalBoundary.Initialization.cell
        (geometry := geometry.public)) at member
  rcases List.mem_append.mp member with register | ram
  · obtain ⟨index, _, impossible⟩ := List.mem_map.mp register
    cases impossible
  · obtain ⟨⟨window, row⟩, present, same⟩ := List.mem_map.mp ram
    obtain ⟨set, _, windowEq⟩ := List.mem_map.mp (List.mem_product.mp present).1
    have addressBound := ExternalBoundary.Initialization.Proofs.address_bound
      (geometry := geometry.public) (window, row)
    change Cell.ram (BitVec.ofNat 32 (4 * (window.val * layout.rows + row.val))) =
      Cell.ram address at same
    change 4 * (window.val * layout.rows + row.val) < 2 ^ 32 at addressBound
    have encoded := Cell.ram.inj same
    rw [← encoded, BitVec.toNat_ofNat, Nat.mod_eq_of_lt addressBound]
    have endBound := extent set
    rw [windowEq] at endBound
    have rowBound := row.isLt
    nlinarith

private theorem standalone_extent (set : Fin standalone.layout.columns.size) :
    4 * ((standaloneWindows.index set).val + 1) * standalone.layout.rows ≤ 2 ^ 30 := by
  have small := set.isLt
  change set.val < 8 at small
  change 4 * (set.val + 1) * 16777216 ≤ 1073741824
  omega

private theorem unified_extent (set : Fin unified.layout.columns.size) :
    4 * ((unifiedWindows.index set).val + 1) * unified.layout.rows ≤ 2 ^ 30 := by
  change 4 * ((if set.val = 0 then 1 else 6) + 1) * 8388608 ≤ 1073741824
  split <;> decide

private theorem initial_profile {layout : Layout} (geometry : Geometry layout)
    (windows : Windows layout)
    (extent : ∀ set, 4 * ((windows.index set).val + 1) * layout.rows ≤ 2 ^ 30) :
    InitialProfile before (cells geometry windows) := by
  refine ⟨?_, registers_zero, ?_⟩
  · apply read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  · intro address member _
    exact zeroMemory_word rfl (selected_word_bound geometry windows extent member)

private theorem initial_image {layout : Layout} (geometry : Geometry layout)
    (windows : Windows layout)
    (extent : ∀ set, 4 * ((windows.index set).val + 1) * layout.rows ≤ 2 ^ 30) :
    initialImage (p := babyBearModulus) before (cells geometry windows) =
      some (ROMView.nativeBootImage (cells geometry windows)) := by
  have reads : ∀ cell ∈ cells geometry windows, cell.read before = .ok 0 before := by
    intro cell member
    cases cell with
    | register index => exact registers_zero index
    | ram address => exact zeroMemory_word rfl (selected_word_bound geometry windows extent member)
  generalize cells geometry windows = domain at *
  revert reads
  induction domain with
  | nil => intro _; rfl
  | cons cell rest ih =>
    intro reads
    have current := reads cell (List.mem_cons_self)
    have tail := ih (fun other member => reads other (List.mem_cons_of_mem cell member))
    simp only [initialImage, List.mapM_cons, current, bind, Option.bind,
      ROMView.nativeBootImage, List.map_cons] at tail ⊢
    rw [tail]
    rfl

private theorem selected_member {layout : Layout} (geometry : Geometry layout)
    (windows : Windows layout) (set : Fin layout.columns.size) (row : Fin layout.rows) :
    ExternalBoundary.Initialization.cell (geometry := geometry.public) (windows.index set, row) ∈
      cells geometry windows := by
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨(windows.index set, row), ?_, rfl⟩
  exact List.mem_product.mpr
    ⟨List.mem_map.mpr ⟨set, List.mem_finRange _, rfl⟩, List.mem_finRange _⟩

/-- Transport only the symbolic member's cell argument. Keeping that transport
inside the generic theorem prevents reduction of a closed full native domain
while elaborating a concrete byte address. -/
private theorem selected_member_eq {layout : Layout} (geometry : Geometry layout)
    (windows : Windows layout) (set : Fin layout.columns.size) (row : Fin layout.rows)
    (target : Cell)
    (encoded : ExternalBoundary.Initialization.cell (geometry := geometry.public)
      (windows.index set, row) = target) : target ∈ cells geometry windows :=
  Eq.mp (congrArg (fun cell : Cell => cell ∈ cells geometry windows) encoded)
    (selected_member geometry windows set row)

theorem standalone_clint_member :
    Cell.ram 33554432 ∈ cells Proofs.standalone_geometry standaloneWindows :=
  selected_member_eq Proofs.standalone_geometry standaloneWindows
    ⟨0, by decide⟩ ⟨8388608, by decide⟩ (.ram 33554432) (by
      change Cell.ram (BitVec.ofNat 32 (4 * (0 * 16777216 + 8388608))) = Cell.ram 33554432
      norm_num
      decide +kernel)

theorem standalone_sig_member :
    Cell.ram 201326592 ∈ cells Proofs.standalone_geometry standaloneWindows :=
  selected_member_eq Proofs.standalone_geometry standaloneWindows
    ⟨3, by decide⟩ ⟨0, by decide⟩ (.ram 201326592) (by
      change Cell.ram (BitVec.ofNat 32 (4 * (3 * 16777216 + 0))) = Cell.ram 201326592
      norm_num
      decide +kernel)

theorem unified_clint_member :
    Cell.ram 33554432 ∈ cells Proofs.unified_geometry unifiedWindows :=
  selected_member_eq Proofs.unified_geometry unifiedWindows
    ⟨0, by decide⟩ ⟨0, by decide⟩ (.ram 33554432) (by
      change Cell.ram (BitVec.ofNat 32 (4 * (1 * 8388608 + 0))) = Cell.ram 33554432
      norm_num
      decide +kernel)

theorem unified_sig_member :
    Cell.ram 201326592 ∈ cells Proofs.unified_geometry unifiedWindows :=
  selected_member_eq Proofs.unified_geometry unifiedWindows
    ⟨1, by decide⟩ ⟨0, by decide⟩ (.ram 201326592) (by
      change Cell.ram (BitVec.ofNat 32 (4 * (6 * 8388608 + 0))) = Cell.ram 201326592
      norm_num
      decide +kernel)

noncomputable def pooledBase : PooledTrace babyBearModulus where
  rows := []
  rom := ⟨ROM.table (cells Proofs.standalone_geometry standaloneWindows)
      (ROMView.nativeBootImage (cells Proofs.standalone_geometry standaloneWindows)),
    Verification.subwordTable (ROM.words before)⟩
  initial := PCState.boundary 0 (4, 0)
  terminal := PCState.boundary 0 (4, 0)
  initialMemory := []
  terminalMemory := []

noncomputable def unifiedBase : UnifiedTrace babyBearModulus where
  rows := []
  rom := UnifiedReduced.Setup.table before
  initial := PCState.boundary 0 (4, 0)
  terminal := PCState.boundary 0 (4, 0)
  initialMemory := []
  terminalMemory := []

/-- The actual standalone domain includes window0 and admits a public all-zero
boot state under Airbender routing. The program is empty at this profile gate. -/
theorem standalone_profile :
    PooledProfile pooledBase standalone.layout Proofs.standalone_geometry
      standaloneWindows before [] := by
  refine {
    ordinary := fun address _ => ordinaryWordAddress_airbender address
    configuration := configuration
    landingPadDisabled := ⟨0, ?_, rfl⟩
    code := by simp
    loads := by simp [NoDiscardedLoads]
    programImage := ⟨[], rfl⟩
    profile := initial_profile _ _ standalone_extent
    initialBoundary := rfl
    physicalImage := ⟨_, initial_image _ _ standalone_extent, rfl⟩
    subwordSetup := rfl
    verifierBoundary := ?_ }
  · simp [before, Std.ExtDHashMap.get?_insert]
  · exact ⟨⟨0, (4, 0)⟩, ⟨rfl, List.Perm.refl _⟩⟩

/-- The actual inline domain selects windows1/6, containing CLINT/SIG
addresses, and admits the same explicit native public boot state. -/
theorem unified_profile :
    UnifiedProfile unifiedBase unified.layout Proofs.unified_geometry
      unifiedWindows before [] := by
  exact {
    profile := initial_profile _ _ unified_extent
    image := ⟨_, initial_image _ _ unified_extent⟩
    initialPC := rfl
    programImage := ⟨[], rfl⟩
    setup := rfl
    code := by simp
    configuration := configuration
    ordinary := fun address _ => ordinaryWordAddress_airbender address
    landingPadDisabled := by simp
    loads := by simp }

end Tests.AirbenderInitialization
