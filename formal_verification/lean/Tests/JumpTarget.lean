import Tests.JumpLink
import Airbender.Review.Trace.Families.JumpBranchSlt.Targets

namespace Tests.JumpTarget
open Airbender Trace Verification Arithmetic Reference.RiscV.Sail
open Tests.JumpLink (words setup)

/-- Logical original-byte JALR fixture. The aliased rd read consumes rs1's native
    readonly refresh. No new arbitrary-program native export is claimed. -/
def assignment (i : Nat) : ZMod mersenne31Modulus :=
  if i = 57 then 4 else Tests.JumpLink.jalr i

def nativeRow : Row mersenne31Modulus JumpBranchSltFamily := ⟨.jumpBranchSlt,assignment⟩
private def cell (register time value : Nat) : MemoryToken mersenne31Modulus :=
  ⟨Nat.pair 0 (Nat.pair register 0), (time, 0), Nat.pair value 0⟩
def trace : Data mersenne31Modulus JumpBranchSltFamily where
  rows := [nativeRow]
  rom := ()
  initial := ⟨(4,0),(4,0)⟩
  terminal := ⟨(264,0),(8,0)⟩
  initialMemory := [cell 0 0 0,cell 1 0 257]
  terminalMemory := [cell 0 5 0,cell 1 6 8]
def before : State :=
  { Tests.JumpLink.before with regs := (Std.ExtDHashMap.emptyWithCapacity
    |>.insert .x1 (257 : BitVec 32) |>.insert .PC (4 : BitVec 32)) }

private theorem public_words (i : Fin 3) :
    (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read before =
      .ok words[i.val] before := by
  fin_cases i <;>
    simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
      EStateM.run, get, getThe, MonadStateOf.get, bind, pure, EStateM.bind,
      EStateM.get, EStateM.pure, before, Tests.JumpLink.before, words, Std.ExtHashMap.getElem_insert]

set_option maxRecDepth 32768 in
theorem program_image : JumpBranchSlt.sparseDecoderSetupImage before 3 20 = some setup := by
  have slots : ([0,4,8] : List (BitVec 32)).mapM
      (programSlotWith JumpBranchSlt.decoderFields before) = some setup.slots := by
    simp only [List.mapM_cons, List.mapM_nil, programSlotWith,
      show (Cell.ram 0).read before = .ok (0xffdff0ef : BitVec 32) before from public_words ⟨0, by decide⟩,
      show (Cell.ram 4).read before = .ok (0x008080e7 : BitVec 32) before from public_words ⟨1, by decide⟩,
      show (Cell.ram 8).read before = .ok (0x0080006f : BitVec 32) before from public_words ⟨2, by decide⟩,
      bind, Option.bind]
    cbv
  change (([0,4,8] : List (BitVec 32)).mapM (programSlotWith JumpBranchSlt.decoderFields before)).bind
    (fun entries => some (SparseDecoderSetup.mk entries 1048573)) = some setup
  rw [slots]
  rfl

theorem native_constraints :
    FlatOperation.ConstraintsHoldFlat (environment assignment) JumpBranchSlt.importedConstraints := by
  simp [JumpBranchSlt.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, assignment, Tests.JumpLink.jalr, Tests.JumpControl.assignment]
  repeat' apply And.intro
  all_goals first | (apply range16_contains; decide) |
    (apply timestamp19_contains; decide) | try decide
  all_goals
    simp only [Lookup.Contains, fixed3, Table.toRaw, conditionalControlTable,
      jumpCleanupTable, Table.fromStatic, StaticTable.toTable, ProvableType.fromElements,
      Expression.eval, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, assignment, Tests.JumpLink.jalr, Tests.JumpControl.assignment]
    solve
    | refine ⟨⟨0, by decide⟩, ?_⟩
      norm_num [conditionalControlRow, controlFlag]
    | refine ⟨⟨265, by decide⟩, ?_⟩
      norm_num [jumpCleanupRow]

theorem accepted : Accepted trace := by
  constructor
  · intro row member
    have same : row = nativeRow := by simpa [trace] using member
    subst row
    exact native_constraints
  · intro row member
    have same : row = nativeRow := by simpa [trace] using member
    subst row
    decide
  · change [trace.initial,nativeRow.finish].Perm [trace.terminal,nativeRow.start]
    have start : nativeRow.start = trace.initial := rfl
    have finish : nativeRow.finish = trace.terminal := rfl
    rw [start,finish]
    exact List.Perm.swap _ _ []
  · change ([cell 0 0 0,cell 1 0 257,cell 1 4 257,cell 0 5 0,cell 1 6 8]).Perm
      [cell 0 5 0,cell 1 6 8,cell 1 0 257,cell 0 0 0,cell 1 4 257]
    decide +kernel

theorem public_inputs : ImageBoundary trace before [.register 0,.register 1] := by
  have zero : (Cell.register 0).read before = .ok (0 : BitVec 32) before := rfl
  have old : (Cell.register 1).read before = .ok (257 : BitVec 32) before := by
    apply Reference.RiscV.Sail.read_register
    simp [before,Std.ExtDHashMap.get?_insert]
  have pc : Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) before =
      .ok (4 : BitVec 32) before := by
    apply Reference.RiscV.Sail.read_register
    simp [before]
  constructor
  · decide
  · simp only [initialImage,List.mapM_cons,List.mapM_nil,zero,old]
    rfl
  · rw [initialState,pc]
    rfl

theorem decoded : JumpBranchSlt.Decoded trace setup := by
  intro row member
  have same : row = nativeRow := by simpa [trace] using member
  subst row
  refine ⟨⟨1,by decide⟩,?_⟩
  decide +kernel

/-- Original byte decoding, public source 257 and actual native matching derive
    the JALR target 264, clearing bit zero of 265. Source and destination alias. -/
theorem initialized_jalr_target :
    (Word.mk (assignment 13).val (assignment 14).val).toBitVec = 264 ∧
    (Word.mk (assignment 13).val (assignment 14).val).toBitVec.toNat % 4 = 0 := by
  have target := JumpBranchSlt.public_jump_targets program_image public_inputs accepted decoded
    nativeRow (by simp [trace]) (by decide)
  exact ⟨target.1.trans (by decide),target.2⟩

/-- The actually exported JAL -4 target wraps to 0xfffffffc from public PC zero. -/
theorem initialized_negative_jal :
    (Word.mk (Tests.ControlHistory.assignment false 13).val
      (Tests.ControlHistory.assignment false 14).val).toBitVec = 0xfffffffc := by
  have target := JumpBranchSlt.public_jump_targets Tests.ControlValues.decoder_image
    Tests.ControlHistory.public_inputs Tests.ControlHistory.accepted Tests.ControlValues.decoded
    (Tests.ControlHistory.nativeRow false) (by simp [Tests.ControlHistory.trace]) (by decide)
  exact target.1.trans (by decide)

theorem zero_destination_target :
    (Word.mk (Tests.JumpLink.zero 13).val (Tests.JumpLink.zero 14).val).toBitVec = 16 := by
  obtain ⟨selected,other⟩ := JumpBranchSlt.Proofs.jump_identity false Tests.JumpLink.zero_native (by decide)
  have target := JumpBranchSlt.Proofs.jump_pc false Tests.JumpLink.zero_native selected other
    (base := ⟨8,0⟩) (offset := ⟨8,0⟩) ⟨by decide,by decide,by decide,by decide⟩
    (by constructor <;> decide) (by constructor <;> decide) (by intro; constructor <;> decide)
  exact target.1.trans (by decide)

/-- Full native local row: target addition wraps from 0xfffffffc plus eight to
    four. This local regression is separate from initialized/public decoding. -/
theorem wrapped_target :
    (Word.mk (Tests.JumpLink.wrap 13).val (Tests.JumpLink.wrap 14).val).toBitVec = 4 := by
  obtain ⟨selected,other⟩ := JumpBranchSlt.Proofs.jump_identity false Tests.JumpLink.wrap_native (by decide)
  have target := JumpBranchSlt.Proofs.jump_pc false Tests.JumpLink.wrap_native selected other
    (base := ⟨65532,65535⟩) (offset := ⟨8,0⟩) ⟨by decide,by decide,by decide,by decide⟩
    (by constructor <;> decide) (by constructor <;> decide) (by intro; constructor <;> decide)
  exact target.1.trans (by decide)

def misaligned (i : Nat) : ZMod mersenne31Modulus :=
  if i = 22 ∨ i = 40 then 259 else if i = 42 then 267 else if i = 47 then 1
  else Tests.JumpLink.jalr i

theorem misaligned_cleanup_valid :
    jumpCleanupTable.Contains #[] (#v[misaligned 42,misaligned 47,misaligned 48] :
      Vector (ZMod mersenne31Modulus) 3) := by
  refine ⟨⟨267,by decide⟩,?_⟩
  norm_num [jumpCleanupTable,Table.fromStatic,StaticTable.toTable,ProvableType.fromElements,
    jumpCleanupRow,misaligned,Tests.JumpLink.jalr,Tests.JumpControl.assignment]

/-- The cleanup table itself accepts 267→264, but native bit-one alignment
    rejects that JALR target rather than silently rounding a two-byte address. -/
theorem misaligned_jalr_rejected :
    ¬FlatOperation.ConstraintsHoldFlat (environment misaligned) JumpBranchSlt.importedConstraints := by
  intro native
  have align := assertion_of_holds native ⟨26,by rw [JumpBranchSlt.Proofs.constraint_count]; decide⟩
  norm_num [JumpBranchSlt.importedConstraints,FlatOperation.constraints,Expression.eval,environment,
    misaligned,Tests.JumpLink.jalr,Tests.JumpControl.assignment] at align

end Tests.JumpTarget
