import Tests.ControlValues

namespace Tests.JumpLink
open Airbender Trace Verification Arithmetic Reference.RiscV.Sail

/-- Separate original-byte logical fixture; only the existing first word has a
    native export certificate. No new arbitrary-program Rust refinement is claimed. -/
def words : Vector (BitVec 32) 3 := #v[0xffdff0ef, 0x008080e7, 0x0080006f]
def before : State :=
  { (default : State) with mem := ((Std.ExtHashMap.emptyWithCapacity : Std.ExtHashMap Nat (BitVec 8))
    |>.insert 0 0xef |>.insert 1 0xf0 |>.insert 2 0xdf |>.insert 3 0xff
    |>.insert 4 0xe7 |>.insert 5 0x80 |>.insert 6 0x80 |>.insert 7 0x00
    |>.insert 8 0x6f |>.insert 9 0x00 |>.insert 10 0x80 |>.insert 11 0x00) }
def jalrEntry : JumpBranchSlt.ProgramEntry :=
  ⟨4, 0x008080e7, .JALR (8, .Regidx 1, .Regidx 1), ⟨(),1,0,1,⟨8,0⟩,2,0⟩⟩
def zeroEntry : JumpBranchSlt.ProgramEntry :=
  ⟨8, 0x0080006f, .JAL (8, .Regidx 0), ⟨(),0,0,0,⟨8,0⟩,1,0⟩⟩
def setup : SparseDecoderSetup Unit :=
  ⟨[some JumpBranchSlt.NativeSetup.jalEntry, some jalrEntry, some zeroEntry],1048573⟩

private theorem fixture_words (i : Fin 3) :
    (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read before =
      .ok words[i.val] before := by
  fin_cases i <;>
    simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
      EStateM.run, get, getThe, MonadStateOf.get, bind, pure, EStateM.bind,
      EStateM.get, EStateM.pure, before, words, Std.ExtHashMap.getElem_insert]

set_option maxRecDepth 32768 in
theorem program_image : JumpBranchSlt.sparseDecoderSetupImage before 3 20 = some setup := by
  have slots : ([0,4,8] : List (BitVec 32)).mapM
      (programSlotWith JumpBranchSlt.decoderFields before) = some setup.slots := by
    simp only [List.mapM_cons, List.mapM_nil, programSlotWith,
      show (Cell.ram 0).read before = .ok (0xffdff0ef : BitVec 32) before from fixture_words ⟨0, by decide⟩,
      show (Cell.ram 4).read before = .ok (0x008080e7 : BitVec 32) before from fixture_words ⟨1, by decide⟩,
      show (Cell.ram 8).read before = .ok (0x0080006f : BitVec 32) before from fixture_words ⟨2, by decide⟩,
      bind, Option.bind]
    cbv
  change (([0,4,8] : List (BitVec 32)).mapM (programSlotWith JumpBranchSlt.decoderFields before)).bind
    (fun entries => some (SparseDecoderSetup.mk entries 1048573)) = some setup
  rw [slots]
  rfl

/-- Odd JALR source 257 plus eight cleans to 264; its link is PC four plus four.
    Source/destination aliases retain the same old value locally. -/
def jalr (i : Nat) : ZMod mersenne31Modulus :=
  if i = 0 then 4 else if i = 5 ∨ i = 18 then 1 else if i = 12 then 2
  else if i = 17 then 0 else if i = 22 ∨ i = 40 then 257
  else if i = 26 ∨ i = 38 then 8 else if i = 30 then 268435456
  else if i = 13 ∨ i = 48 then 264 else if i = 42 then 265
  else Tests.JumpControl.assignment i

/-- Original JAL x0,+8 at PC eight retains raw link twelve but masks the write. -/
def zero (i : Nat) : ZMod mersenne31Modulus :=
  if i = 0 then 8 else if i = 7 ∨ i = 36 ∨ i = 38 then 0
  else if i = 8 then 1 else if i = 26 then 12 else if i = 30 then 894784853
  else if i = 13 ∨ i = 42 ∨ i = 48 then 16
  else Tests.JumpControl.assignment i

/-- Full local native row, separate from the bounded public decoder address
    domain: the unmasked x1 link wraps from 0xfffffffc to zero. -/
def wrap (i : Nat) : ZMod mersenne31Modulus :=
  if i = 0 then 65532 else if i = 1 then 65535
  else if i = 26 ∨ i = 30 ∨ i = 31 ∨ i = 38 then 0
  else if i = 28 ∨ i = 29 ∨ i = 35 ∨ i = 44 ∨ i = 49 ∨ i = 50 then 1
  else if i = 32 then 32767 else if i = 13 ∨ i = 42 ∨ i = 48 then 4
  else Tests.JumpControl.assignment i

theorem jalr_native :
    FlatOperation.ConstraintsHoldFlat (environment jalr) JumpBranchSlt.importedConstraints := by
  simp [JumpBranchSlt.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, jalr, Tests.JumpControl.assignment]
  repeat' apply And.intro
  all_goals first | (apply range16_contains; decide) |
    (apply timestamp19_contains; decide) | try decide
  all_goals
    simp only [Lookup.Contains, fixed3, Table.toRaw, conditionalControlTable,
      jumpCleanupTable, Table.fromStatic, StaticTable.toTable, ProvableType.fromElements,
      Expression.eval, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, jalr, Tests.JumpControl.assignment]
    solve
    | refine ⟨⟨0, by decide⟩, ?_⟩
      norm_num [conditionalControlRow, controlFlag]
    | refine ⟨⟨265, by decide⟩, ?_⟩
      norm_num [jumpCleanupRow]

theorem zero_native :
    FlatOperation.ConstraintsHoldFlat (environment zero) JumpBranchSlt.importedConstraints := by
  simp [JumpBranchSlt.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, zero, Tests.JumpControl.assignment]
  repeat' apply And.intro
  all_goals first | (apply range16_contains; decide) |
    (apply timestamp19_contains; decide) | try decide
  all_goals
    simp only [Lookup.Contains, fixed3, Table.toRaw, conditionalControlTable,
      jumpCleanupTable, Table.fromStatic, StaticTable.toTable, ProvableType.fromElements,
      Expression.eval, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, zero, Tests.JumpControl.assignment]
    solve
    | refine ⟨⟨0, by decide⟩, ?_⟩
      norm_num [conditionalControlRow, controlFlag]
    | refine ⟨⟨16, by decide⟩, ?_⟩
      norm_num [jumpCleanupRow]

theorem wrap_native :
    FlatOperation.ConstraintsHoldFlat (environment wrap) JumpBranchSlt.importedConstraints := by
  simp [JumpBranchSlt.importedConstraints, FlatOperation.ConstraintsHoldFlat, Expression.eval,
    environment, wrap, Tests.JumpControl.assignment]
  repeat' apply And.intro
  all_goals first | (apply range16_contains; decide) |
    (apply timestamp19_contains; decide) | try decide
  all_goals
    simp only [Lookup.Contains, fixed3, Table.toRaw, conditionalControlTable,
      jumpCleanupTable, Table.fromStatic, StaticTable.toTable, ProvableType.fromElements,
      Expression.eval, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, wrap, Tests.JumpControl.assignment]
    solve
    | refine ⟨⟨56, by decide⟩, ?_⟩
      norm_num [conditionalControlRow, controlFlag]
    | refine ⟨⟨4, by decide⟩, ?_⟩
      norm_num [jumpCleanupRow]

/-- The existing actually exported JAL -4 still writes the saved link four. -/
theorem exported_jal_link :
    (Word.mk (Tests.ControlHistory.assignment false 38).val
      (Tests.ControlHistory.assignment false 39).val).toBitVec = 4 := by
  have member : JumpBranchSlt.NativeSetup.setup.table.Contains #[]
      (JumpBranchSlt.decoderQuery (Tests.ControlHistory.assignment false)) := by
    have logical := Tests.ControlValues.decoded (Tests.ControlHistory.nativeRow false)
      (by simp [Tests.ControlHistory.trace])
    simpa only [JumpBranchSlt.Proofs.row_decoder_query, Tests.ControlHistory.nativeRow] using logical
  have link := JumpBranchSlt.native_jump_link Tests.ControlValues.decoder_image
    (Tests.ControlHistory.native_constraints false) member (by decide)
  exact link.trans (by decide)

theorem public_jalr_link : (Word.mk (jalr 38).val (jalr 39).val).toBitVec = 8 := by
  have link := JumpBranchSlt.native_jump_link program_image jalr_native
    (by refine ⟨⟨1,by decide⟩,?_⟩; decide +kernel) (by decide)
  exact link.trans (by decide)

theorem public_x0_link : (Word.mk (zero 38).val (zero 39).val).toBitVec = 0 := by
  have link := JumpBranchSlt.native_jump_link program_image zero_native
    (by refine ⟨⟨2,by decide⟩,?_⟩; decide +kernel) (by decide)
  exact link.trans (by decide)

theorem wrap_link : (Word.mk (wrap 38).val (wrap 39).val).toBitVec = 0 := by
  have selectors := JumpBranchSlt.Proofs.jump_selectors (by decide) wrap_native (by decide)
  have link := JumpBranchSlt.Proofs.jump_link (by decide) wrap_native selectors.1 selectors.2
    (initial := ⟨65532,65535⟩) ⟨by decide,by decide⟩
    (by constructor <;> decide) (Or.inl (by decide))
  exact link.1.trans (by decide)

def altered (i : Nat) : ZMod mersenne31Modulus :=
  if i = 38 then 9 else jalr i

/-- Changing the actual native link while preserving all decoder columns fails. -/
theorem altered_link_rejected :
    ¬FlatOperation.ConstraintsHoldFlat (environment altered) JumpBranchSlt.importedConstraints := by
  intro holds
  have link := JumpBranchSlt.native_jump_link program_image holds
    (by refine ⟨⟨1,by decide⟩,?_⟩; decide +kernel) (by decide)
  have wrong : (9 : BitVec 32) = 8 := by convert link using 1 <;> decide
  exact (by decide : (9 : BitVec 32) ≠ 8) wrong

end Tests.JumpLink
