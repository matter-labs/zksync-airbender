import Airbender.Review.Trace.Families.WordMemory.NativeBoot
import Airbender.Proofs.Trace.Families.WordMemory.BootShadow
import Airbender.Proofs.WordMemory.ROMPadding
import Airbender.Review.Trace.Families.WordMemory.ROMImage
import Airbender.Review.Trace.Families.WordMemory.CodeHistory
import Airbender.Review.Trace.Families.WordMemory.Projection
import Airbender.Review.Trace.Families.WordMemory.Inputs
import Airbender.Proofs.Trace.Families.WordMemory.ProjectedPorts

namespace Tests.WordMemoryNativeBoot
open Airbender Verification Arithmetic Trace

private def rom (discard : Bool) : WordROM :=
  ⟨[if discard then 0x0100a003 else 0x0100a183, 0, 0, 0, 0xc0001073], by simp⟩

/-- Full native row with PC zero, time four and prior port timestamps zero. -/
private def row (store inROM discard : Bool) (i : Nat) : ZMod mersenne31Modulus :=
  let addressHi := if inROM then 0 else 64
  let rd := if store || discard then 0 else 3
  let candidateLo := if store then 0 else if inROM then 4211 else 123
  let candidateHi := if !store && inROM then 49152 else 0
  let writeLo := if store then 123 else if discard then 0 else candidateLo
  let writeHi := if discard then 0 else candidateHi
  if i = 2 then 4
  else if i = 4 ∨ i = 5 ∨ i = 49 ∨ i = 52 ∨ i = 55 then 1
  else if i = 6 then if store then 2 else 0
  else if i = 7 then rd
  else if i = 8 then if rd = 0 then 1 else 0
  else if i = 9 then 16
  else if i = 11 then 2
  else if i = 12 then if store then 1 else 0
  else if i = 13 then 4
  else if i = 15 then 8
  else if i = 19 then 16
  else if i = 18 ∨ i = 20 then addressHi
  else if i = 22 then if inROM then 0 else 1
  else if i = 24 then if !store && inROM then 1 else 0
  else if i = 25 then if !store && !inROM then 1 else 0
  else if i = 26 then 4211
  else if i = 27 then 49152
  else if i = 28 then if store then 2 else 16
  else if i = 29 then if store then 0 else addressHi
  else if i = 30 then if !store && inROM then 0 else 123
  else if i = 32 then if store then 0 else 1
  else if i = 33 then if store then 16 else rd
  else if i = 34 then if store then addressHi else 0
  else if i = 37 then writeLo
  else if i = 38 then writeHi
  else if i = 39 then candidateLo
  else if i = 40 then candidateHi
  else if i = 41 then if discard then 0 else candidateLo
  else if i = 42 then if discard then 0 else candidateHi
  else if i = 43 then 1227138194
  else if i = 45 then 2147450879
  else 0

private theorem satisfies (store inROM discard : Bool) (legal : (store && inROM) = false) :
    FlatOperation.ConstraintsHoldFlat (environment (row store inROM discard))
      (Airbender.WordMemory.importedConstraints (rom discard)) := by
  cases store <;> cases inROM <;> cases discard <;> simp_all only [Bool.false_and,
    Bool.true_and, Bool.true_eq_false]
  all_goals
    simp [Airbender.WordMemory.importedConstraints, FlatOperation.ConstraintsHoldFlat,
      Expression.eval, environment, row]
    repeat' apply And.intro
    all_goals first | (apply range16_contains; decide) |
      (apply timestamp19_contains; decide) | try decide
    all_goals
      simp only [Lookup.Contains, fixed3, Table.toRaw, romSeparatorTable,
        romWordTable, Table.fromStatic, StaticTable.toTable, ProvableType.fromElements,
        Expression.eval, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, row]
      solve
      | refine ⟨⟨0, by decide⟩, ?_⟩
        norm_num [romSeparatorRow, WordROM.row, WordROM.word, rom]
      | refine ⟨⟨64, by decide⟩, ?_⟩
        norm_num [romSeparatorRow, WordROM.row, WordROM.word, rom]
      | refine ⟨⟨4, by decide⟩, ?_⟩
        norm_num [romSeparatorRow, WordROM.row, WordROM.word, rom]
        decide

private def nativeRow (store inROM discard : Bool) : Row mersenne31Modulus WordMemoryFamily :=
  ⟨.wordMemory, row store inROM discard⟩


private def destination (discard : Bool) : Cell := .register (if discard then 0 else 3)
private def cells (discard : Bool) : List Cell := [.register 1, destination discard]
private def shadows : List (BitVec 32) := [16]

private def trace (discard : Bool) : Data mersenne31Modulus WordMemoryFamily where
  rows := [nativeRow false true discard]
  rom := rom discard
  initial := (nativeRow false true discard).start
  terminal := (nativeRow false true discard).finish
  initialMemory := [(Cell.register 1).initialToken 0, (destination discard).initialToken 0,
    (Cell.ram 16).initialToken 0]
  terminalMemory := (nativeRow false true discard).writes

private theorem accepted (discard : Bool) : Accepted (trace discard) := by
  constructor
  · intro actual member
    have same : actual = nativeRow false true discard := by simpa [trace] using member
    subst actual
    exact satisfies false true discard rfl
  · intro actual member
    have same : actual = nativeRow false true discard := by simpa [trace] using member
    subst actual
    rfl
  · change [(nativeRow false true discard).start, (nativeRow false true discard).finish].Perm
      [(nativeRow false true discard).finish, (nativeRow false true discard).start]
    exact List.Perm.swap _ _ []
  · have initial : (trace discard).initialMemory.Perm (nativeRow false true discard).reads := by
      cases discard <;> decide
    change ((trace discard).initialMemory ++ (nativeRow false true discard).writes).Perm
      ((nativeRow false true discard).writes ++ (nativeRow false true discard).reads)
    exact (initial.append_right _).trans List.perm_append_comm

-- Architectural bytes are real public ROM data. Native shadow value zero stays
-- independently initialized and matched; it is not the loaded ROM word.
private def attributes : SailRV32.PMA :=
  { (default : SailRV32.PMA) with readable := true, writable := true, executable := true }

private def before (discard : Bool) : Reference.RiscV.Sail.State :=
  { (default : Reference.RiscV.Sail.State) with
    regs := ((Std.ExtDHashMap.emptyWithCapacity :
      Std.ExtDHashMap SailRV32.Register SailRV32.RegisterType) |>.insert .x1 (0 : BitVec 32)
      |>.insert .x2 (0 : BitVec 32)
      |>.insert .x3 (0 : BitVec 32)
      |>.insert .x4 (0 : BitVec 32)
      |>.insert .x5 (0 : BitVec 32)
      |>.insert .x6 (0 : BitVec 32)
      |>.insert .x7 (0 : BitVec 32)
      |>.insert .x8 (0 : BitVec 32)
      |>.insert .x9 (0 : BitVec 32)
      |>.insert .x10 (0 : BitVec 32)
      |>.insert .x11 (0 : BitVec 32)
      |>.insert .x12 (0 : BitVec 32)
      |>.insert .x13 (0 : BitVec 32)
      |>.insert .x14 (0 : BitVec 32)
      |>.insert .x15 (0 : BitVec 32)
      |>.insert .x16 (0 : BitVec 32)
      |>.insert .x17 (0 : BitVec 32)
      |>.insert .x18 (0 : BitVec 32)
      |>.insert .x19 (0 : BitVec 32)
      |>.insert .x20 (0 : BitVec 32)
      |>.insert .x21 (0 : BitVec 32)
      |>.insert .x22 (0 : BitVec 32)
      |>.insert .x23 (0 : BitVec 32)
      |>.insert .x24 (0 : BitVec 32)
      |>.insert .x25 (0 : BitVec 32)
      |>.insert .x26 (0 : BitVec 32)
      |>.insert .x27 (0 : BitVec 32)
      |>.insert .x28 (0 : BitVec 32)
      |>.insert .x29 (0 : BitVec 32)
      |>.insert .x30 (0 : BitVec 32)
      |>.insert .x31 (0 : BitVec 32) |>.insert .PC (0 : BitVec 32)
      |>.insert .mstatus 0 |>.insert .cur_privilege .Machine |>.insert .misa 0x40000100
      |>.insert .senvcfg 0 |>.insert .menvcfg 0x10
      |>.insert .pmpcfg_n (Vector.replicate 64 0)
      |>.insert .pmpaddr_n (Vector.replicate 64 0)
      |>.insert .pma_regions [Reference.RiscV.Sail.rv32Region attributes]
      |>.insert .mhartid 7 |>.insert .htif_tohost_base none)
    mem := (Std.ExtHashMap.emptyWithCapacity
      |>.insert 0 (if discard then (0x03 : BitVec 8) else 0x83)
      |>.insert 1 (if discard then 0xa0 else 0xa1)
      |>.insert 2 0 |>.insert 3 1
      |>.insert 4 0 |>.insert 5 0 |>.insert 6 0 |>.insert 7 0
      |>.insert 8 0 |>.insert 9 0 |>.insert 10 0 |>.insert 11 0
      |>.insert 12 0 |>.insert 13 0 |>.insert 14 0 |>.insert 15 0
      |>.insert 16 0x73 |>.insert 17 0x10 |>.insert 18 0 |>.insert 19 0xc0) }

set_option maxRecDepth 16384 in
private theorem profile (discard : Bool) : InitialProfile (before discard) (cells discard) := by
  constructor
  · apply Reference.RiscV.Sail.read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  · have numeric : ∀ index : Nat, index < 32 →
        (Cell.register (BitVec.ofNat 5 index)).read (before discard) = .ok 0 (before discard) := by
      intro index bound
      interval_cases index
      all_goals first
        | rfl
        | (apply Reference.RiscV.Sail.read_register; simp [before, Std.ExtDHashMap.get?_insert])
    intro index
    simpa using numeric index.toNat index.isLt
  · intro address member _bound
    simp [cells, destination] at member

private theorem inputs (discard : Bool) :
    Airbender.WordMemory.NativeBootBoundary (trace discard) (before discard) (cells discard) shadows := by
  constructor
  · cases discard <;> decide
  · intro cell member
    simp only [cells, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact Airbender.WordMemory.Proofs.architectural_register _
  · intro address member
    have same : address = 16 := by simpa [shadows] using member
    subst address
    decide
  · exact profile discard
  · cases discard <;> rfl
  · cases discard <;> rfl

private def entry (discard : Bool) : ProgramEntry WordMemoryFamily :=
  ⟨0, (if discard then 0x0100a003 else 0x0100a183),
    .LOAD (16, .Regidx 1, .Regidx (if discard then 0 else 3), false, 4),
    ⟨.wordMemory, 1, 0, (if discard then 0 else 3), ⟨16, 0⟩, 0, 2⟩⟩
private def setup (discard : Bool) : Airbender.WordMemory.DecoderSetup := ⟨[entry discard], 1⟩

private theorem decoded (discard : Bool) : Airbender.WordMemory.Decoded (trace discard) (setup discard) := by
  intro actual member
  have same : actual = nativeRow false true discard := by simpa [trace] using member
  subst actual
  change ∃ i : Fin 2, (nativeRow false true discard).decoderQuery = (setup discard).row i
  refine ⟨⟨0, by decide⟩, ?_⟩
  cases discard <;> decide

set_option maxRecDepth 32768 in
theorem public_decoder_built (discard : Bool) :
    Airbender.WordMemory.decoderSetupImage (before discard) 1 1 = some (setup discard) := by
  have bytes : (Cell.ram 0).read (before discard) = .ok (entry discard).bits (before discard) := by
    cases discard <;>
      simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
        EStateM.run, get, getThe, MonadStateOf.get, bind, pure, EStateM.bind,
        EStateM.get, EStateM.pure, before, entry, Std.ExtHashMap.getElem_insert]
  have program : programImageWith Airbender.WordMemory.decoderFields
      (before discard) [0] = some [entry discard] := by
    simp only [programImageWith, List.mapM_cons, List.mapM_nil,
      programEntryWith, bytes, bind, Option.bind]
    cases discard <;> rfl
  change (programImageWith Airbender.WordMemory.decoderFields (before discard) [0]).bind
    (fun entries => some (Airbender.WordMemory.DecoderSetup.mk entries 1)) = _
  rw [program]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem configuration (discard : Bool) : Reference.RiscV.Sail.FlatMemoryConfiguration (before discard) := by
  constructor
  · simp [before, Std.ExtDHashMap.get?_insert]
  · simp [before, Std.ExtDHashMap.get?_insert]
  · exact ⟨0x40000100, by simp [before, Std.ExtDHashMap.get?_insert]⟩
  · exact ⟨0, by simp [before, Std.ExtDHashMap.get?_insert]⟩
  · exact ⟨0x10, by simp [before, Std.ExtDHashMap.get?_insert]⟩
  · simp [before, Std.ExtDHashMap.get?_insert]
  · exact ⟨Vector.replicate 64 0, by simp [before, Std.ExtDHashMap.get?_insert]⟩
  · exact ⟨attributes, by simp [before, Std.ExtDHashMap.get?_insert], rfl, rfl, rfl⟩
  · exact ⟨7, by simp [before, Std.ExtDHashMap.get?_insert]⟩
  · simp [before]


private theorem aligned (discard : Bool) : ∀ cell ∈ cells discard, cell.Aligned := by
  intro cell member
  simp [cells] at member
  rcases member with rfl | rfl <;> trivial

/-- Actual bytes construct the same native ROM table, including its retained
    UNIMP tail. Its shadow seed value remains a separate native input. -/
theorem public_rom_built (discard : Bool) :
    wordROMImage (before discard) 5 = some (rom discard) := by
  have bytes (i : Fin 5) :
      (Cell.ram (BitVec.ofNat 32 (4 * i.val))).read (before discard) =
        .ok ((rom discard).word i.val) (before discard) := by
    fin_cases i <;> cases discard <;>
      simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
        EStateM.run, get, getThe, MonadStateOf.get, bind, pure, EStateM.bind,
        EStateM.get, EStateM.pure, before, rom, WordROM.word, Std.ExtHashMap.getElem_insert]
  have b0 := bytes ⟨0, by decide⟩
  have b1 := bytes ⟨1, by decide⟩
  have b2 := bytes ⟨2, by decide⟩
  have b3 := bytes ⟨3, by decide⟩
  have b4 := bytes ⟨4, by decide⟩
  unfold wordROMImage
  rw [dif_pos (by decide)]
  simp only [readROMWords, b0, b1, b2, b3, b4, bind, Option.bind, pure]
  cases discard <;> rfl

/-- Both ordinary and x0 native ROM loads start from actual zero GPRs and zero
    native shadows; original Sail execution reads the independent ROM word. -/
theorem zero_boot_fetched_execution [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (discard : Bool) :
    Airbender.WordMemory.Realizes (setup discard).program (trace discard) (before discard) (cells discard) := by
  apply Airbender.WordMemory.native_boot_execution (inputs discard) (public_decoder_built discard)
    (accepted discard) (decoded discard) (aligned discard) (configuration discard)
    (public_rom_built discard) (by decide)
  · intro address member
    simp [cells, destination] at member
  · intro address member
    have same : address = 16 := by simpa [shadows] using member
    subst address
    decide

/-- Nonzero register data cannot be disguised as the fixed native boot image. -/
theorem invented_seed_rejected (discard : Bool) :
    (trace discard).initialMemory ≠
      [(Cell.register 1).initialToken 1, (destination discard).initialToken 0,
       (Cell.ram 16).initialToken 0] := by
  cases discard <;> decide

/-- Full native matching forces zero at every terminal token for the actual
    readonly ROM-shadow address; no physical ROM/shadow equality is supplied. -/
theorem shadow_terminal_zero (discard : Bool) :
    ∀ sink ∈ (trace discard).terminalMemory,
      sink.address = (Cell.ram 16).addressCode → sink.value = 0 := by
  intro sink member same
  exact Airbender.WordMemory.Proofs.native_boot_shadow_terminal (by decide)
    (inputs discard) (accepted discard) member (by decide) same

/-- The general boot execution reaches native PC four and the actual masked
    destination, including original LW-to-x0 with its real ROM memory read. -/
theorem zero_boot_final_values [_root_.Sail.ArchSem.MemoryPlatform SailRV32.exception]
    (discard : Bool) :
    ∃ after, Relation.ReflTransGen (Airbender.WordMemory.SailStep (setup discard).program) (before discard) after ∧
      Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) after = .ok (4 : BitVec 32) after ∧
      (destination discard).read after = .ok (if discard then 0 else (0xc0001073 : BitVec 32)) after := by
  obtain ⟨after, execution, pc, values⟩ := zero_boot_fetched_execution discard
  let token := writeToken (nativeRow false true discard).columns (row false true discard)
    Airbender.WordMemory.importedConstraintsMemoryPorts[2]
  have present : token ∈ (trace discard).terminalMemory := by cases discard <;> decide
  have code : token.address = (destination discard).addressCode := by cases discard <;> decide
  have kept : Airbender.WordMemory.architecturalAddress token.address = true := by
    rw [code]
    exact Airbender.WordMemory.Proofs.architectural_register _
  obtain ⟨cell, _, address, read⟩ := values token present kept
  have same : cell = destination discard := Trace.Proofs.cell_address_injective (address.trans code)
  subst cell
  refine ⟨after, execution, pc, ?_⟩
  cases discard <;>
    simpa [token, writeToken, MemoryPort.writeCode, WordColumns.code, WordColumns.evaluate,
      MemoryToken.word, nativeRow, Row.columns, row, Airbender.WordMemory.importedConstraintsMemoryPorts,
      Nat.unpair_pair, Word.toBitVec, Word.value, limbBase,
      show (4211 : ZMod mersenne31Modulus).val = 4211 from by decide,
      show (49152 : ZMod mersenne31Modulus).val = 49152 from by decide] using read

/-- Loader zero padding and raw table UNIMP fallback are distinct paths. Both
    preserve the supplied public word; no million-entry list is evaluated here. -/
theorem native_padding_paths (discard : Bool) :
    (rom discard).zeroPadded.words.length = 1048576 ∧
      (rom discard).zeroPadded.word 0 = (rom discard).word 0 ∧
      (rom discard).zeroPadded.word 5 = 0 ∧
      (rom discard).word 5 = 0xc0001073 :=
  ⟨Airbender.WordMemory.Proofs.zero_padding_length _,
    Airbender.WordMemory.Proofs.zero_padding_prefix _ (by cases discard <;> decide),
    Airbender.WordMemory.Proofs.zero_padding_tail _ (by cases discard <;> decide) (by decide), rfl⟩

/-- The native padding model does not silently add absent bytes to Sail. -/
theorem padding_does_not_fill_sail_bytes (discard : Bool) :
    (Cell.ram 20).read (before discard) = .error (.OutOfMemoryRange 20) (before discard) := by
  simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
    EStateM.run, get, getThe, MonadStateOf.get, bind, EStateM.bind,
    EStateM.get, throw, throwThe, MonadExceptOf.throw, EStateM.throw,
    before]

/-- An actual nonzero public GPR fails the original zero-boot profile. -/
theorem nonzero_public_register_rejected (discard : Bool) :
    ¬InitialProfile { before discard with regs := (before discard).regs.insert .x1 (1 : BitVec 32) }
      (cells discard) := by
  intro claimed
  have actual : (Cell.register 1).read
      { before discard with regs := (before discard).regs.insert .x1 (1 : BitVec 32) } =
      .ok (1 : BitVec 32)
        { before discard with regs := (before discard).regs.insert .x1 (1 : BitVec 32) } := by
    apply Reference.RiscV.Sail.read_register
    simp
  have zero := claimed.registers 1
  rw [actual] at zero
  have impossible : (1 : BitVec 32) = 0 := (EStateM.Result.ok.inj zero).1
  exact (by decide : ¬(1 : BitVec 32) = 0) impossible

end Tests.WordMemoryNativeBoot
