import Airbender.Review.Circuits.WordMemory.Theorems
import Airbender.Review.Trace.Families.WordMemory.Decoder
import Airbender.Review.Trace.Families.WordMemory.SparseDecoder
import Airbender.Proofs.WordMemory.ROMPadding
import Airbender.Proofs.WordMemory.Address
import Airbender.Proofs.WordMemory.PC
import Airbender.Proofs.WordMemory.Timestamp

namespace Tests.WordMemory
open Airbender Verification Arithmetic

private def rom : WordROM := ⟨[], by decide⟩

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
  else if i = 11 then 2
  else if i = 12 then if store then 1 else 0
  else if i = 13 then 4
  else if i = 15 then 8
  else if i = 17 ∨ i = 19 then 16
  else if i = 18 ∨ i = 20 then addressHi
  else if i = 22 then if inROM then 0 else 1
  else if i = 24 then if !store && inROM then 1 else 0
  else if i = 25 then if !store && !inROM then 1 else 0
  else if i = 26 then 4211
  else if i = 27 then 49152
  else if i = 28 then if store then 2 else 16
  else if i = 29 then if store then 0 else addressHi
  else if i = 30 then 123
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
      (Airbender.WordMemory.importedConstraints rom) := by
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

theorem ram_load : Airbender.WordMemory.NativeTransfers rom (row false false false) :=
  Airbender.WordMemory.native_transfers rom _ (satisfies false false false rfl)

theorem ram_store : Airbender.WordMemory.NativeTransfers rom (row true false false) :=
  Airbender.WordMemory.native_transfers rom _ (satisfies true false false rfl)

theorem rom_load : Airbender.WordMemory.NativeTransfers rom (row false true false) :=
  Airbender.WordMemory.native_transfers rom _ (satisfies false true false rfl)

theorem discarded_rom_load :
    FlatOperation.ConstraintsHoldFlat (environment (row false true true))
      (Airbender.WordMemory.importedConstraints rom) ∧
    row false true true 37 = 0 ∧ row false true true 38 = 0 :=
  ⟨satisfies false true true rfl, rfl, rfl⟩

theorem rom_store_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat (environment (row true true false))
      (Airbender.WordMemory.importedConstraints rom) := by
  intro h
  have store := (Airbender.WordMemory.native_transfers rom _ h).store (by decide)
  have impossible := store.1
  revert impossible
  decide

theorem changed_rom_read_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat
      (environment (fun i => if i = 26 then 4212 else row false true false i))
      (Airbender.WordMemory.importedConstraints rom) := by
  intro h
  have value := (Airbender.WordMemory.Proofs.rom_values (by decide) h).2.1
  revert value
  decide

theorem unaligned_address_rejected :
    ¬ FlatOperation.ConstraintsHoldFlat
      (environment (fun i => if i = 19 then 17 else row false false false i))
      (Airbender.WordMemory.importedConstraints rom) := by
  intro h
  have aligned := (Airbender.WordMemory.native_transfers rom _ h).addressAlignment
  revert aligned
  decide

theorem native_rom_padding : rom.word 0 = BitVec.ofNat 32 3221229683 ∧
    rom.word 1048575 = BitVec.ofNat 32 3221229683 := ⟨rfl, rfl⟩

private def image : WordROM := ⟨[0, 0, 0, 0, 0xdeadbeef], by decide⟩

private def imageRow (i : Nat) : ZMod mersenne31Modulus :=
  if i = 26 ∨ i = 37 ∨ i = 39 ∨ i = 41 then 48879
  else if i = 27 ∨ i = 38 ∨ i = 40 ∨ i = 42 then 57005
  else row false true false i

private theorem image_satisfies :
    FlatOperation.ConstraintsHoldFlat (environment imageRow)
      (Airbender.WordMemory.importedConstraints image) := by
  simp [Airbender.WordMemory.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, environment, imageRow, row]
  repeat' apply And.intro
  all_goals first | (apply range16_contains; decide) |
    (apply timestamp19_contains; decide) | try decide
  all_goals
    simp only [Lookup.Contains, fixed3, Table.toRaw, romSeparatorTable,
      romWordTable, Table.fromStatic, StaticTable.toTable, ProvableType.fromElements,
      Expression.eval, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil,
      imageRow, row]
    solve
    | refine ⟨⟨0, by decide⟩, ?_⟩
      norm_num [romSeparatorRow]
    | refine ⟨⟨4, by decide⟩, ?_⟩
      norm_num [WordROM.row, WordROM.word, image]; decide

theorem image_load :
    FlatOperation.ConstraintsHoldFlat (environment imageRow)
      (Airbender.WordMemory.importedConstraints image) ∧
    imageRow 37 = 48879 ∧ imageRow 38 = 57005 :=
  ⟨image_satisfies, rfl, rfl⟩

theorem ram_effective_address :
    (Airbender.WordMemory.addressWord (row false false false)).toBitVec =
      (Airbender.WordMemory.sourceWord (row false false false)).toBitVec +
      (Airbender.WordMemory.immediateWord (row false false false)).toBitVec := by
  apply Airbender.WordMemory.native_address _ _ (satisfies false false false rfl)
  all_goals constructor <;> decide

theorem native_clock_order :
    Trace.ClockEffects Airbender.WordMemory.importedConstraintsTraceColumns (row false false false) := by
  apply Airbender.WordMemory.Proofs.clock_effects (by decide) (satisfies false false false rfl)
  constructor
  · constructor <;> decide
  · decide
  · intro port member
    simp [Airbender.WordMemory.importedConstraintsTraceColumns] at member
    rcases member with rfl | rfl | rfl <;> constructor <;> decide

theorem native_pc_increment :
    (⟨(row false false false 13).val, (row false false false 14).val⟩ : Word).Bounded ∧
    (⟨(row false false false 13).val, (row false false false 14).val⟩ : Word).toBitVec =
      (⟨0, 0⟩ : Word).toBitVec + 4 := by
  apply Airbender.WordMemory.Proofs.native_pc_successor (by decide)
    (satisfies false false false rfl)
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · constructor <;> decide
  · decide

private def wrappedRow (i : Nat) : ZMod mersenne31Modulus :=
  if i = 0 ∨ i = 17 then 65532
  else if i = 1 ∨ i = 18 then 65535
  else if i = 9 then 4
  else if i = 13 ∨ i = 19 ∨ i = 28 ∨ i = 43 ∨ i = 45 then 0
  else if i = 21 ∨ i = 44 ∨ i = 46 then 1
  else row false true false i

/-- Full native row simultaneously wraps address and PC from 0xfffffffc to zero. -/
private theorem wrapped_satisfies :
    FlatOperation.ConstraintsHoldFlat (environment wrappedRow)
      (Airbender.WordMemory.importedConstraints rom) := by
  simp [Airbender.WordMemory.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, environment, wrappedRow, row]
  repeat' apply And.intro
  all_goals first | (apply range16_contains; decide) |
    (apply timestamp19_contains; decide) | try decide
  all_goals
    simp only [Lookup.Contains, fixed3, Table.toRaw, romSeparatorTable,
      romWordTable, Table.fromStatic, StaticTable.toTable, ProvableType.fromElements,
      Expression.eval, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil,
      wrappedRow, row]
    refine ⟨⟨0, by decide⟩, ?_⟩
    norm_num [romSeparatorRow, WordROM.row, WordROM.word, rom]

theorem native_address_wrap :
    (Airbender.WordMemory.addressWord wrappedRow).toBitVec = 0 ∧
    (Airbender.WordMemory.addressWord wrappedRow).toBitVec =
      (Airbender.WordMemory.sourceWord wrappedRow).toBitVec +
      (Airbender.WordMemory.immediateWord wrappedRow).toBitVec := by
  refine ⟨by decide, ?_⟩
  apply Airbender.WordMemory.native_address _ _ wrapped_satisfies
  all_goals constructor <;> decide

theorem native_pc_wrap :
    (⟨(wrappedRow 13).val, (wrappedRow 14).val⟩ : Arithmetic.Word).Bounded ∧
    (⟨(wrappedRow 13).val, (wrappedRow 14).val⟩ : Arithmetic.Word).toBitVec =
      (⟨65532, 65535⟩ : Arithmetic.Word).toBitVec + 4 := by
  apply Airbender.WordMemory.Proofs.native_pc_successor (by decide) wrapped_satisfies
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · constructor <;> decide
  · decide


private def decoderRow (w : Nat → ZMod mersenne31Modulus) :
    Trace.Row mersenne31Modulus Trace.WordMemoryFamily := ⟨.wordMemory, w⟩
private def decoderTrace (w : Nat → ZMod mersenne31Modulus) :
    Trace.Data mersenne31Modulus Trace.WordMemoryFamily where
  rows := [decoderRow w]
  rom := rom
  initial := (decoderRow w).start
  terminal := (decoderRow w).finish
  initialMemory := (decoderRow w).reads
  terminalMemory := (decoderRow w).writes

private theorem decoder_accepted {w : Nat → ZMod mersenne31Modulus}
    (native : FlatOperation.ConstraintsHoldFlat (environment w)
      (Airbender.WordMemory.importedConstraints rom)) (active : w 4 = 1) :
    Trace.Accepted (decoderTrace w) := by
  constructor
  · intro row member
    have same : row = decoderRow w := by simpa [decoderTrace] using member
    subst row
    exact native
  · intro row member
    have same : row = decoderRow w := by simpa [decoderTrace] using member
    subst row
    exact active
  · change [(decoderRow w).start, (decoderRow w).finish].Perm
      [(decoderRow w).finish, (decoderRow w).start]
    exact List.Perm.swap _ _ []
  · change ((decoderRow w).reads ++ (decoderRow w).writes).Perm
      ((decoderRow w).writes ++ (decoderRow w).reads)
    exact List.perm_append_comm

private def decoderBefore (store : Bool) : Reference.RiscV.Sail.State :=
  { (default : Reference.RiscV.Sail.State) with mem :=
    (Std.ExtHashMap.emptyWithCapacity
      |>.insert 0 (if store then (0x23 : BitVec 8) else 0x83)
      |>.insert 1 (if store then 0xa0 else 0xa1) |>.insert 2 (if store then 0x20 else 0) |>.insert 3 0) }

private def decoderEntry (store discard : Bool) : Trace.ProgramEntry Trace.WordMemoryFamily :=
  if store then
    ⟨0, 0x0020a023, .STORE (0, .Regidx 2, .Regidx 1, 4),
      ⟨.wordMemory, 1, 2, 0, ⟨0, 0⟩, 1, 2⟩⟩
  else
    ⟨0, (if discard then 0x0000a003 else 0x0000a183),
      .LOAD (0, .Regidx 1, .Regidx (if discard then 0 else 3), false, 4),
      ⟨.wordMemory, 1, 0, (if discard then 0 else 3), ⟨0, 0⟩, 0, 2⟩⟩
private def decoderSetup (store discard : Bool) : Airbender.WordMemory.DecoderSetup :=
  ⟨[decoderEntry store discard], 1⟩

private def publicBefore (store discard : Bool) : Reference.RiscV.Sail.State :=
  if discard && !store then
    { (decoderBefore store) with mem :=
      (Std.ExtHashMap.emptyWithCapacity |>.insert 0 (0x03 : BitVec 8)
        |>.insert 1 0xa0 |>.insert 2 0 |>.insert 3 0) }
  else decoderBefore store

set_option maxRecDepth 32768 in
private theorem decoder_image (store discard : Bool) :
    Airbender.WordMemory.decoderSetupImage (publicBefore store discard) 1 1 =
      some (decoderSetup store discard) := by
  have bytes : (Trace.Cell.ram 0).read (publicBefore store discard) =
      .ok (decoderEntry store discard).bits (publicBefore store discard) := by
    cases store <;> cases discard <;>
      simp [Trace.Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
        EStateM.run, get, getThe, MonadStateOf.get, bind, pure, EStateM.bind,
        EStateM.get, EStateM.pure, publicBefore, decoderBefore, decoderEntry,
        Std.ExtHashMap.getElem_insert]
  have program : Trace.programImageWith Airbender.WordMemory.decoderFields
      (publicBefore store discard) [0] = some [decoderEntry store discard] := by
    simp only [Trace.programImageWith, List.mapM_cons, List.mapM_nil,
      Trace.programEntryWith, bytes, bind, Option.bind]
    cases store <;> cases discard <;> rfl
  change (Trace.programImageWith Airbender.WordMemory.decoderFields
    (publicBefore store discard) [0]).bind
    (fun entries => some (Airbender.WordMemory.DecoderSetup.mk entries 1)) =
      some (decoderSetup store discard)
  rw [program]
  rfl

private theorem decoder_member (store discard : Bool) :
    Airbender.WordMemory.Decoded (decoderTrace (row store false discard))
      (decoderSetup store discard) := by
  intro actual member
  have same : actual = decoderRow (row store false discard) := by simpa [decoderTrace] using member
  subst actual
  change ∃ i : Fin 2, (decoderRow (row store false discard)).decoderQuery =
    (decoderSetup store discard).row i
  refine ⟨⟨0, by decide⟩, ?_⟩
  cases store <;> cases discard <;> decide

theorem public_load_decoding :
    ∀ native ∈ (decoderTrace (row false false false)).rows,
      ∃ entry ∈ (decoderSetup false false).program,
        entry.SourceWith (publicBefore false false) Airbender.WordMemory.decoderFields ∧
        native.decoderQuery = entry.query :=
  Airbender.WordMemory.public_decoder_soundness (decoder_image false false)
    (decoder_accepted (satisfies false false false rfl) rfl) (decoder_member false false)

theorem public_store_decoding :
    ∀ native ∈ (decoderTrace (row true false false)).rows,
      ∃ entry ∈ (decoderSetup true false).program,
        entry.SourceWith (publicBefore true false) Airbender.WordMemory.decoderFields ∧
        native.decoderQuery = entry.query :=
  Airbender.WordMemory.public_decoder_soundness (decoder_image true false)
    (decoder_accepted (satisfies true false false rfl) rfl) (decoder_member true false)

theorem public_x0_load_decoding :
    ∀ native ∈ (decoderTrace (row false false true)).rows,
      ∃ entry ∈ (decoderSetup false true).program,
        entry.SourceWith (publicBefore false true) Airbender.WordMemory.decoderFields ∧
        native.decoderQuery = entry.query :=
  Airbender.WordMemory.public_decoder_soundness (decoder_image false true)
    (decoder_accepted (satisfies false false true rfl) rfl) (decoder_member false true)

theorem decoded_native_inputs :
    (decoderRow (row false false false)).start.word.Bounded ∧
    (decoderRow (row false false false)).decoderImmediate.Bounded ∧
    (decoderRow (row false false false)).start.word.lo % 4 = 0 := by
  have accepted := decoder_accepted (satisfies false false false rfl) rfl
  have present : decoderRow (row false false false) ∈ (decoderTrace (row false false false)).rows := by
    simp [decoderTrace]
  have bounds := Airbender.WordMemory.Proofs.decoded_word_bounds (by decide)
    (decoder_image false false) accepted (decoder_member false false) _ present
  exact ⟨bounds.1, bounds.2,
    Airbender.WordMemory.Proofs.decoded_pc_aligned (by decide)
      (decoder_image false false) accepted (decoder_member false false) _ present⟩

theorem negative_load_projection : Airbender.WordMemory.decoderFields
    (.LOAD (0xfff, .Regidx 1, .Regidx 0, false, 4)) =
      some ⟨.wordMemory, 1, 0, 0, ⟨65535, 65535⟩, 0, 2⟩ := rfl

theorem negative_store_projection : Airbender.WordMemory.decoderFields
    (.STORE (0xfff, .Regidx 2, .Regidx 1, 4)) =
      some ⟨.wordMemory, 1, 2, 0, ⟨65535, 65535⟩, 1, 2⟩ := rfl

theorem unsupported_memory_projection :
    Airbender.WordMemory.decoderFields (.LOAD (0, .Regidx 1, .Regidx 3, true, 4)) = none ∧
    Airbender.WordMemory.decoderFields (.LOAD (0, .Regidx 1, .Regidx 3, false, 1)) = none ∧
    Airbender.WordMemory.decoderFields (.STORE (0, .Regidx 2, .Regidx 1, 2)) = none := ⟨rfl, rfl, rfl⟩

private def missingBefore : Reference.RiscV.Sail.State :=
  { (default : Reference.RiscV.Sail.State) with mem := Std.ExtHashMap.emptyWithCapacity }

theorem missing_word_decoder_bytes :
    Airbender.WordMemory.decoderSetupImage missingBefore 1 1 = none := by
  simp [Airbender.WordMemory.decoderSetupImage, Trace.programImageWith,
    Trace.programEntryWith, Trace.Cell.read, _root_.Sail.ArchSem.readBytes,
    _root_.Sail.ArchSem.readByte, EStateM.run, get, getThe, MonadStateOf.get,
    bind, pure, EStateM.bind, EStateM.get, throw, throwThe,
    MonadExceptOf.throw, EStateM.throw, missingBefore]

theorem insufficient_word_decoder_capacity :
    Airbender.WordMemory.decoderSetupImage (publicBefore false false) 2 0 = none := rfl

theorem word_decoder_padding_retained :
    (decoderSetup false false).row (p := mersenne31Modulus) ⟨1, by decide⟩ =
      Vector.replicate 10 (-1) := rfl

theorem word_decoder_padding_rejected :
    (decoderRow (row false false false)).decoderQuery ≠ Vector.replicate 10 (-1) :=
  Airbender.WordMemory.Proofs.padding_excluded (by decide) (satisfies false false false rfl)

private def badFlagRow (i : Nat) : ZMod mersenne31Modulus :=
  if i = 8 then 2 else if i = 37 ∨ i = 41 then -123 else row false false false i

theorem bad_flag_native_satisfies :
    FlatOperation.ConstraintsHoldFlat (environment badFlagRow)
      (Airbender.WordMemory.importedConstraints rom) := by
  simp [Airbender.WordMemory.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, environment, badFlagRow, row]
  repeat' apply And.intro
  all_goals first | (apply range16_contains; decide) |
    (apply timestamp19_contains; decide) | try decide
  all_goals
    simp only [Lookup.Contains, fixed3, Table.toRaw, romSeparatorTable,
      romWordTable, Table.fromStatic, StaticTable.toTable, ProvableType.fromElements,
      Expression.eval, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil,
      badFlagRow, row]
    solve
    | refine ⟨⟨64, by decide⟩, ?_⟩
      norm_num [romSeparatorRow]
    | refine ⟨⟨4, by decide⟩, ?_⟩
      norm_num [WordROM.row, WordROM.word, rom]

theorem bad_flag_decoder_rejected :
    ¬ Airbender.WordMemory.Decoded (decoderTrace badFlagRow) (decoderSetup false false) := by
  intro decoded
  have accepted := decoder_accepted bad_flag_native_satisfies rfl
  have present : decoderRow badFlagRow ∈ (decoderTrace badFlagRow).rows := by simp [decoderTrace]
  have flag := Airbender.WordMemory.Proofs.decoded_zero_flag_exact (by decide)
    accepted decoded _ present
  change (2 : ZMod mersenne31Modulus) = 0 at flag
  revert flag
  decide

/-- Both ordinary and x0 ROM loads retain a readonly native RAM-shadow access. -/
theorem rom_shadow_value_preserved (discard : Bool) :
    Airbender.WordMemory.importedConstraintsMemoryPorts[1].writeCode (row false true discard) =
      Airbender.WordMemory.importedConstraintsMemoryPorts[1].readCode (row false true discard) :=
  Airbender.WordMemory.native_shadow_refresh (satisfies false true discard rfl)
    (port := Airbender.WordMemory.importedConstraintsMemoryPorts[1])
    (by simp [Airbender.WordMemory.importedConstraintsMemoryPorts])
    (address := 16) (by decide) (by cases discard <;> decide)

/-- A real changing RAM store cannot be projected into the readonly shadow domain. -/
theorem changing_store_not_shadow {address : BitVec 32} (region : address.toNat < 4194304) :
    Airbender.WordMemory.importedConstraintsMemoryPorts[2].address.code (row true false false) ≠
      (Trace.Cell.ram address).addressCode := by
  intro same
  have preserved := Airbender.WordMemory.native_shadow_refresh (satisfies true false false rfl)
    (port := Airbender.WordMemory.importedConstraintsMemoryPorts[2])
    (by simp [Airbender.WordMemory.importedConstraintsMemoryPorts]) region same
  have changing : Airbender.WordMemory.importedConstraintsMemoryPorts[2].writeCode (row true false false) ≠
      Airbender.WordMemory.importedConstraintsMemoryPorts[2].readCode (row true false false) := by decide
  exact changing preserved

/-- A complete native x0 load after the interior hole, with matching immediate
    and zero-padded ROM shadow. No expected read/result is supplied. -/
def sparseAfterHole (i : Nat) : ZMod mersenne31Modulus :=
  if i = 0 then 12 else if i = 13 then 16 else if i = 9 then 16
  else if i = 43 then 896194221 -- native inverse of 12 - 65532
  else if i = 17 ∨ i = 26 ∨ i = 27 then 0 else row false false true i

private def sparseROM : WordROM := WordMemory.NativeSparse.programROM.zeroPadded

theorem sparse_after_hole_native_constraints {table : WordROM} (zero : table.word 4 = 0) :
    FlatOperation.ConstraintsHoldFlat (environment sparseAfterHole)
      (WordMemory.importedConstraints table) := by
  simp [WordMemory.importedConstraints, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, environment, sparseAfterHole, row]
  repeat' apply And.intro
  all_goals first | (apply range16_contains; decide) |
    (apply timestamp19_contains; decide) | try decide
  all_goals
    simp only [Lookup.Contains, fixed3, Table.toRaw, romSeparatorTable,
      romWordTable, Table.fromStatic, StaticTable.toTable, ProvableType.fromElements,
      Expression.eval, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, sparseAfterHole, row]
    solve
    | refine ⟨⟨64, by decide⟩, ?_⟩; norm_num [romSeparatorRow]
    | refine ⟨⟨4, by decide⟩, ?_⟩
      norm_num [WordROM.row, zero]
      decide +kernel

private theorem sparse_after_hole_constraints :
    FlatOperation.ConstraintsHoldFlat (environment sparseAfterHole)
      (WordMemory.importedConstraints sparseROM) :=
  sparse_after_hole_native_constraints (WordMemory.Proofs.zero_padding_tail _ (by decide) (by decide))

/-- Accepted full native constraints and actual exported membership recover the
    original LW-to-x0 source at PC 12, beyond the unsupported word at PC four. -/
theorem native_sparse_after_hole_source :
    ∃ entry ∈ WordMemory.NativeSparse.setup.program,
      entry.SourceWith WordMemory.NativeSparse.before WordMemory.decoderFields ∧
      (Trace.Row.mk .wordMemory sparseAfterHole : Trace.Row mersenne31Modulus Trace.WordMemoryFamily).decoderQuery = entry.query := by
  apply WordMemory.exported_sparse_decoder_soundness
    (row := (Trace.Row.mk .wordMemory sparseAfterHole : Trace.Row mersenne31Modulus Trace.WordMemoryFamily))
    (rom := sparseROM) sparse_after_hole_constraints
  exact ⟨⟨3, by decide⟩, by decide +kernel⟩

end Tests.WordMemory
