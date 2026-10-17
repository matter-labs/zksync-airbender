import Airbender.Review.Trace.Families.WordMemory.Projection

namespace Tests.WordMemoryProjection
open Airbender Verification Arithmetic Trace

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

private def nativeRow (store inROM discard : Bool) : Row mersenne31Modulus WordMemoryFamily :=
  ⟨.wordMemory, row store inROM discard⟩


private def destination (discard : Bool) : Cell := .register (if discard then 0 else 3)
private def cells (discard : Bool) : List Cell := [.register 1, destination discard]
private def seeds : List Airbender.WordMemory.ShadowSeed := [(16, 123)]

private def trace (discard : Bool) : Data mersenne31Modulus WordMemoryFamily where
  rows := [nativeRow false true discard]
  rom := rom
  initial := (nativeRow false true discard).start
  terminal := (nativeRow false true discard).finish
  initialMemory := [(Cell.register 1).initialToken 16, (destination discard).initialToken 0,
    (Cell.ram 16).initialToken 123]
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

-- There are no Sail bytes at the native shadow address 16. Actual instruction
-- bytes remain available at zero; shadow value 123 is a separate native input.
private def before (discard : Bool) : Reference.RiscV.Sail.State :=
  { (default : Reference.RiscV.Sail.State) with
    regs := (Std.ExtDHashMap.emptyWithCapacity |>.insert .x1 (16 : BitVec 32)
      |>.insert .x3 (0 : BitVec 32) |>.insert .PC (0 : BitVec 32))
    mem := (Std.ExtHashMap.emptyWithCapacity
      |>.insert 0 (if discard then (0x03 : BitVec 8) else 0x83)
      |>.insert 1 (if discard then 0xa0 else 0xa1)
      |>.insert 2 0 |>.insert 3 0) }

private theorem inputs (discard : Bool) :
    Airbender.WordMemory.ShadowImageBoundary (trace discard) (before discard) (cells discard) seeds := by
  have source : (Cell.register 1).read (before discard) = .ok (16 : BitVec 32) (before discard) := by
    apply Reference.RiscV.Sail.read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have target : (destination discard).read (before discard) = .ok (0 : BitVec 32) (before discard) := by
    cases discard
    · apply Reference.RiscV.Sail.read_register
      simp [before, Std.ExtDHashMap.get?_insert]
    · rfl
  have pc : Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) (before discard) =
      .ok (0 : BitVec 32) (before discard) := by
    apply Reference.RiscV.Sail.read_register
    simp [before]
  constructor
  · cases discard <;> decide
  · intro cell member
    rcases List.mem_cons.mp member with rfl | member
    · exact Airbender.WordMemory.Proofs.architectural_register _
    · have same : cell = destination discard := by simpa [cells] using member
      subst cell
      exact Airbender.WordMemory.Proofs.architectural_register _
  · intro seed member
    have same : seed = (16, 123) := by simpa [seeds] using member
    subst seed
    decide
  · simp only [Airbender.WordMemory.shadowInitialImage, cells, initialImage,
      List.mapM_cons, List.mapM_nil, source, target]
    rfl
  · rw [initialState, pc]
    rfl

private def entry (discard : Bool) : ProgramEntry WordMemoryFamily :=
  ⟨0, (if discard then 0x0000a003 else 0x0000a183),
    .LOAD (0, .Regidx 1, .Regidx (if discard then 0 else 3), false, 4),
    ⟨.wordMemory, 1, 0, (if discard then 0 else 3), ⟨0, 0⟩, 0, 2⟩⟩
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

/-- A full-image constructor fails here, while projected initialization succeeds. -/
theorem missing_shadow_bytes (discard : Bool) :
    ¬ ∃ value, (Cell.ram 16).read (before discard) = .ok value (before discard) := by
  simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
    EStateM.run, get, getThe, MonadStateOf.get, bind, EStateM.bind, EStateM.get,
    before, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

private def event (discard : Bool) (port : Fin 3) : MemoryAccess :=
  let native := nativeRow false true discard
  let actual := Airbender.WordMemory.importedConstraintsMemoryPorts[port.val]
  ((trace discard).memoryEpoch + (actual.event native.columns native.assignment).1,
    actual.address.code native.assignment, actual.readCode native.assignment, actual.writeCode native.assignment)

/-- Both ordinary and discarded native ROM loads retain full matching while
    realizing only source/destination GPRs. No Sail shadow byte or read is supplied. -/
theorem projected_rom_history (discard : Bool) :
    ∃ (history : TimestampSortedMemoryAccessList) (after : Reference.RiscV.Sail.State),
      MemoryHistory (trace discard) history ∧
      List.Mem (event discard 1) history.val ∧
      SailHistory (cells discard) [event discard 2, event discard 0] (before discard) after ∧
      SailStateMatches (cells discard) history after := by
  have aligned : ∀ cell ∈ cells discard, cell.Aligned := by
    intro cell member
    simp [cells] at member
    rcases member with rfl | rfl <;> trivial
  obtain ⟨history, rows, after, checked, permutation, _, actual, final⟩ :=
    Airbender.WordMemory.public_projected_sail_history (inputs discard) (accepted discard)
      (decoded discard) aligned
  have same : rows = [nativeRow false true discard] := List.perm_singleton.mp permutation
  subst rows
  have nativeShadow : event discard 1 ∈ (trace discard).nativeEvents := by
    rw [Trace.Proofs.native_events_projection (by decide) (accepted discard)
      (Airbender.WordMemory.Proofs.shadow_clock_boundary (by decide) (inputs discard))]
    simp only [trace, List.flatMap_cons, List.flatMap_nil, List.append_nil, rowEvents, nativeRowEvents]
    apply List.mem_map.mpr
    exact ⟨Airbender.WordMemory.importedConstraintsMemoryPorts[1],
      by change _ ∈ Airbender.WordMemory.importedConstraintsMemoryPorts.toList
         simp [Airbender.WordMemory.importedConstraintsMemoryPorts], rfl⟩
  have retained : List.Mem (event discard 1) history.val := checked.1.mem_iff.mpr
    (List.mem_append_right _ nativeShadow)
  refine ⟨history, after, checked, retained, ?_, final⟩
  have shape : (([nativeRow false true discard].flatMap fun native =>
        (rowEvents (trace discard).memoryEpoch native).reverse).filter fun edge =>
        Airbender.WordMemory.architecturalAddress edge.2.1) =
        [event discard 2, event discard 0] := by
    have first : Airbender.WordMemory.architecturalAddress (event discard 0).2.1 = true := by
      have address : (event discard 0).2.1 = (Cell.register 1).addressCode := by
        cases discard <;> decide
      rw [address]
      exact Airbender.WordMemory.Proofs.architectural_register _
    have middle : Airbender.WordMemory.architecturalAddress (event discard 1).2.1 = false := by
      have address : (event discard 1).2.1 = (Cell.ram 16).addressCode := by
        cases discard <;> decide
      rw [address, Airbender.WordMemory.Proofs.architectural_ram]
      decide
    have last : Airbender.WordMemory.architecturalAddress (event discard 2).2.1 = true := by
      have address : (event discard 2).2.1 = (destination discard).addressCode := by
        cases discard <;> decide
      rw [address]
      exact Airbender.WordMemory.Proofs.architectural_register _
    change ([event discard 2, event discard 1, event discard 0].filter _) = _
    simp only [List.filter_cons, first, middle, last, Bool.false_eq_true,
      ↓reduceIte, List.filter_nil]
  exact shape ▸ actual

/-- Projected native ROM loads perform the actual masked Sail GPR write, with
    readonly source refreshes stuttering even though the shadow is not readable. -/
theorem projected_rom_sail_write (discard : Bool) :
    ∃ after, Reference.Sail.run
      ((destination discard).write (if discard then 0 else 0xc0001073)) (before discard) =
        .ok () after := by
  obtain ⟨_, after, _, _, history, _⟩ := projected_rom_history discard
  refine ⟨after, ?_⟩
  cases history with
  | cons past target tm ta tr tw =>
    cases past with
    | cons empty source sm sa sr sw =>
      cases empty with
      | nil =>
        have readonly : (event discard 0).2.2.1 = (event discard 0).2.2.2 := rfl
        have first := Trace.Proofs.cell_write_same sr
        rw [readonly] at first
        have same := (EStateM.Result.ok.inj (first.symm.trans sw)).2
        subst_vars
        have address : (event discard 2).2.1 = (destination discard).addressCode := by
          cases discard <;> decide
        have sameCell := Trace.Proofs.cell_address_injective (ta.trans address)
        subst target
        have value : memoryWord (event discard 2).2.2.2 =
            (if discard then 0 else 0xc0001073) := by
          cases discard <;>
            simp [event, memoryWord, MemoryPort.writeCode, WordColumns.code,
              WordColumns.evaluate, Airbender.WordMemory.importedConstraintsMemoryPorts,
              nativeRow, row, Nat.unpair_pair, Word.toBitVec, Word.value]
          all_goals decide
        rw [value] at tw
        exact tw

/-- The native shadow refresh value is independent of the actual loaded ROM word. -/
theorem shadow_value_is_not_rom :
    (event false 1).2.2.2 ≠ (event false 2).2.2.2 := by decide

end Tests.WordMemoryProjection
