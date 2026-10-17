import Airbender.Review.Trace.Families.WordMemory.History
import Airbender.Review.Trace.Families.WordMemory.Values

namespace Tests.WordMemoryHistory
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

private def trace (store inROM discard : Bool) : Data mersenne31Modulus WordMemoryFamily where
  rows := [nativeRow store inROM discard]
  rom := rom
  initial := (nativeRow store inROM discard).start
  terminal := (nativeRow store inROM discard).finish
  initialMemory := (nativeRow store inROM discard).reads
  terminalMemory := (nativeRow store inROM discard).writes

private theorem accepted (store inROM discard : Bool) (legal : (store && inROM) = false) :
    Accepted (trace store inROM discard) := by
  constructor
  · intro actual member
    have same : actual = nativeRow store inROM discard := by simpa [trace] using member
    subst actual
    exact satisfies store inROM discard legal
  · intro actual member
    have same : actual = nativeRow store inROM discard := by simpa [trace] using member
    subst actual
    rfl
  · change [(nativeRow store inROM discard).start, (nativeRow store inROM discard).finish].Perm
      [(nativeRow store inROM discard).finish, (nativeRow store inROM discard).start]
    exact List.Perm.swap _ _ []
  · change ((nativeRow store inROM discard).reads ++ (nativeRow store inROM discard).writes).Perm
      ((nativeRow store inROM discard).writes ++ (nativeRow store inROM discard).reads)
    exact List.perm_append_comm

private def address (inROM : Bool) : BitVec 32 := if inROM then 16 else 4194320
private def second (store inROM : Bool) : Cell :=
  if store then .register 2 else .ram (address inROM)
private def last (store inROM discard : Bool) : Cell :=
  if store then .ram (address inROM) else .register (if discard then 0 else 3)
private def cells (store inROM discard : Bool) : List Cell :=
  [.register 1, second store inROM, last store inROM discard]

-- The native RAM-shadow cell is explicitly initialized in this logical fixture.
-- Its projection to architectural ROM state remains a separate obligation.
private def before (store inROM discard : Bool) : Reference.RiscV.Sail.State :=
  { (default : Reference.RiscV.Sail.State) with
    regs := (Std.ExtDHashMap.emptyWithCapacity
      |>.insert .x1 (address inROM) |>.insert .x2 (123 : BitVec 32)
      |>.insert .x3 (0 : BitVec 32) |>.insert .PC (0 : BitVec 32))
    mem := (Std.ExtHashMap.emptyWithCapacity
      |>.insert (address inROM).toNat (if store then (0 : BitVec 8) else 123)
      |>.insert ((address inROM).toNat + 1) 0
      |>.insert ((address inROM).toNat + 2) 0
      |>.insert ((address inROM).toNat + 3) 0
      |>.insert 0 (if store then (0x23 : BitVec 8) else if discard then 0x03 else 0x83)
      |>.insert 1 (if store || discard then 0xa0 else 0xa1)
      |>.insert 2 (if store then 0x20 else 0) |>.insert 3 0) }

private theorem inputs (store inROM discard : Bool) :
    ImageBoundary (trace store inROM discard) (before store inROM discard) (cells store inROM discard) := by
  have source : (Cell.register 1).read (before store inROM discard) =
      .ok (address inROM) (before store inROM discard) := by
    apply Reference.RiscV.Sail.read_register
    simp [before, Std.ExtDHashMap.get?_insert]
  have operand : (second store inROM).read (before store inROM discard) =
      .ok (123 : BitVec 32) (before store inROM discard) := by
    cases store
    · cases inROM <;>
        simp [second, Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
          EStateM.run, get, getThe, MonadStateOf.get, bind, pure, EStateM.bind,
          EStateM.get, EStateM.pure, before, address, Std.ExtHashMap.getElem_insert]
    · apply Reference.RiscV.Sail.read_register
      simp [before, Std.ExtDHashMap.get?_insert]
  have target : (last store inROM discard).read (before store inROM discard) =
      .ok (0 : BitVec 32) (before store inROM discard) := by
    cases store
    · cases discard
      · apply Reference.RiscV.Sail.read_register
        simp [before, Std.ExtDHashMap.get?_insert]
      · rfl
    · cases inROM <;>
        simp [last, Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
          EStateM.run, get, getThe, MonadStateOf.get, bind, pure, EStateM.bind,
          EStateM.get, EStateM.pure, before, address, Std.ExtHashMap.getElem_insert]
  have pc : Reference.Sail.run (SailRV32.Functions.get_arch_pc ()) (before store inROM discard) =
      .ok (0 : BitVec 32) (before store inROM discard) := by
    apply Reference.RiscV.Sail.read_register
    simp [before]
  constructor
  · cases store <;> cases inROM <;> cases discard <;> decide
  · simp only [cells, initialImage, List.mapM_cons, List.mapM_nil, source, operand, target]
    cases store <;> cases inROM <;> cases discard <;> rfl
  · rw [initialState, pc]
    rfl

private def entry (store discard : Bool) : ProgramEntry WordMemoryFamily :=
  if store then
    ⟨0, 0x0020a023, .STORE (0, .Regidx 2, .Regidx 1, 4),
      ⟨.wordMemory, 1, 2, 0, ⟨0, 0⟩, 1, 2⟩⟩
  else
    ⟨0, (if discard then 0x0000a003 else 0x0000a183),
      .LOAD (0, .Regidx 1, .Regidx (if discard then 0 else 3), false, 4),
      ⟨.wordMemory, 1, 0, (if discard then 0 else 3), ⟨0, 0⟩, 0, 2⟩⟩
private def setup (store discard : Bool) : Airbender.WordMemory.DecoderSetup :=
  ⟨[entry store discard], 1⟩

private theorem decoded (store inROM discard : Bool) :
    Airbender.WordMemory.Decoded (trace store inROM discard) (setup store discard) := by
  intro actual member
  have same : actual = nativeRow store inROM discard := by simpa [trace] using member
  subst actual
  change ∃ i : Fin 2, (nativeRow store inROM discard).decoderQuery = (setup store discard).row i
  refine ⟨⟨0, by decide⟩, ?_⟩
  cases store <;> cases inROM <;> cases discard <;> decide

set_option maxRecDepth 32768 in
theorem public_decoder_built (store inROM discard : Bool) :
    Airbender.WordMemory.decoderSetupImage (before store inROM discard) 1 1 =
      some (setup store discard) := by
  have bytes : (Cell.ram 0).read (before store inROM discard) =
      .ok (entry store discard).bits (before store inROM discard) := by
    cases store <;> cases inROM <;> cases discard <;>
      simp [Cell.read, _root_.Sail.ArchSem.readBytes, _root_.Sail.ArchSem.readByte,
        EStateM.run, get, getThe, MonadStateOf.get, bind, pure, EStateM.bind,
        EStateM.get, EStateM.pure, before, address, entry, Std.ExtHashMap.getElem_insert]
  have program : programImageWith Airbender.WordMemory.decoderFields
      (before store inROM discard) [0] = some [entry store discard] := by
    simp only [programImageWith, List.mapM_cons, List.mapM_nil,
      programEntryWith, bytes, bind, Option.bind]
    cases store <;> cases discard <;> rfl
  change (programImageWith Airbender.WordMemory.decoderFields
    (before store inROM discard) [0]).bind
    (fun entries => some (Airbender.WordMemory.DecoderSetup.mk entries 1)) = _
  rw [program]
  rfl

theorem ram_load_history : ∃ history, MemoryHistory (trace false false false) history :=
  (Airbender.WordMemory.public_memory_soundness (inputs false false false)
    (accepted false false false rfl)).1

theorem ram_store_history : ∃ history, MemoryHistory (trace true false false) history :=
  (Airbender.WordMemory.public_memory_soundness (inputs true false false)
    (accepted true false false rfl)).1

theorem discarded_rom_shadow_latest : LatestRead (trace false true true)
    (nativeRow false true true) Airbender.WordMemory.importedConstraintsMemoryPorts[1] :=
  (Airbender.WordMemory.public_memory_soundness (inputs false true true)
    (accepted false true true rfl)).2 _ (by simp [trace]) _ (by
      change _ ∈ Airbender.WordMemory.importedConstraintsMemoryPorts
      simp [Airbender.WordMemory.importedConstraintsMemoryPorts])

theorem all_native_bounds (store inROM discard : Bool) (legal : (store && inROM) = false) :
    (∀ actual ∈ (trace store inROM discard).rows, ∀ port ∈ actual.ports,
      (readToken actual.assignment port).word.Bounded) ∧
    (∀ actual ∈ (trace store inROM discard).rows, ∀ port ∈ actual.ports,
      (writeToken actual.columns actual.assignment port).word.Bounded) ∧
    (∀ token ∈ (trace store inROM discard).terminalMemory, token.word.Bounded) :=
  Airbender.WordMemory.public_value_bounds (inputs store inROM discard)
    (accepted store inROM discard legal) (decoded store inROM discard)

theorem derived_clocks (store inROM discard : Bool) (legal : (store && inROM) = false) :
    ∀ actual ∈ (trace store inROM discard).rows, ClockInputs actual.columns actual.assignment :=
  Trace.Proofs.clock_inputs (by decide) (accepted store inROM discard legal)
    (Trace.Proofs.image_clock_boundary (by decide) (inputs store inROM discard))

private def omittedShadow : Data mersenne31Modulus WordMemoryFamily :=
  { trace false true true with initialMemory :=
    [(nativeRow false true true).reads[0]'(by decide), (nativeRow false true true).reads[2]'(by decide)] }

/-- A discarded architectural result does not erase a participating native read. -/
theorem omitted_shadow_rejected : ¬ Accepted omittedShadow := by
  intro accepted
  have count := accepted.memory.count_eq ((nativeRow false true true).reads[1]'(by decide))
  revert count
  decide

end Tests.WordMemoryHistory
