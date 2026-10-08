import Airbender.Review.Trace.Theorems

namespace Tests.NonDeterminismDecoder
open Airbender Arithmetic Trace Reference.RiscV.Sail Reference.Sail
set_option warningAsError true
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

-- Independent public bytes: CSRRW x1,0x7C0,x0; CSRRW x0,0x7C0,x1.
private def before : State :=
  { (default : State) with
    mem := (Std.ExtHashMap.emptyWithCapacity).insert 0 (0xF3 : BitVec 8)
      |>.insert 1 0x10 |>.insert 2 0 |>.insert 3 0x7C
      |>.insert 4 0x73 |>.insert 5 0x90 |>.insert 6 0 |>.insert 7 0x7C }

private def readEntry : ProgramEntry :=
  ⟨0, 0x7C0010F3, .CSRReg (0x7C0, .Regidx 0, .Regidx 1, .CSRRW),
    ⟨.addSub, 0, 0, 1, ⟨0, 0⟩, 256⟩⟩
private def writeEntry : ProgramEntry :=
  ⟨4, 0x7C009073, .CSRReg (0x7C0, .Regidx 1, .Regidx 0, .CSRRW),
    ⟨.addSub, 0, 0, 0, ⟨0, 0⟩, 1⟩⟩

private theorem read_decoding : SailRV32.Functions.encdec_backwards readEntry.bits =
    (.pure readEntry.instruction : SailRV32.SailM SailRV32.instruction) := by
  dsimp only [readEntry, writeEntry]
  simp only [SailRV32.Functions.encdec_backwards]
  simp only [SailRV32.Functions.currentlyEnabled, SailRV32.Functions.hartSupports]
  rfl

private theorem write_decoding : SailRV32.Functions.encdec_backwards writeEntry.bits =
    (.pure writeEntry.instruction : SailRV32.SailM SailRV32.instruction) := by
  dsimp only [readEntry, writeEntry]
  simp only [SailRV32.Functions.encdec_backwards]
  simp only [SailRV32.Functions.currentlyEnabled, SailRV32.Functions.hartSupports]
  rfl

theorem original_read_decoder (state : State) :
    run (SailRV32.Functions.encdec_backwards 0x7C0010F3) state =
      .ok readEntry.instruction state := by
  change run (SailRV32.Functions.encdec_backwards readEntry.bits) state = _
  rw [read_decoding]
  rfl

theorem original_write_decoder (state : State) :
    run (SailRV32.Functions.encdec_backwards 0x7C009073) state =
      .ok writeEntry.instruction state := by
  change run (SailRV32.Functions.encdec_backwards writeEntry.bits) state = _
  rw [write_decoding]
  rfl

private theorem bytes (write : Bool) :
    (Cell.ram (if write then 4 else 0)).read before =
      .ok (if write then writeEntry.bits else readEntry.bits) before := by
  cases write <;>
    simp [Cell.read, Sail.ArchSem.readBytes, Sail.ArchSem.readByte, EStateM.run,
      get, getThe, MonadStateOf.get, bind, pure, EStateM.bind, EStateM.get, EStateM.pure,
      before, readEntry, writeEntry, Std.ExtHashMap.getElem_insert]

theorem public_image : programImageWith NonDeterminism.decoderFields before [0, 4] =
    some [readEntry, writeEntry] := by
  have read := bytes false
  have write := bytes true
  simp only [Bool.false_eq_true, if_false, if_true] at read write
  simp only [programImageWith, List.mapM_cons, List.mapM_nil, programEntryWith,
    read, write, read_decoding, write_decoding, bind, Option.bind]
  rfl

private def assignment : Nat → ZMod babyBearModulus
  | 2 | 19 | 27 => 4
  | 4 | 7 | 18 | 42 | 43 | 44 => 1
  | 21 => 8
  | 33 => 0x5678
  | 34 => 0x1234
  | _ => 0

private def row : Row babyBearModulus := ⟨.addSub, assignment⟩
private def regToken (index time value : Nat) : MemoryToken babyBearModulus :=
  ⟨(Cell.register (BitVec.ofNat 5 index)).addressCode, (time, 0), value⟩
private def trace : Data babyBearModulus where
  rows := [row]
  rom := ROM.table [] []
  initial := row.start
  terminal := row.finish
  initialMemory := [regToken 0 0 0, regToken 1 0 0]
  terminalMemory := [regToken 0 5 0, regToken 1 6 (Nat.pair 0x5678 0x1234)]

theorem native_constraints : FlatOperation.ConstraintsHoldFlat
    (Verification.environment assignment) AddSub.clockConstraints := by
  simp [AddSub.clockConstraints, AddSub.importedConstraints,
    AddSub.importedConstraintsTimestampLookups, FlatOperation.ConstraintsHoldFlat,
    Expression.eval, Verification.environment, assignment]
  all_goals repeat' apply And.intro
  all_goals first
    | decide
    | (apply Verification.range16_contains
       norm_num [Expression.eval, Verification.environment, assignment, limbBase,
         ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])
    | (apply Proofs.range_contains
       norm_num [Expression.eval, Verification.environment, assignment, timestampBase,
         ZMod.val_ofNat, ZMod.val_natCast, ZMod.val_one, babyBearModulus])

private theorem accepted : Accepted trace := by
  constructor
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    exact native_constraints
  · intro actual member
    have same := List.mem_singleton.mp member
    subst actual
    rfl
  · exact List.Perm.swap _ _ []
  · decide

private theorem membership : Decoded trace [readEntry, writeEntry] := by
  intro actual member
  have same := List.mem_singleton.mp member
  subst actual
  change ∃ i : Fin 2, _
  exact ⟨0, by decide⟩

/-- Source bytes, original CSR instruction, PC, indices and selector 8 are
    recovered from public decoding and native query membership. -/
theorem fetched_read : row.Fetched before NonDeterminism.decoderFields :=
  NonDeterminism.decoder_soundness accepted public_image membership row (by simp [trace])

theorem read_selector : ∀ i : Fin 9,
    assignment (#[10, 11, 12, 13, 14, 15, 16, 17, 18][i]) = if i.val = 8 then 1 else 0 := by
  have bits := Proofs.query_selectors_of_bound (p := babyBearModulus) (by decide)
    accepted (row := row) (by simp [trace]) (entry := readEntry) (by decide) (by decide)
  intro i
  have checked := bits i
  fin_cases i <;>
    simpa [readEntry, row, Row.decoderColumns, AddSub.importedConstraintsDecoderColumns,
      Nat.testBit, Nat.shiftRight_eq_div_pow] using checked

theorem malformed_csr_rejected :
    NonDeterminism.decoderFields (.CSRReg (0x7C0, .Regidx 1, .Regidx 1, .CSRRW)) = none ∧
    NonDeterminism.decoderFields (.CSRReg (0x7C0, .Regidx 0, .Regidx 0, .CSRRW)) = none ∧
    NonDeterminism.decoderFields (.CSRReg (0x7C1, .Regidx 0, .Regidx 1, .CSRRW)) = none ∧
    NonDeterminism.decoderFields (.CSRReg (0x7C0, .Regidx 0, .Regidx 1, .CSRRS)) = none ∧
    NonDeterminism.decoderFields (.CSRImm (0x7C0, 0, .Regidx 1, .CSRRW)) = none := by
  repeat' first | apply And.intro | rfl

end Tests.NonDeterminismDecoder
