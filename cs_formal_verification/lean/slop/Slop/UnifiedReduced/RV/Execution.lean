import Slop.UnifiedReduced.RV.Dispatch
import Slop.UnifiedReduced.RV.Laws
import Slop.Trace.RVRealizes
import Slop.Trace.RVRom
import Slop.Trace.ROMView
import Human.Trace.UnifiedReduced.RVTheorems

/-! The unified execution claim on the RV route: the trace is seeded by the RV image (all of RAM starts at zero, as
    the native seed), x0-preserving, and each of its rows takes one `RV.step` (`row_step`); the generic composition
    (`rv_realizes`) then gives `RVRealizes`. -/

namespace Airbender.UnifiedReduced.Proofs.RV
open Arithmetic Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

private theorem read_zero : ∀ (a : RV.Word) (n : Nat), RV.read (fun _ => 0) a n = 0
  | _, 0 => rfl
  | a, n + 1 => by rw [RV.read, read_zero (a + 1) n]; simp

/-- With registers and RAM at zero, the RV image of the tracked cells is the native zero seed. -/
theorem rv_zero_image {p : Nat} {initial : RV.State} {cells : List Cell} {tokens : List (MemoryToken p)}
    (profile : RVInitialProfile initial cells) (image : initialImageRV initial cells = some tokens) :
    tokens = Trace.ROMView.nativeBootImage cells := by
  have zeroMem : initial.mem = fun _ => 0 := funext profile.ram
  have reads := rvImage_reads cells tokens image
  clear image
  induction reads with
  | nil => rfl
  | @cons cell token cells tokens head tail ih =>
    obtain ⟨value, read, rfl⟩ := head
    have zero : value = 0 := by
      cases cell with
      | register index => exact Option.some.inj (read.symm.trans (profile.registers index))
      | ram address =>
        by_cases r : RV.readable address 4
        · rw [readRV_ram _ r, zeroMem, read_zero] at read
          exact (Option.some.inj read).symm
        · simp [Cell.readRV, r] at read
    subst zero
    rw [ih ⟨profile.pc, profile.registers, profile.ram⟩]
    rfl

/-- Every row of an accepted RV-decoded unified trace takes one `RV.step`. -/
theorem row_steps {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {trace : UnifiedTrace p} {initial : RV.State} {cells : List Cell} {program : List RVProgramEntry}
    (inputs : RVExecutionInputs trace initial cells program) (accepted : Accepted trace)
    (decoded : RVDecoded trace program) (boundary : ClockBoundary trace)
    (image : initialImageRV initial cells = some trace.initialMemory) :
    RVRowSteps trace initial cells := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  have limbSize : limbBase < p := by dsimp [limbBase]; omega
  obtain ⟨addresses, programImage⟩ := inputs.programImage
  have bounds := (rv_value_bounds clockSize inverse accepted boundary image).1
  intro row member before after position history
  obtain ⟨entry, present, _, query⟩ := rv_decoder_member (decoded _ member)
  obtain ⟨guard, entryBits, i, decodes, fields⟩ := rvProgram_entry_fetch programImage entry present
  obtain ⟨beforePC, step⟩ := rv_step_of_position position (rv_query_pc limbSize query) guard
    (entryBits ▸ decodes)
  have rom : before.rom = initial.rom := by
    obtain ⟨_, _, middle, _, _, writes, atState⟩ := position
    rw [atState]
    exact (rvWriteHistory_rom writes : middle.rom = initial.rom)
  obtain ⟨family, w⟩ := row
  cases family
  have core : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      (importedConstraints (Setup.tableWith (ROM.wordsRV initial))) := by
    have sub := Verification.holds_of_sublist (accepted.constraints _ member)
      (List.sublist_append_left (importedConstraints trace.rom) importedConstraintsTimestampLookups)
    rw [inputs.setup] at sub
    exact sub
  have active : w 4 = 1 := by
    simpa [Row.columns, CircuitLayout.columns, importedConstraintsTraceColumns] using accepted.active _ member
  have readBound (k : Fin 3) : (readToken w importedConstraintsMemoryPorts[k]).word.Bounded :=
    bounds _ member _ (by fin_cases k <;> simp [Row.ports, CircuitLayout.ports, importedConstraintsMemoryPorts])
  have facts : RowFacts (ROM.wordsRV initial) cells trace.memoryEpoch w before after entry i := {
    core := core
    active := active
    query := query
    fields := fields
    decodes := decodes
    pc := beforePC
    pcAligned := guard.2
    leftBound := by simpa [readToken, MemoryToken.word, MemoryPort.readCode, WordColumns.code, pairCode,
      importedConstraintsMemoryPorts] using readBound 0
    rightBound := by simpa [readToken, MemoryToken.word, MemoryPort.readCode, WordColumns.code, pairCode,
      importedConstraintsMemoryPorts] using readBound 1
    oldBound := by simpa [readToken, MemoryToken.word, MemoryPort.readCode, WordColumns.code, pairCode,
      importedConstraintsMemoryPorts] using readBound 2
    history := history
    cellsAligned := inputs.aligned
    romImage := by funext k; simp only [ROM.wordsRV, rom] }
  obtain ⟨next, exec, same⟩ := row_step hp byteInverse facts
  exact ⟨next, step.trans exec, same⟩

/-- `UnifiedReduced.RVExecutionSoundnessClaim`, proved. -/
theorem rv_trace_execution [Fact p.Prime] (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {trace : UnifiedTrace p} {initial : RV.State} {cells : List Cell} {program : List RVProgramEntry}
    (inputs : RVExecutionInputs trace initial cells program) (accepted : Accepted trace)
    (decoded : RVDecoded trace program) :
    RVRealizes trace initial cells := by
  have clockSize : 2 * timestampBase + 4 < p := by dsimp [timestampBase]; omega
  obtain ⟨tokens, publicImage⟩ := inputs.image
  have image : initialImageRV initial cells = some trace.initialMemory := by
    rw [inputs.seed, ← rv_zero_image inputs.profile publicImage]
    exact publicImage
  have boundary := Trace.ROMView.native_clocks (by omega) inputs.seed inputs.initialPC
  obtain ⟨addresses, programImage⟩ := inputs.programImage
  have zero := RVZero.rv_zero_writes_of_preserving clockSize inverse accepted boundary image
    (rv_zero_preserving (by omega) accepted programImage decoded)
  have start : initial.pc = trace.initial.word.toBitVec := by
    rw [inputs.initialPC, inputs.profile.pc]
    simp [PCState.boundary, PCState.encode, PCState.State.word, Word.toBitVec, Word.value]
  exact rv_realizes clockSize inverse accepted boundary image inputs.distinct inputs.aligned zero start
    (row_steps hp inverse byteInverse inputs accepted decoded boundary image)

end Airbender.UnifiedReduced.Proofs.RV
