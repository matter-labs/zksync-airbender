module
public import Slop.UnifiedReduced.RV.Dispatch
public import Slop.UnifiedReduced.RV.Laws
public import Slop.Trace.RVRealizes
public import Slop.Trace.RVRom
public import Slop.Trace.ROMView
public import Human.Trace.UnifiedReduced.RVTheorems
public import Slop.Trace.RVBootSeed
public import Slop.KeccakSplit.Field
public import Slop.Final.Circuits.InitsTeardowns.Theorems

@[expose] public section

/-! The unified execution claim on the RV route: the trace is seeded by the inline inits/teardowns sets' zero boot
    image (`rv_boot_seed`), which is the RV image of the starting state, x0-preserving, and each of its rows takes one
    `RV.step` (`row_step`); the generic composition (`rv_realizes`) then gives `RVRealizes`. -/

namespace Airbender.UnifiedReduced.Proofs.RV
open Arithmetic Trace Trace.Proofs
set_option warningAsError true
set_option maxRecDepth 16384

/-- Every row of an accepted RV-decoded unified trace takes one `RV.step`. -/
theorem row_steps {p : Nat} [Fact p.Prime] (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {trace : UnifiedTrace p} {initial : RV.State} {cells : List Cell} {program : List RVProgramEntry}
    {inits : List (InitsTeardowns.Witness p InitsTeardowns.unifiedLayout)}
    (inputs : RVExecutionInputs trace initial cells program inits) (accepted : Accepted trace)
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

/-- The boot seed is the zero boot image of the tracked cells: the register seeds, then the inline sets' `Init` tokens,
    which the inits/teardowns claim makes the zero boot image of their windows. -/
theorem rv_boot_seed {trace : UnifiedTrace babyBearModulus} {initial : RV.State} {cells : List Cell}
    {program : List RVProgramEntry}
    {inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout)}
    (inputs : RVExecutionInputs trace initial cells program inits) :
    trace.initialMemory = Trace.ROMView.nativeBootImage cells :=
  boot_seed_image InitsTeardowns.unified_claim.1 inputs.topBits inputs.seeds inputs.domain

/-- `UnifiedReduced.BootRamZeroClaim`, proved: every tracked RAM cell of the starting state reads 0. -/
theorem boot_ram_zero {trace : UnifiedTrace babyBearModulus} {initial : RV.State} {cells : List Cell}
    {program : List RVProgramEntry}
    {inits : List (InitsTeardowns.Witness babyBearModulus InitsTeardowns.unifiedLayout)}
    (inputs : RVExecutionInputs trace initial cells program inits) :
    ∀ address, Cell.ram address ∈ cells → (Cell.ram address).readRV initial = some 0 := by
  intro address member
  have image := inputs.image
  rw [rv_boot_seed inputs] at image
  exact rv_image_zero image _ member

/-- `UnifiedReduced.RVExecutionSoundnessClaim`, proved. The byte inverse fixes the field to BabyBear, where the
    inits/teardowns claim gives the zero seed. -/
theorem rv_trace_execution [Fact p.Prime] (hp : 4194304 ≤ p) (inverse : (-3840 : ZMod p) * 524288 = 1)
    (byteInverse : 256 * (-7864320 : ZMod p) = 1)
    {trace : UnifiedTrace p} {initial : RV.State} {cells : List Cell} {program : List RVProgramEntry}
    {inits : List (InitsTeardowns.Witness p InitsTeardowns.unifiedLayout)}
    (inputs : RVExecutionInputs trace initial cells program inits) (accepted : Accepted trace)
    (decoded : RVDecoded trace program) :
    RVRealizes trace initial cells := by
  obtain rfl := Keccak.Split.Native.Proofs.scale256_field byteInverse
  have clockSize : 2 * timestampBase + 4 < babyBearModulus := by dsimp [timestampBase]; omega
  have image := inputs.image
  have boundary := Trace.ROMView.native_clocks (by omega) (rv_boot_seed inputs) inputs.initialPC
  obtain ⟨addresses, programImage⟩ := inputs.programImage
  have zero := RVZero.rv_zero_writes_of_preserving clockSize inverse accepted boundary image
    (rv_zero_preserving (by omega) accepted programImage decoded)
  have start : initial.pc = trace.initial.word.toBitVec := by
    rw [inputs.initialPC, inputs.pc]
    simp [PCState.boundary, PCState.encode, PCState.State.word, Word.toBitVec, Word.value]
  exact rv_realizes clockSize inverse accepted boundary image inputs.distinct inputs.aligned zero start
    (row_steps hp inverse byteInverse inputs accepted decoded boundary image)

end Airbender.UnifiedReduced.Proofs.RV
