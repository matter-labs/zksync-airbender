module
public import Proven.Trace.Machine.CPUHistory
public import Proven.Trace.Machine.Program
public import Proven.UnifiedReduced.RV.Dispatch
public import Proven.Trace.RVPooledRow

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- A native ordinary unified cycle supplies the existing row interface through its public ROM and shared history. -/
theorem unified_projected_row_facts {trace : UnifiedTrace babyBearModulus}
    {initial before after : RV.State} {cells : List Cell} {w : Nat → ZMod babyBearModulus}
    {addresses : List (BitVec 32)} {program : List RVMachineProgramEntry} {entry : RVMachineProgramEntry}
    {ordinary : DecoderData UnifiedFamily} {instruction : RV.Instr}
    (image : rvMachineProgramImage .unified initial addresses = some program) (present : entry ∈ program)
    (data : entry.data = RVMachineDecoderData.ofOrdinary (family := fun _ => .unified) ordinary)
    (query : (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).decoderQuery =
      (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus)))
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment w)
      ((⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).constraints trace.rom))
    (active : w 4 = 1)
    (clock : (decodeTimestamp w UnifiedReduced.importedConstraintsTraceColumns.initialTime).Bounded ∧
      (decodeTimestamp w UnifiedReduced.importedConstraintsTraceColumns.initialTime).lo % 4 = 0)
    (reads : ∀ port ∈ (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).ports, (readToken w port).word.Bounded)
    (aligned : ∀ cell ∈ cells, cell.Aligned) (setup : trace.rom = UnifiedReduced.Setup.tableRV initial)
    (fields : UnifiedReduced.rvDecoderFields instruction = some ordinary) (decoded : RV.decode entry.bits = some instruction)
    {events : List MemoryAccess} (permutation : events.Perm (cpuEvents (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily)
      (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).ports))
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1)) (history : RVHistory cells events before after)
    (rom : before.rom = initial.rom) :
    UnifiedReduced.Proofs.RV.RowFacts (ROM.wordsRV initial) cells trace.memoryEpoch w
      (before.setPC entry.pc) (after.setPC entry.pc) ⟨entry.pc, entry.bits, ordinary⟩ instruction := by
  have guard := (machine_entry_fetch image entry present).1
  have nativeQuery : UnifiedReduced.decoderQuery w = (⟨entry.pc, entry.bits, ordinary⟩ : UnifiedReduced.RVProgramEntry).query := by
    rw [data] at query
    exact query.trans (ordinary_query (fun _ => .unified) ⟨entry.pc, entry.bits, ordinary⟩)
  have core := Verification.holds_of_sublist constraints
    (List.sublist_append_left (UnifiedReduced.importedConstraints trace.rom) UnifiedReduced.importedConstraintsTimestampLookups)
  rw [setup] at core
  have readBound (k : Fin 3) : (readToken w UnifiedReduced.importedConstraintsMemoryPorts[k]).word.Bounded :=
    reads _ (by fin_cases k <;> simp [Row.ports, CircuitLayout.ports, UnifiedReduced.importedConstraintsMemoryPorts])
  have nativeHistory := cpu_row_history trace.memoryEpoch clock permutation ordered history
  exact {
    core := core
    active := active
    query := nativeQuery
    fields := fields
    decodes := decoded
    pc := rfl
    pcAligned := guard.2
    leftBound := by simpa [readToken, MemoryToken.word, MemoryPort.readCode, WordColumns.code, pairCode,
      UnifiedReduced.importedConstraintsMemoryPorts] using readBound 0
    rightBound := by simpa [readToken, MemoryToken.word, MemoryPort.readCode, WordColumns.code, pairCode,
      UnifiedReduced.importedConstraintsMemoryPorts] using readBound 1
    oldBound := by simpa [readToken, MemoryToken.word, MemoryPort.readCode, WordColumns.code, pairCode,
      UnifiedReduced.importedConstraintsMemoryPorts] using readBound 2
    history := rv_history_with_pc nativeHistory entry.pc
    cellsAligned := aligned
    romImage := by funext k; simp only [ROM.wordsRV, RV.State.setPC, rom] }

end Airbender.Trace.Machine.Proofs
