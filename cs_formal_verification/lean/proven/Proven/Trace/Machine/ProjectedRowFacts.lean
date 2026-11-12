module
public import Proven.Trace.Machine.CPUHistory
public import Proven.Trace.Machine.Program
public import Proven.Trace.RVPooled.Row

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- A native ordinary cycle supplies the existing pooled row interface with its actual shared-history reads. -/
theorem unrolled_projected_row_facts {config : RVMachineConfig}
    {trace : PooledTrace babyBearModulus} {initial before after : RV.State} {cells : List Cell}
    {addresses : List (BitVec 32)} {program : List RVMachineProgramEntry}
    {row : Row babyBearModulus PooledFamily} {entry : RVMachineProgramEntry} {ordinary : DecoderData PooledFamily}
    (image : rvMachineProgramImage config initial addresses = some program) (present : entry ∈ program)
    (data : entry.data = RVMachineDecoderData.ofOrdinary (family := RVMachineDecoderFamily.pooled) ordinary)
    (family : entry.data.family = .pooled row.family)
    (query : row.decoderQuery = (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus)))
    (constraints : FlatOperation.ConstraintsHoldFlat (Verification.environment row.assignment) (row.constraints trace.rom))
    (active : row.assignment row.columns.execute = 1)
    (clock : (decodeTimestamp row.assignment row.columns.initialTime).Bounded ∧
      (decodeTimestamp row.assignment row.columns.initialTime).lo % 4 = 0)
    (reads : ∀ port ∈ row.ports, (readToken row.assignment port).word.Bounded)
    (finish : row.finish.word.Bounded) (aligned : ∀ cell ∈ cells, cell.Aligned)
    (wordTable : trace.rom.wordMemory = ROM.table cells (romImageRV initial cells))
    (subwordTable : trace.rom.subwordMemory = Verification.subwordTable (ROM.wordsRV initial))
    {events : List MemoryAccess} (permutation : events.Perm (cpuEvents row row.ports))
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1)) (history : RVHistory cells events before after)
    (rom : before.rom = initial.rom) :
    RVPooledRowFacts trace initial cells row (before.setPC entry.pc) (after.setPC entry.pc)
      ⟨entry.pc, entry.bits, ordinary⟩ := by
  have guard := (machine_entry_fetch image entry present).1
  have nativeFamily : ordinary.family = row.family := by
    rw [data] at family
    exact RVMachineDecoderFamily.pooled.inj family
  have nativeQuery : row.decoderQuery = (⟨entry.pc, entry.bits, ordinary⟩ : RVPooledProgramEntry).query := by
    rw [data] at query
    exact query.trans (ordinary_query RVMachineDecoderFamily.pooled ⟨entry.pc, entry.bits, ordinary⟩)
  have nativeHistory := cpu_row_history trace.memoryEpoch clock permutation ordered history
  exact ⟨constraints, active, nativeFamily, nativeQuery, rfl, guard.2, reads, finish,
    rv_history_with_pc nativeHistory entry.pc, aligned, rom, wordTable, subwordTable⟩

end Airbender.Trace.Machine.Proofs
