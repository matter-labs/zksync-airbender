module
public import Proven.Trace.Machine.CPUHistory
public import Proven.Trace.Machine.CycleGroups
public import Proven.Trace.Machine.MemoryBounds
public import Proven.Trace.Machine.Program
public import Proven.Trace.RVPooledRow

@[expose] public section
namespace Airbender.Trace.Machine.Proofs
open Arithmetic Trace.Proofs Delegation
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

/-- Projection-free native facts used by unified arithmetic and external-input steps. -/
structure UnifiedCycleFacts (trace : UnifiedTrace babyBearModulus) (initial : RV.State) (cells : List Cell)
    (w : Nat → ZMod babyBearModulus) (before after : RV.State) (entry : UnifiedReduced.RVProgramEntry) : Prop where
  /-- The row satisfies the complete native arithmetic and memory equations. -/
  core : FlatOperation.ConstraintsHoldFlat (Verification.environment w) (UnifiedReduced.importedConstraints trace.rom)
  /-- The native row participates. -/
  active : w 4 = 1
  /-- The exact typed metadata view equals the native query. -/
  query : UnifiedReduced.decoderQuery w = entry.query
  /-- The cut state uses the public entry PC. -/
  pc : before.pc = entry.pc
  /-- The public entry is aligned. -/
  pcAligned : entry.pc.toNat % 4 = 0
  /-- Shared matching bounds every native port read. -/
  reads : ∀ port ∈ (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).ports, (readToken w port).word.Bounded
  /-- The actual shared cut gives the three native port operations. -/
  history : RVHistory cells (rowEvents trace.memoryEpoch (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily)).reverse before after
  /-- Every tracked RAM word is aligned. -/
  aligned : ∀ cell ∈ cells, cell.Aligned
  /-- Native memory writes preserve the public ROM bytes. -/
  rom : before.rom = initial.rom

/-- A unified non-caller cycle supplies the common native arithmetic interface without an ordinary-decoder premise. -/
theorem unified_noncaller_facts {trace : UnifiedTrace babyBearModulus} {workers : WorkerPools babyBearModulus}
    {program : List RVMachineProgramEntry} {initialState before after : RV.State} {cells : List Cell} {addresses : List (BitVec 32)}
    (accepted : UnifiedAcceptance trace workers program)
    (initial : (timeOfPair trace.initial.timestamp).Bounded)
    (alignedClock : (timeOfPair trace.initial.timestamp).value % 4 = 0)
    (image : initialImageRV initialState cells = some trace.initialMemory)
    (aligned : ∀ cell ∈ cells, cell.Aligned)
    (programImage : rvMachineProgramImage .unified initialState addresses = some program)
    (tables : workers.standard.setup = modeledSetup Keccak.Controller.rows)
    {w : Nat → ZMod babyBearModulus} (member : (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily) ∈ trace.rows)
    (notCaller : ¬ UnifiedReduced.Caller.Selected w)
    {entry : RVMachineProgramEntry} (present : entry ∈ program) {ordinary : DecoderData UnifiedFamily}
    (data : entry.data = RVMachineDecoderData.ofOrdinary (family := fun _ => .unified) ordinary)
    (query : (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).decoderQuery =
      (entry.data.row entry.pc).map (fun value : Nat => (value : ZMod babyBearModulus)))
    {events : List MemoryAccess} (permutation : events.Perm ((unifiedMemory trace workers).steps.map transferEvent))
    (ordered : events.Pairwise (fun a b => b.1 ≤ a.1))
    (history : RVHistory cells (events.filter fun event => decide
      ((⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).clock < event.1 ∧
        event.1 ≤ (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).clock + 4)) before after)
    (rom : before.rom = initialState.rom) :
    UnifiedCycleFacts trace initialState cells w (before.setPC entry.pc) (after.setPC entry.pc) ⟨entry.pc, entry.bits, ordinary⟩ := by
  have notCalled : (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily) ∉
      trace.rows.filter (fun source => decide (UnifiedReduced.Caller.Selected source.assignment)) := by
    intro called
    exact notCaller (of_decide_eq_true (List.mem_filter.mp called).2)
  have ports : UnifiedReduced.Caller.machinePorts (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily) =
      (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).ports := by
    unfold UnifiedReduced.Caller.machinePorts
    exact ite_eq_right notCaller
  have grouped := unified_ordinary_cycle_group accepted initial alignedClock permutation member notCalled
  rw [ports] at grouped
  have clock := state_clock_inputs (by decide) (by decide) accepted.constraints accepted.states initial alignedClock _ member
  have words := (unified_memory_bounds accepted initial alignedClock image tables).1
  have reads : ∀ port ∈ (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).ports, (readToken w port).word.Bounded := by
    intro port included
    have step : (readToken w port, writeToken (⟨.machine, w⟩ : Row babyBearModulus UnifiedFamily).columns w port) ∈
        (unifiedMemory trace workers).steps :=
      List.mem_append.mpr (Or.inl (List.mem_flatMap.mpr ⟨⟨.machine, w⟩, member,
        List.mem_map.mpr ⟨port, by simpa [ports] using included, rfl⟩⟩))
    exact (words _ step).1
  have core := Verification.holds_of_sublist (accepted.constraints _ member)
    (List.sublist_append_left (UnifiedReduced.importedConstraints trace.rom) UnifiedReduced.importedConstraintsTimestampLookups)
  have typedQuery : UnifiedReduced.decoderQuery w = (⟨entry.pc, entry.bits, ordinary⟩ : UnifiedReduced.RVProgramEntry).query := by
    rw [data] at query
    exact query.trans (ordinary_query (fun _ => .unified) ⟨entry.pc, entry.bits, ordinary⟩)
  have nativeHistory := cpu_row_history trace.memoryEpoch clock grouped (ordered.sublist List.filter_sublist) history
  exact ⟨core, accepted.active _ member, typedQuery, rfl, (machine_entry_fetch programImage entry present).1.2,
    reads, rv_history_with_pc nativeHistory entry.pc, aligned, rom⟩

end Airbender.Trace.Machine.Proofs
